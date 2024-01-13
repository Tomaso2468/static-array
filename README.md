# Static Array
A rust crate providing a heap-allocated non-resizable type-checked array.

The following types are provided:
- `HeapArray` - A one dimensional heap-allocated array.
- `HeapArray2D` - A two dimensional heap-allocated array.
- `HeapArray3D` - A three dimensional heap-allocated array.

## Examples
### Creating a large array on the heap using a function.

```rust
use static_array::HeapArray;

// Creates an array 16 MB (on 64 bit systems) in size which is larger than the standard linux stack size.
let array: HeapArray<usize, 2000000> = HeapArray::from_fn(|i| i);

assert_eq!(1247562, array[1247562]);
```

### Creating a large array from the default value of a type.

```rust
use static_array::HeapArray;

let array: HeapArray<usize, 2000000> = HeapArray::default();

assert_eq!(0, array[1247562]);
```

