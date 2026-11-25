# Read iff

For any store `s`, finite heap `h` and heap postcondition `Q`,
`safePre (.read name addr) Q s h` holds if and only if there is a value `v`
with `h.lookup (addr.eval s) = some v` and `Q (Function.update s name v) h`.
The address is evaluated before the store update; the heap is unchanged.
