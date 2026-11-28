# Alloc iff

For any store `s`, finite heap `h` and heap postcondition `Q`,
`safePre (.alloc name value) Q s h` holds if and only if, for every address
`a ∉ h`, `Q (Function.update s name a) (Finmap.insert a (value.eval s) h)`.
The value expression uses the original store. Allocation is demonic over
fresh addresses; finiteness of the heap ensures at least one exists.
