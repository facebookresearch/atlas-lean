# Free iff

For any store `s`, finite heap `h` and heap postcondition `Q`,
`safePre (.free addr) Q s h` holds if and only if `addr.eval s ∈ h` and
`Q s (Finmap.erase (addr.eval s) h)`. Free leaves the store unchanged.
The allocated-address requirement remains even when `Q` is always true.
