# Write iff

For any store `s`, finite heap `h` and heap postcondition `Q`,
`safePre (.write addr value) Q s h` holds if and only if `addr.eval s ∈ h`
and `Q s (Finmap.insert (addr.eval s) (value.eval s) h)`. Both expressions
use the original store. The membership condition excludes missing cells,
which `insert` alone would otherwise add.
