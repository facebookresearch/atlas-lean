# Assign iff

For any store `s`, finite heap `h` and heap postcondition `Q`,
`safePre (.assign name value) Q s h` holds if and only if `Q` holds on
`h` and the store obtained by setting `name` to `value.eval s`. The
expression is evaluated in the original store; assignment leaves the heap unchanged.
