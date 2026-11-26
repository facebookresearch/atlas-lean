# Inv

The inductive invariant, for each process `i` against the other:
`choosing` and ticket-holding follow the program counter; a process past the
`choosing` check is not overtaken by a later `read` of the other; and a process
in its critical section comes first, unless the other holds no ticket or is
returning it.
