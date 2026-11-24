# Appending one time to a finite chain law

Appending a time `b` to the times `τ` of a
finite chain law adds one transition `K (b - τ_last)` from the last state: the joint law of the
first `n + 1` states and the appended state is the chain law at `τ` composed with that kernel
step. The times need not be ordered.

## Sources

- the recursive definition of `finiteChainKernel` (Ethier & Kurtz (1986), ch. 4, §1, (1.10)), by induction on the number of times.
