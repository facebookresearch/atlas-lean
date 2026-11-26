# Session Reading

Read a CLL proposition as a binary branching type, when every
subproposition that must itself be read lies in the atom- and
exponential-free fragment. Payload propositions of tensor and par are
carried opaquely. The clauses are: $1$ and $\bot$ read as `end`; $0$ as the empty `branch` and $\top$ as the empty `select`; $A \otimes B$ as receiving the payload $A$, then the reading of $B$; the par of $A$ and $B$ as sending the payload $A^\perp$, the dual of $A$, then the reading of $B$; $A \oplus B$ as a two-way `branch` and $A \mathbin{\&} B$ as a two-way `select`, with labels left and right for the readings of $A$ and $B$, when both are readable. Atoms, their duals and both exponentials have no reading.
