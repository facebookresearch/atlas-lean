# Consistent cut

A cut $C$ of an execution is *consistent* when it is left-closed under
Lamport's happened-before relation $<$: if $b \in C$ and $a < b$, then $a \in C$.
