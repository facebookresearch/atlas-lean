# One round of pointer jumping for suffix sums

Given a state in which each node $v$ has
a pointer $p(v)$, either a node or undefined, and a sum $s(v)$ in an additive monoid $M$, one
round produces a new state as follows. If $p(v)$ is undefined, the pointer of $v$ stays
undefined and its sum stays $s(v)$. If $p(v) = u$, the new pointer of $v$ is $p(u)$ and its new
sum is $s(v) + s(u)$, with $s(u)$ added on the right so that list order is kept.
