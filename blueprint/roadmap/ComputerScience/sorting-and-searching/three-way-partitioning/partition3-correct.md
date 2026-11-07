# Correctness of the stable three-way partition

Let $p$ be an element of a linearly ordered
type $\alpha$, let $xs$ be a list over $\alpha$, and let $B$, $E$ and $A$ be the below, equal and
above lists of the stable three-way partition of $xs$ around $p$. Then the concatenation $B$, $E$,
$A$ is a permutation of $xs$, every element $x$ of $B$ satisfies $x < p$, every element of $E$
equals $p$, and every element $x$ of $A$ satisfies $p < x$.
