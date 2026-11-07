# Entries of rectangular matrix accumulation

Let $\alpha$ be a commutative additive monoid
with a multiplication, and let $A$, $B$, $C$ be $p \times q$, $q \times r$ and $p \times r$
matrices over $\alpha$, stored as vectors of rows. For all $i < p$ and $j < r$, the $(i, j)$ entry
of the matrix returned by rectangular matrix accumulation on $A$, $B$, $C$ is
$C_{ij} + \sum_{k < q} A_{ik} B_{kj}$.
