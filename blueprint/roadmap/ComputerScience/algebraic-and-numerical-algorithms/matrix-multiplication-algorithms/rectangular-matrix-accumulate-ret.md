# Rectangular matrix accumulation computes $C + AB$

Let $\alpha$ be a commutative additive
monoid with a multiplication, and let $A$, $B$, $C$ be $p \times q$, $q \times r$ and $p \times r$
matrices over $\alpha$, stored as vectors of rows. The matrix returned by rectangular matrix
accumulation on $A$, $B$, $C$ equals $C + AB$, where $AB$ is the matrix product,
$(AB)_{ij} = \sum_{k < q} A_{ik} B_{kj}$.
