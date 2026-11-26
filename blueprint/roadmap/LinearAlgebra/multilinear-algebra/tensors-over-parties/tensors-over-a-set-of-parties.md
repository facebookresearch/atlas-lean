# Tensors over a finite set of parties and the restriction preorder

Let $I$ be a finite set of *parties* and $K$ a field. A *tensor over $I$* is an array $t\in\bigotimes_{a\in I}K^{X_a}$ with a finite index set $X_a$ for each party. A tensor $s$ is a *restriction* of $t$, written $s\le t$, if $s=(\bigotimes_aA_a)t$ for linear maps $A_a$; $s$ and $t$ are *equivalent* if each is a restriction of the other. The tensor (Kronecker) product $s\otimes t$ multiplies index sets partywise, and equivalence classes form a commutative monoid. A *unit tensor* $\langle r\rangle$ has entry $1$ on the diagonal of $[r]^I$, and a *wire* between two parties is the unit tensor held by those two parties only.

## Depends on

- [Tensor restrictions and degenerations](../../../TheoryOfComputation/algebraic-complexity/tensor-degenerations-and-matrix-multiplication/tensor-restrictions-and-degenerations.md)

## Sources

- Anthropic, "VP ≠ VNP over every field", manuscript, 2026.
- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
