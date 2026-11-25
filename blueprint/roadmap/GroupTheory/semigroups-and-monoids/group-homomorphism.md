# Multiplication-preserving maps and group homomorphisms

Let $M$ and $N$ be sets, each with a binary operation written as multiplication. A *multiplication-preserving map* from $M$ to $N$ is a map $\varphi \colon M \to N$ with $\varphi(xy) = \varphi(x)\varphi(y)$ for all $x, y \in M$; no identity elements or inverses are assumed. When $M = G$ and $N = H$ are groups, these maps are exactly the group homomorphisms from $G$ to $H$, the maps $\varphi$ with $\varphi(xy) = \varphi(x)\varphi(y)$ for all $x, y \in G$. Such a map preserves identities and inverses: $\varphi(1) = \varphi(1 \cdot 1) = \varphi(1)\varphi(1)$ gives $\varphi(1) = 1$ after cancelling in $H$, and then $\varphi(x^{-1})\varphi(x) = \varphi(1) = 1$ gives $\varphi(x^{-1}) = \varphi(x)^{-1}$. Mathlib's usual bundled group homomorphisms are its monoid homomorphisms, which also record $\varphi(1) = 1$; for groups that condition holds automatically, by the cancellation above.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for maps preserving multiplication between types with a multiplication: `MulHom`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Group/Hom/Defs.lean#L283-L301.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the bundled monoid homomorphisms, which also preserve the identity: `MonoidHom`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Group/Hom/Defs.lean#L366-L367.
