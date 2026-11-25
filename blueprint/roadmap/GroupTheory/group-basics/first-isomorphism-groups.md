# First isomorphism theorem for groups

Let $\varphi \colon G \to H$ be a homomorphism of groups. Then the map $G/\ker\varphi \to \varphi(G)$, $g\ker\varphi \mapsto \varphi(g)$, is well defined and is an isomorphism of groups from the quotient group $G/\ker\varphi$ onto the image $\varphi(G)$, a subgroup of $H$.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the map $g\ker\varphi \mapsto \varphi(g)$: `QuotientGroup.rangeKerLift`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/GroupTheory/QuotientGroup/Basic.lean#L112-L115.
