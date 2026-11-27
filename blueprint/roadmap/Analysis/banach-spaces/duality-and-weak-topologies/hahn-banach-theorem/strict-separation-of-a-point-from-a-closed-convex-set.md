# Strict separation of a point from a closed convex set

Let $E$ be a real locally convex topological vector space, for instance $\mathbb{R}^n$ or a real normed space, let $t \subseteq E$ be a closed convex set and
$x \in E$ a point not in $t$. Then there are a continuous linear functional $f$ on $E$ and a real number $u$ with $f(x) < u$ and $u < f(b)$ for every $b \in t$.

## Sources

- W. Rudin, *Functional Analysis*, 2nd ed., McGraw-Hill, 1991: Theorem 3.4(b), with the compact set taken to be $\{x\}$.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842: `geometric_hahn_banach_point_closed`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/LocallyConvex/Separation.lean#L223-L228.
