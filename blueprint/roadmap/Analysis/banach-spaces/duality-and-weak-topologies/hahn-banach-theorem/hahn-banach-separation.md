# Hahn–Banach separation of an open convex set from a disjoint convex set

Let $X$ be a real topological vector space, for instance a real normed space with the topology of its norm, and let $A, B \subseteq X$ be disjoint convex sets with $A$ open. Then there are a continuous linear functional $F$ on $X$ and a real number $u$ such that $F(a) < u$ for every $a \in A$ and $u \le F(b)$ for every $b \in B$.

## Sources

- John B. Conway, A Course in Functional Analysis, 2nd ed., Graduate Texts in Mathematics 96, Springer, 1990.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for separation in a real topological vector space, with no nonemptiness or local convexity assumption on the two sets: `geometric_hahn_banach_open`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/LocallyConvex/Separation.lean#L86-L103.
