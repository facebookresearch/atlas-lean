# Existence of smooth partitions of unity

Let $M$ be a smooth manifold, possibly with boundary or corners, modelled on a finite-dimensional real normed space, and suppose that $M$ is Hausdorff and $\sigma$-compact, that is, a countable union of compact subsets. Let $s \subseteq M$ be a closed subset and let $(U_i)_{i \in I}$ be an indexed family of open subsets of $M$ whose union contains $s$. Then there is a smooth partition of unity on $s$ subordinate to $(U_i)$: a family $(\psi_i)_{i \in I}$ of smooth functions $\psi_i \colon M \to \mathbb{R}$ such that each $\psi_i$ is nonnegative, the family of supports $\{x : \psi_i(x) \neq 0\}$ is locally finite, $\sum_i \psi_i(x) \le 1$ for all $x \in M$, $\sum_i \psi_i(x) = 1$ for all $x \in s$, and the closure of the support of each $\psi_i$ is contained in $U_i$. Taking $s = M$ gives a smooth partition of unity subordinate to any indexed open cover of $M$.

## Sources

- John M. Lee, Introduction to Smooth Manifolds, 2nd ed., Graduate Texts in Mathematics 218, Springer, 2013.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for smooth partitions of unity on a set: `SmoothPartitionOfUnity`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Geometry/Manifold/PartitionOfUnity.lean#L117-L133.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for subordination to a family of sets: `SmoothPartitionOfUnity.IsSubordinate`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Geometry/Manifold/PartitionOfUnity.lean#L270-L273.
