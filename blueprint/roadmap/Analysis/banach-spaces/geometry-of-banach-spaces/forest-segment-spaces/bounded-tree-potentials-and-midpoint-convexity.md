# Midpoint convexity and a renorming obstruction for bounded tree potentials

On the tree of finite words over $\mathbb N$, choose whether to include the empty root among the coefficient coordinates. An admissible real test $f$ vanishes at an excluded root and satisfies $|\sum_{v\preceq s}f(v)|\le1$ for every word $s$. Choose one quadratic budget: sums of squared coefficients are at most one over every finite set of siblings; or over every finite antichain and $f$ has finite support; or over every finite subset and $f$ is square-summable. Define the norm of a finitely supported vector $x$ as the supremum of $|\sum_vx(v)f(v)|$ over the admissible tests and complete in that norm.

For each of the two choices about the root and each of the three budgets, the resulting real Banach space is separable and infinite-dimensional. For every $0<t<1$ its averaged modulus is at least $\sqrt{1+t^2/4}-1$. The modulus is the infimum over unit $x$, supremum over norm-closed finite-codimensional subspaces $F$, and infimum over $y\in F$ with $\|y\|\ge1$, of $(\|x+ty\|+\|x-ty\|)/2-1$. No isomorphic real normed space is AUC, where AUC asks positivity at every $t>0$ of the corresponding one-sided modulus with $\|y\|=1$ and $\|x+ty\|-1$ in place of the average.

## Depends on

- The bounded-prefix test norm, the three different quadratic budgets, and the cofinite moduli above.

## Proof depends on

- Admissible-tail comparison and clipping for each test family, and an isomorphic renorming obstruction.

## Expansion

Prove separation and norm bounds on the finitely supported vectors before completing. Track the root and support choices through the midpoint estimate and show why the one-sided obstruction persists for all equivalent norms.

## Sources

- OpenAI, [BoundedTreePotentials comparator, main_counterexample](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BoundedTreePotentials.lean#L339-L349).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
