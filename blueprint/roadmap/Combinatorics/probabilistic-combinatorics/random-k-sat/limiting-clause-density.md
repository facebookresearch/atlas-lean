# A limiting density threshold for proper random k-SAT

For fixed integer $k\ge3$, a proper clause on $n$ Boolean variables chooses a uniform $k$-element subset and an independent fair sign at each variable. An $m$-clause formula consists of $m$ independent draws with replacement. Let $p(n,k,m)$ be the number of satisfiable ordered formulas divided by the total number of ordered formulas. A formula is satisfiable if one assignment simultaneously makes at least one literal true in every clause. At $m=0$ this ratio is $1$, including when $n<k$. If $n<k$ and $m>0$ there are no formulas and the ratio is set to $0$.

There exists a finite real $\alpha_k>0$ so that $p(n,k,\lfloor cn\rfloor)\to1$ for every real $0\le c<\alpha_k$, and $p(n,k,\lfloor cn\rfloor)\to0$ for every $c>\alpha_k$, as $n\to\infty$. The floor is a natural floor (truncated below zero). Neither behavior at equality nor a value for $\alpha_k$ is asserted.

The [proper-clause model](proper-clause-probability.md) gives $p(n,k,m)$. At $k=3$ it is exactly the [canonical random 3-SAT probability](../random-3-sat-threshold/sat-prob.md): an optional signed literal at each variable is equivalent to a chosen set with a sign on that set, and the canonical type stores one sign function on all variables with the constraint that it is false off the selected set. This bijection preserves satisfying assignments and ordered formula counts, including the empty-formula and empty-ensemble cases. The $k=3$ conclusion implies [the canonical common-cutoff proposition](../random-3-sat-threshold/has-constant-threshold.md) using the empty formula at negative densities. That proposition does not itself include positivity of the common cutoff; the converse for $k=3$ uses a positive lower cutoff. The source also quantifies over every larger fixed $k$; this is not a second page for the $k=3$ proposition alone.

## Depends on

- [Satisfiability probability of random 3-SAT](../random-3-sat-threshold/sat-prob.md)
- [Proper-clause satisfiability probability](proper-clause-probability.md)
- [Common cutoff in the canonical 3-SAT model](../random-3-sat-threshold/has-constant-threshold.md)

## Proof depends on

Sharpness for the finite-size threshold plus convergence of its location. A sharp transition around a possibly oscillating sequence of densities does not imply a limiting threshold.

## Expansion

Prove the finite-model bridge from the counting ratio to the product law for $n\ge k$. Separate lower and upper positive-density bounds, finite-size sharpness, and convergence of the transition location. The latter step must apply to each fixed $k\ge3$.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FixedClauseThreshold.lean#L51-L53)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/235.md)
- [Accompanying manuscript: A Limiting Satisfiability Threshold for Every Fixed Clause Size](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-Limiting-Satisfiability-Threshold-for-Every-Fixed-Clause-Size-September-25-2026/article.pdf)
- [Background: Friedgut, *Sharp thresholds of graph properties, and the k-sat problem*, Journal of the American Mathematical Society 12 (1999), 1017–1054](https://doi.org/10.1090/S0894-0347-99-00305-7)
- [Background: Ding, Sly and Sun, Proof of the satisfiability conjecture for large k](https://arxiv.org/abs/1411.0650)
