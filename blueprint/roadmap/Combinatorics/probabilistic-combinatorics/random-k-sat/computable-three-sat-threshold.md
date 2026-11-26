# Computability of the limiting random 3-SAT threshold

For the [canonical proper-clause random 3-SAT probability](../random-3-sat-threshold/sat-prob.md), there exist $\alpha>0$, a sequence $q:\mathbb N\to\mathbb Q$, and one deterministic partial-recursive code. At each fixed nonnegative density below $\alpha$ the satisfiability probabilities tend to $1$ and at each fixed density above $\alpha$ they tend to $0$. The function $r\mapsto\operatorname{encode}(q_r)$ is computable, and the code halts on every input $r$ returning that encoding with $|q_r-\alpha|\le2^{-r}$. The output rational need not be a finite-volume approximation and the statement assumes no effective rate of convergence of the satisfiability probabilities.

## Depends on

- [Proper-clause satisfiability probability](proper-clause-probability.md)

- [Satisfiability probability of random 3-SAT](../random-3-sat-threshold/sat-prob.md)

## Proof depends on

- [The limiting density for every fixed clause size](limiting-clause-density.md)

## Expansion

Establish sound and complete effectively enumerable upper and lower certificates for the transition, including the supercritical energy estimate and the finite-to-limiting comparison. State their quantitative separation guarantees first; a merely existent limiting density does not yield them. Then use both enumerations to trap the threshold in arbitrarily short rational intervals and construct one terminating precision-indexed code.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SATComputability.lean#L45-L47)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/235.md)
- [Accompanying manuscript: Computing the Random 3-SAT Threshold](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf)
- [Background: Friedgut, *Sharp thresholds of graph properties, and the k-sat problem*, Journal of the American Mathematical Society 12 (1999), 1017–1054](https://doi.org/10.1090/S0894-0347-99-00305-7)
