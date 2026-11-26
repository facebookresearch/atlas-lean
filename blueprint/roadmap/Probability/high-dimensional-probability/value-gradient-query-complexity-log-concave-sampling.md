# Value-and-gradient query complexity of well-conditioned log-concave sampling

In dimension $d$, take all $C^2$ functions $V:\mathbb R^d\to\mathbb R$ with $V(0)=0$, $\nabla V(0)=0$, and $\|v\|^2\le v^{\mathsf T}\nabla^2V(x)v\le2\|v\|^2$ for all $x,v$. The target law has density $e^{-V}/\int e^{-V}$ with respect to volume. An algorithm has a private probability space, a measurable query map at each step using the seed and the earlier replies, and a measurable output using the seed and the transcript. Replies are the exact pair $(V(x),\nabla V(x))$. The transcript begins padded by zero pairs, fills one slot at each query, and is passed to the output after $q$ queries. The algorithm is uniform over $V$; for every admissible $V$ the run is measurable and its output law is within $1/10$ in total variation (supremum over measurable events) of the target. Define $Q(d)$ as the smallest feasible natural $q$, or $+\infty$ if none exists.

For every $\eta>0$ there is a real $C$ with $Q(d)\le C d^\eta$ for every $d\ge2$. There are $c>0$ and $d_0\ge2$ with $c\log d\le Q(d)$ for every $d\ge d_0$. If a nonnegative $\gamma$ is admissible when $Q(d)\le d^{\gamma+\eta}$ eventually for every $\eta>0$, the infimum of the admissible exponents is $0$.

**Conventions.** Use the finite adaptive first-order transcript model, the Euclidean Hessian and volume-normalized Gibbs law, and exact-measurable rather than bit-bounded queries.

## Depends on

- [Adaptive value-and-gradient sampling of a normalized Gibbs law](first-order-sampling-model.md)

## Proof depends on

An oracle sampler with subpolynomial worst-case query cost uniformly over the Hessian class, and an indistinguishability lower bound for measurable adaptive algorithms with private randomness.

## Expansion

Prove $0<\int e^{-V}<\infty$ using the Hessian bounds, and split the upper and lower query bounds. A fixed polynomial prefactor is absorbed using exponent slack to derive the exponent conclusion. Keep total variation for the entire output law and do not replace the deterministic per-run query budget by its expectation.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LogConcaveQuery.lean#L81-L88)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/139.md)
- [Accompanying manuscript: Subpolynomial query complexity for well-conditioned log-concave sampling](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf)
