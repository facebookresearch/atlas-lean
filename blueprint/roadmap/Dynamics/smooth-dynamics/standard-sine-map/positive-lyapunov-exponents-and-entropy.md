# Positive Lyapunov exponents and entropy on a full parameter tail

Use the [Standard map, vector growth, and metric entropy](standard-map-dynamics-and-entropy.md) on the unit torus, with derivative cocycle $A_n$ and normalized area $m$.

Write $P(k)$ for existence of a measurable positive-area set $E$ such that **every** $z\in E$ has a positive spectrum as above and in addition $\log\|A_n(z)\|/n\to\ell$ for that same $\ell$. There exists $k_0>0$ so that for every $k\ge k_0$, the metric entropy $h_m(F_k)$ is positive, $P(k)$ holds, and $h_m(F_k)>0\iff P(k)$. The equivalence is asserted on this parameter tail; it is not a separate equivalence for all parameters.

## Depends on

- [Standard map, vector growth, and metric entropy](standard-map-dynamics-and-entropy.md)

## Proof depends on

- [Pesin’s entropy formula for area-preserving torus maps](pesin-formula-for-area-preserving-torus-maps.md)

## Expansion

Derive the cocycle matrix and identify the norm limit and exponents on a common measurable set. Factor the growth proof from the entropy inference and the implication in each direction of the tail-restricted equivalence. Retain the same parameter threshold and exponent witness when combining them.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StandardMapLyapunov.lean#L19-L105) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/146.md).
- OpenAI, [Positive Metric Entropy for the Standard Map at Large Parameters](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf) (September 23, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
