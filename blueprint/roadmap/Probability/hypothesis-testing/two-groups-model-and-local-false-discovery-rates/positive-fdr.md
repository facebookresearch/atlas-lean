# Storey's positive false discovery rate

Let $m \in \mathbb{N}$ and $q : \{0,1\}^2 \to \mathbb{R}$ the law of one test's (null, rejected) indicator pair, the $m$ pairs being i.i.d. Storey's positive false discovery rate $\mathrm{pFDR} = \mathbb{E}[V/R \mid R > 0]$ is

$$\mathrm{pFDR}(q, m) = \frac{\sum_x \prod_i q(x_i)\, \mathrm{FDP}(x)}{\sum_{x :\ R(x) \ne \emptyset} \prod_i q(x_i)},$$

where the sums run over the outcome vectors $x \in (\{0,1\}^2)^m$, $R(x)$ is the [rejection set](rejected-set.md) and $\mathrm{FDP}(x) = |R(x) \cap H_0(x)| / \max(|R(x)|, 1)$ is the [false discovery proportion](../valid-p-values-and-false-discovery-proportion/false-discovery-proportion.md) with $H_0(x)$ the [true-null set](null-set.md). The value is $0$ when the denominator is $0$.
