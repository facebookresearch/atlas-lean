# One-shot achievability (Shannon/Feinstein/DT bounds)

This node collects one-shot achievability bounds for a channel $P_{Y \mid X}$ with input law $P_X$ and information density
$i(x;y) = \log \frac{dP_{X,Y}}{d(P_X \times P_Y)}(x, y)$, with values in $[-\infty, +\infty]$ as in the source's Definition 18.1.

## Expansion

A sound expansion has separate pages for:

1. **Shannon's bound.** For every $M \ge 1$ and $\gamma > 0$ there is a code with $M$ messages and average error at most
   $\Pr[i(X;Y) \le \log M + \gamma] + e^{-\gamma}$ (with natural logarithms), as stated in the source.
2. **Feinstein's lemma.** For every $\gamma > 0$ and every $\varepsilon \in (0, 1)$ there is a code with
   $M \ge \gamma(\varepsilon - \Pr[i(X;Y) < \log \gamma])$ messages and maximal error at most $\varepsilon$, as stated in the source.
3. **Dependence-testing bound.** Average error at most
   $\mathbb{E}\bigl[\exp\bigl(-\bigl(i(X;Y) - \log\frac{M-1}{2}\bigr)^+\bigr)\bigr]$, as stated in the source.

Each bound is a separate page with its exact message and error conventions.

## Related topics

- [Weak converse for discrete memoryless channels](shannon-s-channel-coding-theorem/channel-coding-weak-converse.md)
- [Cross-entropy is entropy plus divergence](../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/cross-entropy-eq-shannon-entropy-add-kl.md)

## Sources

- Information Theory: From Coding to Learning — Yury Polyanskiy (MIT) and Yihong Wu (Yale); Cambridge University Press 2025; authors' draft, Definition 18.1, Thm 18.5 (Shannon), Thm 18.6 (DT bound), Thm 18.7 (Feinstein). <https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf>
