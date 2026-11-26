# Amortized, worst-case and high-probability probe complexity

Let $(P, \mathcal{A})$ be an open-addressed table without reordering filled with $m = n - \lfloor \delta n \rfloor$ keys, and let $J_i$ be the probe complexity of $x_i$. The *amortized expected probe complexity* is $\mathbb{E}\big[\frac{1}{m}\sum_{i=1}^m J_i\big]$; the *worst-case expected probe complexity* is $\max_{1 \le i \le m} \mathbb{E}[J_i]$; a *high-probability worst-case bound* $T$ means $\Pr[\max_i J_i \le T] \ge 1 - n^{-c}$ for a fixed constant $c > 0$. These quantities are functions of $n$ and $\delta$, and bounds are stated asymptotically as $n \to \infty$, uniformly over the stated range of $\delta$.

## Depends on

- [Open-addressing insertion without reordering](oa-without-reordering-model.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
