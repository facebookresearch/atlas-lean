# Generic chaining bound for Gaussian processes, canonical form

Under the hypotheses of the generic chaining bound for Gaussian processes,

$$\mathbb{E}\sup_{t \in T} X_t \le 10\,\gamma_2(T, d), \qquad d(s, t) = (\mathbb{E}(X_s - X_t)^2)^{1/2},$$

with $\gamma_2$ written for the canonical distance exactly as in the majorizing measure theorem
(Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2nd ed., 2021, right-hand inequality
of Theorem 2.10.1). It is the upper half of that theorem with $L = 10$, under the extra
hypothesis that the canonical distance is a metric on $T$ (no two distinct indices carry almost
surely equal variables).

## Informally uses

- [Generic chaining bound for Gaussian processes](integral-i-sup-le-gamma-two-of-is-gaussi.md):
  the same bound stated with the metric.
- [The metric is the canonical distance](edist-eq-canonical-dist.md): the rewriting of the
  distance.
