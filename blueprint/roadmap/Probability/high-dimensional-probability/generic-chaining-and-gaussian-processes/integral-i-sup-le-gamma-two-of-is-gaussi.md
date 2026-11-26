# Generic chaining bound for Gaussian processes

Let $T$ be a finite nonempty metric space and $(X_t)_{t \in T}$ a centred Gaussian process of measurable random
variables on a probability space (its law on $\mathbb{R}^T$ is a Gaussian measure and $\mathbb{E}X_t = 0$) whose canonical distance is the
metric, $d(s, t) = (\mathbb{E}(X_s - X_t)^2)^{1/2}$. Then

$$\mathbb{E}\sup_{t \in T} X_t \le 10\,\gamma_2(T, d)$$

(Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2nd ed., 2021, Theorem 2.7.11 for
Gaussian processes, which is the right-hand inequality of the majorizing measure theorem, Theorem
2.10.1). Integrability of each $X_t$ follows from the Gaussian law. A pseudo-distance, where
distinct indices carry the same variable, is reduced to this case by identifying such indices;
that reduction is not part of the statement above.

## Informally uses

- [Generic chaining bound](integral-i-sup-le-gamma-two.md): Theorem 2.7.11.
- [Increments of a centred Gaussian process](measure-real-abs-sub-ge-le-of-is-gaussia.md): the
  increment condition (2.4) for the canonical distance.
