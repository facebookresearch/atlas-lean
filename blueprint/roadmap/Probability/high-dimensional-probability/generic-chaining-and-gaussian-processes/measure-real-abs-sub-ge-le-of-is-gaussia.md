# Increments of a centred Gaussian process

Let $(X_t)_{t \in T}$, with $T$ finite, be measurable random variables on a probability space. If the law of
$(X_t)_{t \in T}$ on $\mathbb{R}^T$ is a Gaussian measure and every $X_t$ is integrable and centred, then for all $s, t$ and $u > 0$,

$$\mathbb{P}(|X_s - X_t| \ge u) \le 2\exp\Big(-\frac{u^2}{2\,\mathbb{E}(X_s - X_t)^2}\Big)$$

(Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2nd ed., 2021, remark after (2.4)).
The increment is the image of the law under the continuous linear form $y \mapsto y_s - y_t$, hence
a centred Gaussian variable of variance $\mathbb{E}(X_s - X_t)^2$.

## Informally uses

- [Two-sided Gaussian tail](gaussian-real-abs-tail.md): the tail of the increment.
