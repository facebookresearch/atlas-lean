# Kolmogorov's condition for pre-Brownian motion

Let $B$ be a pre-Brownian motion (a real process with the finite-dimensional laws of Brownian motion) with
measurable coordinates. Then for all times $s, t \ge 0$ the pair $(B_s, B_t)$ is measurable and

$$\mathbb E |B_s - B_t|^4 \le 3 |s - t|^2,$$

so $B$ satisfies Kolmogorov's condition with exponents $p = 4$, $q = 2$ and constant $3$: the moment
hypothesis of Kolmogorov's lemma, with $d = 1$ and $\varepsilon = 1$.

## Informally uses

- [Fourth moment of a centered Gaussian](integral-pow-four-gaussian-real.md): the increment
  $B_s - B_t$ is centered Gaussian with variance $|s - t|$, so its fourth moment is $3 |s - t|^2$.

## Sources

- J.-F. Le Gall, DEA lecture notes, 1994, Lemme 2.3.
