# Persistence threshold and optimal harvesting effort under tempered stable jump noise

**Model.** A population $x(t) > 0$ with intrinsic growth rate $a > 0$, crowding coefficient $b > 0$ and harvesting effort $h \ge 0$ follows

$$dx(t) = x(t)\big[a - h - b\,x(t)\big]\,dt + \tau\, x(t)\, dB(t) + \sigma\, x(t-)\, dL(t),$$

where $B$ is a standard Brownian motion and $L$ is an independent spectrally positive Lévy process, $dL(t) = \int_0^\infty z\, N(dt,dz) - \int_0^1 z\, \nu(dz)\, dt$, with one-sided tempered stable Lévy measure

$$\nu(dz) = \frac{e^{-\lambda z}}{z^{1+\beta}}\, dz \quad (z > 0), \qquad \beta \in (0,2),\ \lambda > 0,\ \sigma > 0.$$

Let $\Theta = \int_0^\infty \big[\ln(1 + \sigma z) - \sigma z\, \mathbf{1}_{\{0 < z \le 1\}}\big]\, \frac{e^{-\lambda z}}{z^{1+\beta}}\, dz$ and

$$\Phi = a - h - \frac{\tau^2}{2} + \Theta, \qquad A = a - \frac{\tau^2}{2} + \Theta.$$

**Theorem.**

1. *(Well-posedness.)* For every $x(0) > 0$ there is a unique global solution that stays positive for all $t \ge 0$ almost surely.
2. *(Threshold.)* If $\Phi < 0$ then $x(t) \to 0$ a.s.; if $\Phi = 0$ then $\frac1t\int_0^t x(s)\,ds \to 0$ a.s.; if $\Phi > 0$ then $\frac1t\int_0^t x(s)\,ds \to \Phi/b$ a.s.
3. *(Stationary distribution.)* Every moment is eventually bounded, $\limsup_{t\to\infty}\mathbb{E}[x(t)^p] \le K_p$, and the transition probabilities converge weakly to a unique stationary law $\pi$ on $[0,\infty)$ for every initial value.
4. *(Optimal harvesting.)* The long-run average yield $Y(h) = \lim_{t\to\infty} \frac1t\int_0^t h\, x(s)\, ds = h(A - h)/b$ for $h \in (0, A)$ is maximized by the effort and yield

$$h^* = \frac{A}{2}, \qquad Y^* = \frac{A^2}{4b},$$

whereas for $h \ge A$ one has $\Phi \le 0$ and no optimal harvesting policy exists.

## Depends on

- [Explicit solution of the logistic equation](../logistic-growth-equation/logistic.md)

## Expansion

Itô's formula for jump processes applied to $\ln x$ gives

$$\ln x(t) = \ln x(0) + \Phi\, t - b\int_0^t x(s)\, ds + \tau B(t) + \sigma\text{-jump martingale},$$

where the drift collects $a - h$, the Itô correction $-\tau^2/2$ and the compensator of $\ln(1 + \sigma z)$ against the small-jump compensation, which is exactly $\Theta$. The martingale terms are $o(t)$ by the strong law for martingales (tempering makes all exponential moments of large jumps finite), so a standard comparison lemma for $\ln\Psi(t) \lessgtr \lambda t - \lambda_0\int_0^t \Psi$ yields the threshold trichotomy. Uniform moment bounds give tightness, and a coupling of solutions from different initial values gives uniqueness of the stationary law. The yield is quadratic in $h$, so its maximizer is the midpoint of $(0, A)$. Larger tempering $\lambda$ or smaller stability index $\beta$ change $\Theta$ and therefore shift $h^*$ and $Y^*$.

## Sources

- Wenmin Deng, Fu Zhang, "Optimal Harvesting of a Stochastic Logistic Model Driven by One-Sided Tempered Stable Process", arXiv (2026). Lemmas 2.1, 2.2, 3.1; Theorems 2.1, 3.1, 4.1. <https://doi.org/10.48550/arXiv.2605.15624>
