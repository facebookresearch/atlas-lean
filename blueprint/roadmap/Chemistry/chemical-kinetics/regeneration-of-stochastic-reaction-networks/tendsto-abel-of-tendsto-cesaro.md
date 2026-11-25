# Abelian theorem: Cesàro limits of $0 \le h \le 1$ are Abel limits

Let $h : \mathbb{R} \to \mathbb{R}$ be measurable with $0 \le h(t) \le 1$ for every $t$, and let
$L$ be a real number. If the Cesàro means of $h$ converge to $L$,

$$\frac{1}{t} \int_0^t h(s)\, ds \to L \quad \text{as } t \to \infty,$$

then its Abel means converge to $L$:

$$a \int_0^\infty e^{-a t} h(t)\, dt \to L \quad \text{as } a \to 0 \text{ with } a > 0 .$$

The integral is over $(0, \infty)$; for $a > 0$ the integrand is bounded by $e^{-a t}$, so it is
integrable. The values of $h$ at negative times play no role. The proof writes the Abel mean as
$\int_0^\infty u e^{-u}\, C(u / a)\, du$, where $C(t) = t^{-1} \int_0^t h(s)\, ds$ is the Cesàro
mean and $\int_0^\infty u e^{-u}\, du = 1$, and lets $a \to 0$ by dominated convergence.
