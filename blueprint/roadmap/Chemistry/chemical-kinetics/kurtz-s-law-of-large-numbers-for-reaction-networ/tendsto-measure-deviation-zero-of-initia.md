# Deterministic initial counts with z₀(N)/N → x(0) converge in measure

Let $\mu$ be a measure on a measurable space $\Omega$, not necessarily a probability measure, let
$S$ be a finite set of species and $x \colon \mathbb{R} \to \mathbb{R}^S$ a path, and for each
natural number $N$ let $X_N$ be a random count path $\mathbb{R} \to \mathbb{N}^S$ on $\Omega$.
Suppose there are count vectors $z_0(N) \in \mathbb{N}^S$ such that, for every $N$,
$X_N(0) = z_0(N)$ holds $\mu$-almost everywhere, and that the [scaled states](scaled.md) converge:
$z_0(N)/N \to x(0)$ as $N \to \infty$. Then for every $\delta > 0$,

$$\mu\left(D_N(0) \ge \delta\right) \to 0 \quad (N \to \infty),$$

where $D_N(0) = \|X_N(0)/N - x(0)\|_1$ is the [deviation](deviation.md) at time $0$. The event is
not assumed measurable, and $\mu$ is applied to it as an outer measure. For a probability measure
this is the hypothesis of [Kurtz's law of large numbers](tendsto-measure-deviation.md) that the
scaled initial state converges in probability to $x(0)$.
