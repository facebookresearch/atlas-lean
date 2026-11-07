# Nonnegative integrals of future path functionals over present events

Let $\mu$ be a
probability measure on $\Omega$, let $(\mathcal{F}_t)_{t \ge 0}$ be a filtration indexed by
$\mathbb{R}_{\ge 0}$, and let $(B_t)_{t \ge 0}$ be a real-valued process that is adapted (each
$B_t$ is $\mathcal{F}_t$-measurable) and has independent increments (for $u \le t$, the
increment $B_t - B_u$ is independent of $\mathcal{F}_u$ under $\mu$). Fix $s \ge 0$ and let
$\nu_s$ be the law under $\mu$ of the centered shifted path
$\omega \mapsto (t \mapsto B_{s+t}(\omega) - B_s(\omega))$ on $\mathbb{R}^{\mathbb{R}_{\ge 0}}$
with the product σ-algebra. Then for every measurable
$Y : \mathbb{R}^{\mathbb{R}_{\ge 0}} \to [0, \infty]$ and every $A \in \mathcal{F}_s$,

$$\int_A Y\big((B_{s+t}(\omega))_{t \ge 0}\big) \, d\mu(\omega)
= \int_A \int Y\big(t \mapsto B_s(\omega) + g(t)\big) \, d\nu_s(g) \, d\mu(\omega),$$

where all integrals are Lebesgue integrals of $[0, \infty]$-valued functions.
