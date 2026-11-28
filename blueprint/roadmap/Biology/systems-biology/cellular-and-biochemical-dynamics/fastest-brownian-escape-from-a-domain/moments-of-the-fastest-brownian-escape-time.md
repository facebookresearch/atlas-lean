# Moments of the fastest Brownian escape time

**Setting.** Let $\Omega \subset \mathbb{R}^d$, $d \in \{2, 3\}$, be a bounded open domain whose smooth boundary contains a nonempty, relatively open target $\partial\Omega_{\mathrm T}$; the rest of the boundary is reflecting. Start $N$ independent Brownian particles with diffusivity $D > 0$ at $\mathbf{x}_0 \in \Omega$, let $\tau_n$ be the first time particle $n$ hits $\partial\Omega_{\mathrm T}$, and let $T_N = \min_{n \le N} \tau_n$. For $d = 1$, $T_{1\mathrm{d}}(z_0)$ denotes the same quantity for particles started at distance $z_0$ from an absorbing point.

**Theorem.**
1. *(Upper bound.)* If $\mathbf{x}_{\mathrm T} \in \partial\Omega_{\mathrm T}$ is such that the segment $\{(1-s)\mathbf{x}_0 + s\mathbf{x}_{\mathrm T} : s \in [0,1)\}$ lies in $\Omega$, and $z_0 = \|\mathbf{x}_0 - \mathbf{x}_{\mathrm T}\|$, then for every $m \ge 1$

$$
\limsup_{N \to \infty} \left(\frac{z_0^2}{4D\log N}\right)^{-m} \mathbb{E}\bigl[T_N^m\bigr] \le 1 .
$$

2. *(Exact asymptotics.)* Let $z_0 = \|\mathbf{x}_0 - \mathbf{x}_{\mathrm T}^*\|$ be the distance from $\mathbf{x}_0$ to the closure of the target, attained at $\mathbf{x}_{\mathrm T}^*$, assume the segment from $\mathbf{x}_0$ to $\mathbf{x}_{\mathrm T}^*$ lies in $\Omega$, and assume $\{\mathbf{x} : \|\mathbf{x} - \mathbf{x}_0\| < z_0\} \cap \Omega$ is star-shaped about $\mathbf{x}_0$ (true if $\Omega$ is convex). Then for every $m \ge 1$

$$
\mathbb{E}\bigl[T_N^m\bigr] \sim \mathbb{E}\bigl[T_{1\mathrm{d}}(z_0)^m\bigr] \sim \left(\frac{z_0^2}{4D\log N}\right)^{m}, \qquad N \to \infty .
$$

## Proof sketch

The fastest searcher is the one that runs almost straight to the nearest target point, so short-time large deviations govern everything: $\mathbb{P}(\tau_1 \le t) \approx \exp(-z_0^2/(4Dt))$ as $t \to 0$, and the minimum of $N$ copies concentrates where this probability is about $1/N$, i.e. $t \approx z_0^2/(4D\log N)$. The upper bound comes from comparing with a 1d particle that only has to move a distance $z_0$ along the obstacle-free segment, while the side-escape probability out of a thin cylinder around it decays like $t^{-1/2}e^{-C/t}$ and is negligible. The lower bound projects the motion onto the radial distance from $\mathbf{x}_0$, a Bessel process that must reach radius $z_0$ before the particle can touch the target; the star-shaped condition makes that comparison valid. The leading order does not depend on target size, dimension, or the mean single-particle hitting time.

## Sources

- Sean D. Lawley and Jacob B. Madrid, "A Probabilistic Approach to Extreme Statistics of Brownian Escape Times in Dimensions 1, 2, and 3", *Journal of Nonlinear Science* 30 (2020), 1207–1227, <https://doi.org/10.1007/s00332-019-09605-9>. Preprint version: arXiv:1907.07515 (2019), Theorem 1 (cylinder), Lemmas 2–3, Theorems 4–5 (3d), Theorems 9–10 (2d), <https://doi.org/10.48550/arXiv.1907.07515>.
