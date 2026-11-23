# Negative Boltzmann entropy

Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra and
Lebesgue measure $dx$. For a measure $\rho$ on $E$, let $f : E \to [0, \infty]$ be its Radon–Nikodym
derivative $d\rho/dx$ (the density of the absolutely continuous part of $\rho$ in its Lebesgue
decomposition, and $f = 0$ if $\rho$ has none; a $\sigma$-finite $\rho$ always has one), and let
$\tilde f$ be its finite part: $\tilde f = f$ where $f < \infty$ and $\tilde f = 0$ where $f = \infty$.
Then

$$S(\rho) = \int_E (\tilde f \log \tilde f)^+ \, dx - \int_E (\tilde f \log \tilde f)^- \, dx \in [-\infty, +\infty],$$

with $0 \log 0 = 0$ and the convention $\infty - \infty = -\infty$. So a density that is infinite on a
set of positive measure contributes $0$ there, and the singular part of $\rho$ does not contribute.
In the usual case of an absolutely continuous $\rho$ with a finite density $g$,
$S(\rho) = \int_E g \log g \, dx$, and $-S$ is the Gibbs–Boltzmann entropy. On the admissible set the
negative part is finite: Jordan, Kinderlehrer and Otto show $S(\rho) \ge -C (M(\rho) + 1)^\alpha$ for
every $\alpha \in (n/(n+2), 1)$ (their (14)).

## Sources

- R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), 1–17, the functional $S$ of Section 2 and estimate (14).
