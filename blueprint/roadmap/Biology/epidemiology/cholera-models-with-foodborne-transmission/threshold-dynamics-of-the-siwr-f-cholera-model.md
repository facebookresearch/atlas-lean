# Threshold dynamics of the SIWR-F cholera model

**Model.** In a constant population, let $s, i, r$ be the susceptible, infected and recovered fractions, $w$ the rescaled concentration of *Vibrio cholerae* in the water reservoir and $f$ the food (biomass) density relative to its carrying capacity. The SIWR-F model is

$$\begin{aligned}
\dot s &= \mu - \beta_W (1 + f)\, w s - \beta_I s i - \mu s, &\qquad \dot w &= \xi (i - w),\\
\dot i &= \beta_W (1 + f)\, w s + \beta_I s i - (\gamma + \mu) i, & \dot r &= \gamma i - \mu r,\\
\dot f &= \tilde r f (1 - f) - a f, &&
\end{aligned}$$

with birth and death rate $\mu$, environmental and direct transmission rates $\beta_W, \beta_I$, recovery rate $\gamma$, pathogen decay rate $\xi$, food growth rate $\tilde r$ and food depletion rate $a$, all positive, and $\tilde r > a$ so that food persists at $f^\ast = 1 - a/\tilde r$. Contaminated food multiplies environmental transmission by $1 + f$; with $f \equiv 0$ the model reduces to the classical SIWR model. The orthant is forward invariant, and $\Omega = \{s + i + r \le 1,\ 0 \le w \le 1,\ 0 \le f \le 1\}$ is positively invariant.

**Statement.** The basic reproduction number is

$$\mathcal R_0 = \frac{\beta_I + \beta_W (1 + f^\ast)}{\gamma + \mu}.$$

If $\mathcal R_0 \le 1$, the disease-free equilibrium $(s, i, w, f) = (1, 0, 0, f^\ast)$ is globally asymptotically stable, and it is unstable if $\mathcal R_0 > 1$. If $\mathcal R_0 > 1$, the disease is uniformly strongly persistent: there is $\varepsilon > 0$ such that every solution with $i(0) > 0$ satisfies $\liminf_{t\to\infty} i(t) \ge \varepsilon$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

With infected compartments $(i, w)$ at the disease-free state, new infections enter only $i$, giving $F = \begin{pmatrix} \beta_I & \beta_W(1+f^\ast) \\ 0 & 0\end{pmatrix}$, and $V$ has inverse $\begin{pmatrix} (\gamma+\mu)^{-1} & 0 \\ (\gamma+\mu)^{-1} & \xi^{-1}\end{pmatrix}$, so $\rho(FV^{-1})$ is the stated $\mathcal R_0$. Food grows logistically independently of the epidemic, so $f(t) \to f^\ast$ and the infection subsystem is asymptotically autonomous. For $\mathcal R_0 \le 1$, $s \le 1$ and the linear comparison system for $(i, w)$, which is cooperative with spectral bound of the sign of $\mathcal R_0 - 1$, drive $(i, w) \to 0$; for $\mathcal R_0 > 1$ the disease-free set is a uniform weak repeller and standard persistence theory upgrades this to uniform persistence.

## Sources

- J.-M. Mandeng, Modeling cholera dynamics under food insecurity and environmental contamination: a multi-patch approach, arXiv (2025). <https://doi.org/10.48550/arXiv.2509.05731> (Section 3: normalized SIWR-F system, Lemmas 3.1 to 3.3, Theorem 3.1 and the next-generation computation of $\mathcal R_0$.)
