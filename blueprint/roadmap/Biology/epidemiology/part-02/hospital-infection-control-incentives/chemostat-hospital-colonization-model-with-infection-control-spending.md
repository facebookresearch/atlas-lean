# Chemostat hospital colonization model with infection-control spending

**Model.** Let $X(t) \in [0, 1]$ be the fraction of a hospital's patients colonized by a pathogen. Patients are discharged at rate $\sigma$ (mean stay $1/\sigma$), a fraction $\kappa \in [0, 1)$ of admissions is already colonized, colonization clears at rate $\lambda$, and transmission occurs at rate $\beta(c)$, where $c \ge 0$ is the total investment in infection control:

$$\frac{dX}{dt} = \sigma(\kappa - X) + \beta(c)\, X (1 - X) - \lambda X, \qquad \beta(c) = \frac{a}{1 + b \sqrt{c}}\quad (a, b > 0).$$

**Equilibria.** With $\mathcal{R}_0(c) = \beta(c)/(\sigma + \lambda)$:

- if $\kappa > 0$, the right-hand side is a downward quadratic in $X$ that is positive at $X = 0$, so there is exactly one equilibrium in $(0, 1)$,

    $$\bar X = \frac{(\beta - \sigma - \lambda) + \sqrt{(\beta - \sigma - \lambda)^2 + 4\beta\sigma\kappa}}{2\beta},$$

    and it is globally attracting on $[0, 1]$;
    - if $\kappa = 0$, the equilibria are $X = 0$ and $\bar X = 1 - 1/\mathcal{R}_0$; for $\mathcal{R}_0 > 1$ the positive one is stable and $X = 0$ unstable, for $\mathcal{R}_0 < 1$ only $X = 0$ is feasible, and the system has a transcritical bifurcation at $\mathcal{R}_0 = 1$.

In both cases $\bar X$ is non-increasing in $c$, so infection-control spending lowers equilibrium colonization with diminishing returns.

**Hospital optimum.** If stays are short enough that $X$ is near equilibrium, a hospital spending $h$ (with $c = h$) and paying $D$ per colonized patient minimizes $h + D \bar X(h)$; an interior optimum satisfies

$$1 + D \frac{d\bar X}{dh} = 0 .$$

Under a fixed subsidy $s$ (so $c = h + s$, while the hospital's own cost is still $h + D\bar X$), the optimal total investment $c^\ast$ is unchanged and the hospital's own spending falls one for one, $h^\ast = c^\ast - s$, while $c^\ast - s \ge 0$: the subsidy crowds out private spending. A subsidy paid per uncolonized patient is equivalent to raising $D$, and a matching subsidy raises the return on each dollar the hospital spends.

## Expansion

For $\kappa > 0$, the function $F(X) = -\beta X^2 + (\beta - \sigma - \lambda) X + \sigma\kappa$ has $F(0) = \sigma\kappa > 0$ and $F(1) = -\lambda - \sigma(1 - \kappa) < 0$, so it has one root in $(0, 1)$ and the other negative; $F > 0$ below and $F < 0$ above the root gives global stability on $[0, 1]$. For $\kappa = 0$ the model is logistic with intrinsic rate $\beta - \sigma - \lambda$. Monotonicity in $c$ follows because $\partial F / \partial \beta = X(1 - X) > 0$ and $\beta$ decreases in $c$, so the root moves down. The crowding-out result holds because the hospital's objective depends on $h$ only through $c = h + s$ apart from the linear term $h = c - s$, so the minimizing $c$ does not depend on $s$. Coupling two hospitals through patient transfers makes each hospital's equilibrium depend on the other's spending, which gives a two-player game; hospitals have an incentive to free-ride on each other's investment. Under a limited budget a dollar-for-dollar matching grant reduces infections in a single hospital more than a fixed subsidy or a per-uninfected-patient subsidy, and with two hospitals a subsidy offered to only one should go to the hospital with the lower transmission rate.

## Sources

- S. E. Drohan, S. A. Levin, B. T. Grenfell, R. Laxminarayan, "Incentivizing hospital infection control", Proceedings of the National Academy of Sciences of the USA 116 (2019) 6221–6225, Model section (Equation [1], "Equilibrium analysis and optimization", "Subsidies") and Fig. 3, <https://doi.org/10.1073/pnas.1812231116> (PMC6442548).
