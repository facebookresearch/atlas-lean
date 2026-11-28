# Invasion of a lytic virus into a host population with contact-mediated dormancy

**Model.** A stochastic individual-based model with carrying-capacity parameter $K$ tracks active hosts (1a), dormant hosts (1d), infected hosts (1i) and free virions (2):

- active hosts divide at rate $\lambda_1$ and die at rate $\mu_1 + C(n_{1a} + n_{1d} + n_{1i})/K$, $0 < \mu_1 < \lambda_1$ (logistic competition);
- virions decay at rate $\mu_2$;
- each active-host–virion pair meets at rate $D/K$: with probability $q$ the host senses the virion and becomes **dormant** (the virion survives), otherwise it becomes infected and the virion is absorbed;
- infected hosts recover to active at rate $r$ or lyse at rate $v$, releasing $m$ virions;
- dormant hosts resuscitate at rate $\sigma$ and die at rate $\kappa\mu_1$, $\kappa \ge 0$.

Without virus the host settles at the rescaled density $\bar n_{1a} = (\lambda_1 - \mu_1)/C$.

**Coexistence condition.** The large-$K$ limiting ODE has a positive coexistence equilibrium iff

$$\big(mv - (r+v)\big)(1-q)D\,\bar n_{1a} > \mu_2(r+v),$$

in which case it is unique with active coordinate $n^*_{1a} = \dfrac{\mu_2(r+v)}{(1-q)D(mv - (r+v))} < \bar n_{1a}$. This holds iff the multitype branching process approximating the initial phase is supercritical, with Malthusian growth rate $\tilde\lambda > 0$.

**Extinction probability.** Starting from one virion, the branching approximation goes extinct with probability $s_2$, the smallest nonnegative root of

$$(1-q)D\bar n_{1a}\frac{v}{r+v}x^m - \big((1-q)D\bar n_{1a} + \mu_2\big)x + \mu_2 + (1-q)D\bar n_{1a}\frac{r}{r+v} = 0,$$

and $s_2 < 1$ exactly under the coexistence condition.

**Theorem.** Suppose $\tilde\lambda \ne 0$, $N^K_{1a}(0) \to \bar n_{1a}$, and a single virion is introduced. Let $T_{S_\beta}$ be the hitting time of a $\beta$-neighborhood of the coexistence region and $T^2_0$ the extinction time of the virus-related types. For all small $\beta > 0$:

1. $\displaystyle\lim_{K\to\infty}\mathbb{P}\big(T_{S_\beta} < T^2_0\big) = 1 - s_2$;
2. on successful invasion, $T_{S_\beta}/\log K \to 1/\tilde\lambda$ in probability;
3. on failure, $T^2_0/\log K \to 0$ and the host returns to the virus-free state, $(N^K_{1a}, N^K_{1d})(T^2_0) \to (\bar n_{1a}, 0)$, in probability.

Dormancy enters only through the factor $1 - q$: hosts that hide from a virion deprive it of infections, so a large enough dormancy initiation probability makes $mv - (r+v)$ insufficient and blocks the epidemic, even though dormant cells never die from the virus.

## Expansion

While the virus is rare, the active host density stays near $\bar n_{1a}$ and the virus-related types (1d, 1i, 2) form an approximately linear multitype branching process: a virion is absorbed into an infection at rate $(1-q)D\bar n_{1a}$, an infection yields $m$ virions with probability $v/(r+v)$; first-step analysis gives the polynomial for $s_2$ and the mean offspring matrix gives $\tilde\lambda$. A successful branching process reaches size $\beta K$ in time $\log K/\tilde\lambda$, after which the ODE takes over (Champagnat-type three-phase invasion argument); a failed one dies in $O(1)$ time. Dormant cells play no role in supercriticality because they neither infect nor produce virions; they only reduce the fraction of encounters that convert into infections.

## Sources

- Jochen Blath and András Tóbiás, "Microbial virus epidemics in the presence of contact-mediated host dormancy", ESAIM: Probability and Statistics 27 (2023), 174–220, <https://doi.org/10.1051/ps/2022022>; numbering as in arXiv:2107.11242v3: Section 2 (model, coexistence-condition proposition, approximating branching processes and the equation for $s_2$) and Theorems 2.8–2.10.
