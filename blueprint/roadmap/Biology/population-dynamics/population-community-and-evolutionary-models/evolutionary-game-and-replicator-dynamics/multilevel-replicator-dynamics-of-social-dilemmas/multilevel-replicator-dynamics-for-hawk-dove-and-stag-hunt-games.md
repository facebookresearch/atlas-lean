# Multilevel replicator dynamics for Hawk–Dove and Stag Hunt games

**Model.** Groups play a symmetric two-strategy game with payoffs $R$ (C vs C), $S$ (C vs D), $T$ (D vs C), $P$ (D vs D). In a group with cooperator fraction $x$, set

$$\alpha = R - S - T + P, \quad \beta = S - P, \quad \gamma = S + T - 2P, \qquad \pi_C(x) - \pi_D(x) = \beta + \alpha x, \quad G(x) = P + \gamma x + \alpha x^2,$$

where $G$ is the average payoff of the group. In the limit of infinitely many infinitely large groups (nested Moran processes, within-group selection strength $w_I$, between-group strength $w_G$ and timescale $\Lambda$), the density $f(t,x)$ of group compositions solves the *two-level replicator equation*

$$\partial_t f = -\partial_x\big[x(1-x)(\beta + \alpha x)\,f\big] + \lambda f\Big[G(x) - \int_0^1 G(y)f(t,y)\,dy\Big], \qquad \lambda = \frac{w_G\Lambda}{w_I}.$$

For measure-valued solutions $\mu_t$, the Hölder exponent $\theta$ of $\mu_t$ near $x = 1$ (the tail $\mu_t([1-y,1]) \sim y^\theta$) is preserved in time for the Prisoner's Dilemma and Hawk–Dove games.

**Hawk–Dove ($\alpha<0<\beta<|\alpha|$).** Within groups the cooperator fraction is pushed to the interior equilibrium $\beta/|\alpha|$. If the initial measure has Hölder exponents $\zeta$ near $0$ and $\theta$ near $1$ and

$$\lambda\big(\gamma - (\beta + |\alpha|)\big) < |\alpha|\,\theta,$$

then $\mu_t \rightharpoonup \delta_{\beta/|\alpha|}$: group selection is too weak to move groups away from the within-group optimum for defectors. Above this threshold steady densities $f^\lambda_\theta$ exist; as $\lambda\to\infty$ their modal composition tends to $\gamma/|\alpha| - 1 \in (0,1)$ if $\gamma < 2|\alpha|$, which is strictly below the group-optimal composition $x^* = \gamma/(2|\alpha|)$ (a shadow of within-group selection), and tends to $1$ if $\gamma > 2|\alpha|$.

**Stag Hunt and anti-coordination games.** In the Stag Hunt, if the initial density puts mass arbitrarily close to $x=1$, then for every $\lambda>0$, $f(t,\cdot) \rightharpoonup \delta_1$: any between-group competition selects full cooperation. In the anti-coordination games, for every $\lambda\ge0$ and initial Hölder exponents $\zeta,\theta>0$, $\mu_t \rightharpoonup \delta_{\beta/|\alpha|}$.

## Expansion

Along characteristics of the within-group flow $\dot x = x(1-x)(\beta + \alpha x)$, the equation becomes a linear transport equation with a nonlocal growth term, so $\mu_t$ is the push-forward of $\mu_0$ reweighted by $\exp\big(\lambda\int_0^t G(\phi_s(x))\,ds\big)$ and renormalized. Near $x=1$ the within-group flow drains mass away from full cooperation at an exponential rate, while the group-selection weight amplifies the mass that remains there; since the tail exponent $\theta$ is preserved, comparing these two exponential rates decides whether mass near $x=1$ survives, which gives the threshold, as in the Prisoner's Dilemma case. Steady states are found by solving the stationary first-order ODE explicitly.

## Sources

- Daniel B. Cooney, "Analysis of Multilevel Replicator Dynamics for General Two-Strategy Social Dilemmas", arXiv:1910.06020 (2019), Propositions 3.1 and 3.2 (Hölder exponent preservation), Propositions 5.1 and 5.2 (Hawk–Dove), Propositions 6.1 and 6.2 (Stag Hunt and anti-coordination), <https://doi.org/10.48550/arXiv.1910.06020>.
