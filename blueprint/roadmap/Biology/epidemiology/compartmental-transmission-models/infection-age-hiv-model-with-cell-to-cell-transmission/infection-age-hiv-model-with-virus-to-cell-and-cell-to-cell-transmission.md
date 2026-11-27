# Infection-age HIV model with virus-to-cell and cell-to-cell transmission

Let $T(t)$ be uninfected CD4+ T cells, $V(t)$ free virus and $i(t,a)$ the density of infected cells of infection age $a \ge 0$. With positive constants $\Lambda$ (source), $\mu$ (death of uninfected cells), $r, K$ (logistic proliferation), $\beta_1$ (virus-to-cell infection), $\beta_2$ (cell-to-cell infection), $\sigma$ (death of infected cells), $N$ (burst size) and $c$ (viral clearance), the model is

$$ \frac{dT}{dt} = \Lambda - \mu T + r T\Big(1 - \frac{T + \int_0^\infty i(t,a)\,da}{K}\Big) - \beta_1 T V - \beta_2 T \int_0^\infty i(t,a)\, da , \qquad \frac{dV}{dt} = N\sigma \int_0^\infty i(t,a)\, da - c V , $$

$$ \partial_t i + \partial_a i = -\sigma i , \qquad i(t,0) = \beta_1 T V + \beta_2 T \int_0^\infty \beta(a)\, i(t,a)\, da , $$

with initial data $T(0) \ge 0$, $V(0) \ge 0$, $i(0,\cdot) \in L^1_+(0,\infty)$. The age-dependent infectivity is a step after an eclipse period $\tau > 0$: $\beta(a) = \beta^*$ for $a \ge \tau$ and $\beta(a) = 0$ for $0 < a < \tau$, normalized by $\int_0^\infty \beta(a) e^{-\sigma a}\, da = 1$ (that is, $\beta^* = \sigma e^{\sigma\tau}$).

**Positive equilibrium.** Write $P = N\beta_1 + c\beta_2$ and

$$ Q = K P\big[\Lambda P + c(r-\mu)\big] - c^2 r . $$

If $Q > 0$, there is a unique positive equilibrium, with

$$ \bar T = \frac{c}{P}, \qquad \int_0^\infty \bar i(a)\, da = \frac{Q}{P\,[K(N\sigma\beta_1 + c\beta_2) + c r]}, \qquad \bar V = \frac{N\sigma}{c}\int_0^\infty \bar i(a)\,da , $$

and $\bar i(a)$ proportional to $e^{-\sigma a}$. The equilibrium value $\bar T$ does not depend on $\tau$.

## Expansion

At equilibrium $\bar i(a) = \bar i(0) e^{-\sigma a}$, so the normalization gives $\int_0^\infty \beta \bar i = \bar i(0)$ and $\int_0^\infty \bar i = \bar i(0)/\sigma$, while $\bar V = (N/c)\int\beta\bar i$. The boundary condition then reads $\bar i(0) = \bar T(\beta_1 N/c + \beta_2)\bar i(0)$, forcing $\bar T = c/P$. Substituting into the uninfected-cell balance gives a linear equation for $\int \bar i$, whose solution is positive exactly when $Q > 0$. The model is recast as a non-densely defined abstract Cauchy problem on $\mathbb{R}^3 \times L^1$ after rescaling time and age by $\tau$, which makes $\tau$ a smooth bifurcation parameter.

## Sources

- Xiangming Zhang, Zhihua Liu, "Bifurcation Analysis of an Age Structured HIV Infection Model with Both Virus-to-Cell and Cell-to-Cell Transmissions", International Journal of Bifurcation and Chaos 28 (2018), 1850109, <https://doi.org/10.1142/s0218127418501092>. Published version of arXiv:1711.02739, cited next; locators there refer to the arXiv version.
- X. Zhang, Z. Liu, "Bifurcation analysis of an age structured HIV infection model with both virus-to-cell and cell-to-cell transmissions", arXiv:1711.02739 (2017), Section 1 (model and Assumption 1.1), Section 2.1 (rescaling) and Section 2.2 (existence of equilibria). <https://doi.org/10.48550/arXiv.1711.02739>
