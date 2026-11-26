# Competitive exclusion in the multi-strain diffusive SIS model

Let $\Omega \subset \mathbb R^n$ be a bounded domain with smooth boundary and outer normal $\vec n$. The multi-strain diffusive SIS model with $k$ strains and no co-infection is

$$\begin{aligned} \partial_t S &= d_S \Delta S + \sum_{i=1}^k \gamma_i I_i - \frac{S \sum_{i=1}^k \beta_i I_i}{S + \sum_{j=1}^k I_j}, \\ \partial_t I_i &= d_i \Delta I_i - \gamma_i I_i + \frac{\beta_i S I_i}{S + \sum_{j=1}^k I_j}, \qquad i = 1, \dots, k, \end{aligned}$$

in $\Omega \times (0, \infty)$, with $\partial_{\vec n} S = \partial_{\vec n} I_i = 0$ on $\partial\Omega$, positive Hölder continuous transmission and recovery rates $\beta_i, \gamma_i$ on $\overline\Omega$, diffusion rates $d_S \ge 0$, $d_i > 0$, and nonnegative initial data of total mass $N = \int_\Omega (S + \sum_i I_i)\,dx > 0$, which is conserved.

**Theorem.** Let $k \ge 2$, $d_S > 0$, $d_1 = \dots = d_k = d$, and suppose the [threshold quantity](threshold-dynamics-of-the-multi-strain-diffusive-sis-model.md) satisfies $R_0 > 1$. For every classical solution with positive initial data, $\|(I_2, \dots, I_k)(t, \cdot)\|_\infty \to 0$ in each of the following cases.

1. $\beta_1 = \dots = \beta_k$ and $\gamma_1 < \min_{2 \le i \le k} \gamma_i$.
2. $\gamma_1 = \dots = \gamma_k$ and $\beta_1 > \max_{2 \le i \le k} \beta_i$.
3. $\beta_i = \hat\beta_i g$ and $\gamma_i = \hat\gamma_i h$ for positive constants $\hat\beta_i, \hat\gamma_i$ and positive Hölder functions $g, h$, with $\hat\beta_1 \ge \max_{j \ge 2} \hat\beta_j$ and $\hat\beta_1/\hat\gamma_1 > \max_{j \ge 2} \hat\beta_j/\hat\gamma_j$.

If moreover $d_S = d$ and each $R_i = \beta_i/\gamma_i$ is a constant with $R_1 > \max_{j \ge 2} R_j$, then the solution converges uniformly to $\bigl(N/(|\Omega| R_1),\ \tfrac{N}{|\Omega|}(1 - 1/R_1),\ 0, \dots, 0\bigr)$.

**Spatially homogeneous case.** Without diffusion and with constant rates, every positive solution of the ODE system satisfies

$$I_i(t) = I_i(0) \Bigl(\frac{I_j(t)}{I_j(0)}\Bigr)^{\beta_i/\beta_j} \exp\Bigl(\Bigl(\frac{1}{R_j} - \frac{1}{R_i}\Bigr)\beta_i t\Bigr), \qquad i, j = 1, \dots, k,$$

so the strain with the largest $R_i$ drives all others to extinction (competitive exclusion).

## Depends on

- [Threshold dynamics of the multi-strain diffusive SIS model](threshold-dynamics-of-the-multi-strain-diffusive-sis-model.md)

## Expansion

For the ODE identity write $F = S/(S + \sum_l I_l)$; then $(\ln I_i)' = \beta_i F - \gamma_i$, so $(\ln I_i)'/\beta_i - (\ln I_j)'/\beta_j = 1/R_j - 1/R_i$, and integrating gives the formula. Since $I_j$ stays bounded, $R_j > R_i$ forces $I_i \to 0$. The PDE cases use comparison of $I_i$ with suitable multiples of powers of $I_1$, which requires the common diffusion rate.

## Sources

- Y. Lou and R. B. Salako, *Control strategies for a multi-strain epidemic model*, Bull. Math. Biol. 84 (2022), 10, <https://doi.org/10.1007/s11538-021-00957-6>, PMCID PMC8627176 (Theorem 2.2 and equation (4), after Bremermann and Thieme (1989)).
