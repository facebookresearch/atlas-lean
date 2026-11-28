# Disease-free threshold and persistence for multigroup SIR models

Guo, Li and Shuai (2006) study the $n$-group SIR model with immunization, whose reduced system (1.3) is

$$\dot S_k = (1 - p_k)\Lambda_k - (d^S_k + \theta_k)S_k - \sum_{j=1}^n \beta_{kj}S_k I_j, \qquad \dot I_k = \sum_{j=1}^n \beta_{kj}S_k I_j - (d^I_k + \epsilon_k + \gamma_k)I_k,$$

where, as in the source's Section 1, all parameters are nonnegative, $p_k$ is the immunized fraction of the influx, and the natural death rates $d^S_k, d^I_k$ and the influxes $\Lambda_k$ are positive, on its compact positively invariant region $\Gamma$, with $R_0 = \rho(M_0)$ the spectral radius of the matrix $M_0$ of Eq. (1.7) (the [basic reproduction number](../../global-stability-of-multigroup-sir-epidemics/r0.md)). For irreducible $B = (\beta_{kj})$ they prove (Proposition 3.1): if $R_0 \le 1$, the disease-free equilibrium is the unique equilibrium and is globally stable in $\Gamma$; if $R_0 > 1$, it is unstable and the system is uniformly persistent in the interior of $\Gamma$. The endemic case of the source, Theorem 3.3 (for $R_0 > 1$ a unique endemic equilibrium that attracts the interior of $\Gamma$), is the [Guo–Li–Shuai theorem](../../global-stability-of-multigroup-sir-epidemics/exists-endemic-globally-stable.md) and is not restated here.

## Depends on

- [Basic reproduction number](../../global-stability-of-multigroup-sir-epidemics/r0.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

1. The model (1.2)–(1.3), the invariant region $\Gamma$, the matrix $M_0$ and $R_0$.
2. The case $R_0 \le 1$: uniqueness of the disease-free equilibrium and its global stability in $\Gamma$ via [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md).
3. The case $R_0 > 1$: instability of the disease-free equilibrium and uniform persistence in the interior of $\Gamma$.

## Sources

- H. Guo, M. Y. Li and Z. Shuai, Global stability of the endemic equilibrium of multigroup SIR epidemic models, Can. Appl. Math. Q. 14 (2006), 259–284, Eqs. (1.3) and (1.7) and Proposition 3.1.
