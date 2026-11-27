# Sign of the real-time growth rate and the basic reproduction ratio

Let infected individuals be structured by a heterogeneity state $\xi$ in a set $\Omega$, let $S(\xi)$ be the density of susceptibles, and let $A(\tau, \xi, \eta)$ be the expected infectivity at infection age $\tau$ of an individual of state $\eta$ towards susceptibles of state $\xi$, with next-generation operator $(K(S)\phi)(\xi) = S(\xi)\int_\Omega\int_0^\infty A(\tau, \xi, \eta)\,d\tau\,\phi(\eta)\,d\eta$ on $L^1(\Omega)$ (Diekmann, Heesterbeek and Metz 1990, Eq. (2.1)) and [basic reproduction ratio](../next-generation-operator-and-basic-reproduction/generation-growth.md) $R_0 = r(K(S))$. The definition, the decay of $K(S)^m\phi$ for $R_0 < 1$, the growth for $R_0 > 1$ and the separable case are separate statements ([subcritical decay](../next-generation-operator-and-basic-reproduction/tendsto-norm-pow-apply-zero.md), [supercritical growth](../next-generation-operator-and-basic-reproduction/exists-nonneg-unbounded-of-one-lt.md), [growth at rate $R_0$ under irreducibility](../next-generation-operator-and-basic-reproduction/tendsto-norm-pow-apply-rpow.md), [$R_0$ for a separable kernel](../next-generation-operator-and-basic-reproduction/generation-growth-eq-integral-of-separab.md)). This page states the link with the real-time dynamics: under the source's conditions on $A$ making $K(S)$ positive and compact with $r(K(S))$ a dominant eigenvalue, the real-time growth rate $\lambda_d$ of the linearized epidemic, defined through Eq. (2.5), satisfies $\lambda_d > 0$ exactly when $R_0 > 1$ and $\lambda_d < 0$ exactly when $R_0 < 1$ (Diekmann, Heesterbeek and Metz 1990, Section 2).

## Depends on

- [The basic reproduction ratio `R₀`](../next-generation-operator-and-basic-reproduction/generation-growth.md)

## Expansion

1. The model: the heterogeneity space $\Omega$, the infectivity kernel $A$, the next-generation operator on $L^1(\Omega)$ and the conditions making it positive and compact.
2. The real-time growth rate $\lambda_d$ from Eq. (2.5).
3. The equivalences $\lambda_d > 0 \Leftrightarrow R_0 > 1$ and $\lambda_d < 0 \Leftrightarrow R_0 < 1$.

## Sources

- O. Diekmann, J. A. P. Heesterbeek and J. A. J. Metz, On the definition and the computation of the basic reproduction ratio $R_0$ in models for infectious diseases in heterogeneous populations, J. Math. Biol. 28 (1990), 365–382, Section 2 and Eqs. (2.1)–(2.5), (3.1)–(3.3). <https://doi.org/10.1007/bf00178324>
