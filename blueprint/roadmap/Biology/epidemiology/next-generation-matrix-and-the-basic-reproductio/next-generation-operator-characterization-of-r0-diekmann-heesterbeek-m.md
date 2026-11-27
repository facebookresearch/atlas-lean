# Sign of the real-time growth rate and the basic reproduction ratio

Let infected individuals be structured by a heterogeneity state $\xi$ in a set $\Omega$, let $S(\xi)$ be the density of susceptibles, and let $A(\tau, \xi, \eta)$ be the expected infectivity at infection age $\tau$ of an individual of state $\eta$ towards susceptibles of state $\xi$, with next-generation operator $(K(S)\phi)(\xi) = S(\xi)\int_\Omega\int_0^\infty A(\tau, \xi, \eta)\,d\tau\,\phi(\eta)\,d\eta$ on $L^1(\Omega)$ (Diekmann, Heesterbeek and Metz 1990, Eq. (2.1)) and [basic reproduction ratio](../next-generation-operator-and-basic-reproduction/generation-growth.md) $R_0 = r(K(S))$. The definition, the decay of $K(S)^m\phi$ for $R_0 < 1$, the growth for $R_0 > 1$ and the separable case are separate statements ([subcritical decay](../next-generation-operator-and-basic-reproduction/tendsto-norm-pow-apply-zero.md), [supercritical growth](../next-generation-operator-and-basic-reproduction/exists-nonneg-unbounded-of-one-lt.md), [growth at rate $R_0$ under irreducibility](../next-generation-operator-and-basic-reproduction/tendsto-norm-pow-apply-rpow.md), [$R_0$ for a separable kernel](../next-generation-operator-and-basic-reproduction/generation-growth-eq-integral-of-separab.md)). This page states the link with the real-time dynamics. Assume that $K(S)$ is a positive compact operator on $L^1(\Omega)$ whose spectral radius $r(K(S))$ is an eigenvalue, let $(K_\lambda\phi)(\xi) = S(\xi)\int_\Omega\int_0^\infty A(\tau, \xi, \eta)e^{-\lambda\tau}\,d\tau\,\phi(\eta)\,d\eta$ (Eq. (2.5)), and assume that among the $\lambda$ for which $K_\lambda$ has the eigenvalue one, those of largest real part include a real one, $\lambda_d$, the real-time growth rate of the linearized epidemic $i(t, \xi) = S(\xi)\int_\Omega\int_0^\infty A(\tau, \xi, \eta)\,i(t - \tau, \eta)\,d\tau\,d\eta$ (Eq. (2.4)). Then $\lambda_d > 0$ exactly when $R_0 > 1$ and $\lambda_d < 0$ exactly when $R_0 < 1$ (Diekmann, Heesterbeek and Metz 1990, Section 2). The source names compactness only as an example of a condition on $K(S)$ under which $r(K(S))$ is an eigenvalue and lists no explicit conditions on $A$; conditions on $A$ and $S$ that imply these assumptions are a separate target (Expansion item 1).

## Depends on

- [The basic reproduction ratio `R₀`](../next-generation-operator-and-basic-reproduction/generation-growth.md)

## Expansion

1. Separate target, with its own source: conditions on $A$ and $S$ under which $K(S)$ is a positive compact operator on $L^1(\Omega)$ with $r(K(S))$ an eigenvalue and the real growth rate $\lambda_d$ exists.
2. The real-time growth rate $\lambda_d$ from Eqs. (2.4)–(2.5).
3. The equivalences $\lambda_d > 0 \Leftrightarrow R_0 > 1$ and $\lambda_d < 0 \Leftrightarrow R_0 < 1$.

## Sources

- O. Diekmann, J. A. P. Heesterbeek and J. A. J. Metz, On the definition and the computation of the basic reproduction ratio $R_0$ in models for infectious diseases in heterogeneous populations, J. Math. Biol. 28 (1990), 365–382, Section 2 and Eqs. (2.1)–(2.5), (3.1)–(3.3). <https://doi.org/10.1007/bf00178324>
