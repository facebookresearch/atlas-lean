# Next-generation operator and the basic reproduction ratio

Let infected individuals be structured by a heterogeneity state $\xi$ in a set $\Omega$, let $S(\xi)$ be the density of susceptibles, and let $A(\tau, \xi, \eta)$ be the expected infectivity at infection age $\tau$ of an individual of state $\eta$ towards susceptibles of state $\xi$. Diekmann, Heesterbeek and Metz (1990, Eq. (2.1)) define the next-generation operator $(K(S)\phi)(\xi) = S(\xi)\int_\Omega\int_0^\infty A(\tau, \xi, \eta)\,d\tau\,\phi(\eta)\,d\eta$ on $L^1(\Omega)$. After $m$ generations the infected population is $K(S)^m\phi$, so the per-generation growth factor in the long run is the spectral radius $r(K(S)) = \lim_{m\to\infty}\|K(S)^m\|^{1/m}$ (Eq. (2.2)); $K(S)^m\phi \to 0$ if $r(K(S)) < 1$, while it can be made arbitrarily large if $r(K(S)) > 1$. Since $K(S)$ is positive, conditions such as compactness make $r(K(S))$ an eigenvalue, the dominant eigenvalue, with a positive eigenvector, and the source defines $R_0 = r(K(S))$; the real-time growth rate of the linearized epidemic is positive exactly when $R_0 > 1$ and negative exactly when $R_0 < 1$. For a separable mixing rate $\int_0^\infty A(\tau, \xi, \eta)\,d\tau = a(\xi)b(\eta)$, $K(S)$ has one-dimensional range and $R_0 = \int_\Omega b(\eta)S(\eta)a(\eta)\,d\eta$ (Eq. (3.3)).

## Expansion

1. The model: the heterogeneity space $\Omega$, the infectivity kernel $A$, the next-generation operator on $L^1(\Omega)$ and conditions for its boundedness.
2. The spectral radius formula and its interpretation as the per-generation growth factor; the limitations of the operator norm and of averaged factors discussed in the source.
3. Positivity, compactness and irreducibility: $r(K(S))$ as a dominant eigenvalue with a positive eigenvector (compare the [Krein–Rutman theorem for $C(K)$](../../../Analysis/operator-theory/spectral-theory/krein-rutman.md); the $L^1$ form is needed here).
4. The real-time growth rate $\lambda_d$ from Eq. (2.5) and the equivalences $\lambda_d > 0 \Leftrightarrow R_0 > 1$, $\lambda_d < 0 \Leftrightarrow R_0 < 1$.
5. The separable case (Eq. (3.3)) and the finite-type case, the [basic reproduction number of the next-generation matrix](../../../Biology/epidemiology/next-generation-matrix-and-the-basic-reproductio/r0.md).

## Sources

- O. Diekmann, J. A. P. Heesterbeek and J. A. J. Metz, On the definition and the computation of the basic reproduction ratio $R_0$ in models for infectious diseases in heterogeneous populations, J. Math. Biol. 28 (1990), 365–382, Section 2 and Eqs. (2.1)–(2.5), (3.1)–(3.3). <https://doi.org/10.1007/bf00178324>
