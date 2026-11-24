# Cushing–Zhou net reproductive number for matrix models

Let $T = (\tau_{ij})$ be an $m \times m$ transition matrix with $0 \le \tau_{ij} \le 1$ and column sums at most $1$, $F = (f_{ij}) \ge 0$ a fertility matrix, and $P = F + T$ the projection matrix. Assume, as in Cushing (2011, assumptions A1–A3), that $P$ is primitive, that $T \ne 0$ with spectral radius $\rho(T) < 1$, and that $F(I - T)^{-1}$ has a simple dominant eigenvalue with nonnegative left and right eigenvectors. Let $r = \rho(P)$ be the growth rate and $R_0 = \rho(F(I - T)^{-1})$ the net reproductive number. Then $r = 1$ if and only if $R_0 = 1$, and otherwise $r$ and $R_0$ lie on the same side of $1$: $r > 1 \iff R_0 > 1$ and $r < 1 \iff R_0 < 1$ (Cushing and Zhou 1994, as stated in Cushing 2011, Section 2 and Theorem 1(a)). Consequently the zero solution of $x_{t+1} = P x_t$ is asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$, since a linear map is asymptotically stable exactly when its spectral radius is below $1$.

## Expansion

1. The model: transition and fertility matrices, the projection matrix, and the hypotheses A1–A3 (compare [Perron–Frobenius](../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md) for primitive matrices).
2. The interpretation of $(I - T)^{-1} = \sum_k T^k$ and of $F(I - T)^{-1}$ as the next-generation matrix; $F(I - T)^{-1}$ and $(I - T)^{-1}F$ have the same spectral radius.
3. The threshold equivalence of $r$ and $R_0$ relative to $1$ (the theorem of Cushing and Zhou, with the further argument of Li and Schneider 2002).
4. The stability corollary for the linear projection.
5. Formulas for $R_0$ for models with one newborn class (Leslie and Usher models), as separate statements.

## Sources

- J. M. Cushing, On the relationship between $r$ and $R_0$ and its role in the bifurcation of stable equilibria of Darwinian matrix models, J. Biol. Dyn. 5 (2011), 277–297, Section 2, assumptions A1–A3 and Theorem 1. <https://doi.org/10.1080/17513758.2010.491583>
- Original result: J. M. Cushing and Y. Zhou, The net reproductive value and stability in matrix population models, Nat. Resour. Model. 8 (1994), 297–333. <https://doi.org/10.1111/j.1939-7445.1994.tb00188.x> The threshold equivalence follows its statement in Cushing (2011).
- Original result: C.-K. Li and H. Schneider, Applications of Perron–Frobenius theory to population dynamics, J. Math. Biol. 44 (2002), 450–462. <https://doi.org/10.1007/s002850100132> Cited for the same equivalence in Cushing (2011).
