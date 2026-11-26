# Target reproduction number

**Setting.** Let $K = [k_{ij}] \in \mathbb{R}^{n\times n}$ be a nonnegative next-generation matrix, $k_{ij}$ the expected number of new infections of type $i$ produced by one infected of type $j$, and $R_0 = \rho(K)$ its spectral radius. Let $S \subseteq \{1,\dots,n\}^2$ be a set of entries targeted by a control measure, and let $K_S$ be the matrix with $(K_S)_{ij} = k_{ij}$ for $(i,j) \in S$ and $0$ otherwise.

**Definition.** If $\rho(K - K_S) < 1$, the target reproduction number is

$$T_S = \rho\big(K_S\,(I - K + K_S)^{-1}\big).$$

**Properties.**

1. If $S$ consists of all entries of one or more rows (or columns) of $K$, $T_S$ is the type reproduction number of Roberts and Heesterbeek.
2. If $K$ is irreducible, then $T_S < 1 \iff R_0 < 1$, $T_S = 1 \iff R_0 = 1$ and $T_S > 1 \iff R_0 > 1$.
3. Reducing every targeted entry by a common factor $1 - \varepsilon$ with $\varepsilon > 1 - 1/T_S$ brings the system below threshold, so $1 - 1/T_S$ is the critical control effort on the targeted entries.

**Elasticity.** For a parameter $\omega$ entering $R_0$, the sensitivity index is $\partial R_0/\partial\omega$ and the elasticity index is

$$\Upsilon_{\omega}^{R_0} = \frac{\partial R_0}{\partial \omega}\,\frac{\omega}{R_0},$$

the relative change of $R_0$ per relative change of $\omega$; its sign gives the direction of the effect and its magnitude the relative importance of $\omega$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Since $\rho(K - K_S) < 1$, the Neumann series $(I - (K - K_S))^{-1} = \sum_{m \ge 0}(K - K_S)^m$ converges and is nonnegative. The matrix $K_S (I - K + K_S)^{-1}$ counts infections produced through a targeted entry after any number of generations through untargeted entries only, so $T_S$ is the reproduction number of "targeted generations". Scaling $K_S$ by $1-\varepsilon$ scales $T_S$ by $1 - \varepsilon$; the equivalence in property 2 follows from Perron–Frobenius comparison of $\rho(K)$ with $\rho\big((1-\varepsilon)K_S + K - K_S\big)$ at $\varepsilon = 0$ and at the critical value. For a perfect vaccine given to a fraction $p$ of a single-type population, $T_S = R_0$ and the rule $p > 1 - 1/R_0$ is recovered.

## Sources

- P. van den Driessche, "Reproduction numbers of infectious disease models", Infectious Disease Modelling 2(3) (2017) 288–303, Sections 3 and 4.1–4.2, <https://doi.org/10.1016/j.idm.2017.06.002> (PMC6002118).
- M. G. Roberts and J. A. P. Heesterbeek, "A new method for estimating the effort required to control an infectious disease", Proc. R. Soc. Lond. B 270 (2003) 1359–1364.
- Z. Shuai, J. A. P. Heesterbeek and P. van den Driessche, "Extending the type reproduction number to infectious disease control targeting contacts between types", J. Math. Biol. 67 (2013) 1067–1082.
