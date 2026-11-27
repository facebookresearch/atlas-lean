# Influence function and multiple robustness of the proximal mediation functional

In the setting of the [proximal mediation formula](proximal-mediation-formula.md), besides the outcome bridges $h_1, h_0$ consider
*treatment confounding bridge functions* $q_0(z, x)$ and $q_1(z, m, x)$ solving

$$E\{q_0(Z, X) \mid W, A=0, X\} = \frac{1}{f(A = 0 \mid W, X)},$$

$$E\{q_1(Z, M, X) \mid W, A=1, M, X\}\, f(A=1 \mid W, M, X) = E\{q_0(Z, X) \mid W, A=0, M, X\}\, f(A=0 \mid W, M, X).$$

Under Assumptions 1–5 of that page, each of the representations

$$\psi = E\{\mathbf 1(A=0)\, q_0(Z,X)\, h_1(W,M,X)\} = E\{\mathbf 1(A=1)\, q_1(Z,M,X)\, Y\} = E\{h_0(W,X)\}$$

identifies $\psi = E[Y\{1,M(0)\}]$ under its own existence and completeness conditions, which differ:

- the first, when $h_1$ and $q_0$ exist, under the completeness condition 6(i) (given $Z, A = 1, M, X$) and the completeness condition stated as Assumption A.1.2 of the source's Supplementary Material;
- the second, when $q_0$ and $q_1$ exist, under Assumptions A.1.1–A.1.2 of the Supplementary Material, without Assumption 6;
- the third, when $h_1$ and $h_0$ exist, under Assumption 6 (both parts), as on the formula page.

**Theorem.** Suppose bridge functions $h_1, h_0$ exist at all laws of the semiparametric model, $q_0, q_1$ exist at the true law,
Assumption 6 holds, and $\psi$ is unique. Then

$$\mathrm{IF}_\psi = \mathbf 1(A=1)\, q_1(Z,M,X)\{Y - h_1(W,M,X)\} + \mathbf 1(A=0)\, q_0(Z,X)\{h_1(W,M,X) - h_0(W,X)\} + h_0(W,X) - \psi$$

is an influence function for $\psi$; if moreover the conditional-expectation operators $T_1 : L_2(W,M,X) \to L_2(Z, A=1, M, X)$, $g \mapsto E\{g(W,M,X)\mid Z, A=1, M, X\}$, and
$T_0 : L_2(W,M,X) \to L_2(Z, A=0, X)$, $g \mapsto E\{g(W,M,X)\mid Z, A=0, X\}$, are surjective at the true law (both defined on functions of
$(W, M, X)$; surjectivity of the second on the smaller space of functions of $(W, X)$ would be a stronger condition) and all bridges are unique, the semiparametric efficiency bound is
$E(\mathrm{IF}_\psi^2)$. The estimator solving $\sum_i \mathrm{IF}_\psi(O_i) = 0$ with working models for $(h_1, h_0, q_0, q_1)$ is
consistent if any one of the pairs $(h_1, h_0)$, $(q_0, h_1)$ or $(q_0, q_1)$ is correctly specified.

## Depends on

- [Proximal mediation formula for the natural direct and indirect effects](proximal-mediation-formula.md)

## Expansion

The influence function has mean zero whenever one of the three pairs is correct: with correct $(h_1,h_0)$ the first two terms
have conditional mean zero; with correct $q_0, h_1$ the first term vanishes and the second recentres $h_0$; with correct
$q_0, q_1$ the weights reproduce the cross-world reweighting from $A = 0$ to $A = 1$ and the bridge terms telescope. This is the
proximal analogue of the triply robust mediation estimator of Tchetgen Tchetgen and Shpitser. (Dukes, Shpitser and Tchetgen
Tchetgen 2023, published edition: Theorem 2 with Equations 7–12, Assumption 7, Theorem 3 and Section 3.2.)

## Sources

- O. Dukes, I. Shpitser, and E. J. Tchetgen Tchetgen, "Proximal mediation analysis", Biometrika (2023), <https://doi.org/10.1093/biomet/asad015>; accepted version in the journal's format <https://par.nsf.gov/servlets/purl/10428415>. Numbering of the published edition: Assumptions 1–7, Theorem 2 (alternative identification formulas, Equations 7–12, with Supplementary Assumptions A.1.1–A.1.2), Theorem 3 (influence function and efficiency bound) and Section 3.2 (multiply robust estimation). The arXiv preprint (2109.11904) numbers these differently.
