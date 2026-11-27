# Disease-free equilibrium and threshold of the multipatch dengue model

On patches $i = 1, \dots, n$ humans are $S_i^h, E_i^h, I_i^h, R_i^h$ (total $N_i^h$) and mosquitoes $S_i^v, E_i^v, I_i^v$. Humans of class $C \in \{S, E, I, R\}$ move from patch $j$ to patch $i$ at rate $m_{ij}^C \ge 0$; mosquitoes do not move. With biting rate $b_i$, transmission probabilities $\beta_i^h$ (vector to host) and $\beta_i^v$ (host to vector), recruitment $A_i^h, A_i^v > 0$, death rates $d_i^h, d_i^v > 0$, incubation rates $\nu_i^h, \nu_i^v > 0$, recovery rate $\gamma_i^h > 0$ and $b_i, \beta_i^h, \beta_i^v \ge 0$:

$$\begin{aligned}
\dot S_i^h &= A_i^h - \frac{b_i \beta_i^h}{N_i^h} S_i^h I_i^v + \sum_{j} m_{ij}^S S_j^h - \sum_{j} m_{ji}^S S_i^h - d_i^h S_i^h,\\
\dot E_i^h &= \frac{b_i \beta_i^h}{N_i^h} S_i^h I_i^v + \sum_{j} m_{ij}^E E_j^h - \sum_{j} m_{ji}^E E_i^h - (\nu_i^h + d_i^h) E_i^h,\\
\dot I_i^h &= \nu_i^h E_i^h + \sum_{j} m_{ij}^I I_j^h - \sum_{j} m_{ji}^I I_i^h - (\gamma_i^h + d_i^h) I_i^h,\\
\dot S_i^v &= A_i^v - \frac{b_i \beta_i^v}{N_i^h} S_i^v I_i^h - d_i^v S_i^v, \qquad \dot E_i^v = \frac{b_i \beta_i^v}{N_i^h} S_i^v I_i^h - (\nu_i^v + d_i^v) E_i^v, \qquad \dot I_i^v = \nu_i^v E_i^v - d_i^v I_i^v,
\end{aligned}$$

with $R_i^h$ fed by $\gamma_i^h I_i^h$. The vector parameters $b_i, \beta_i^h, \beta_i^v, d_i^v, \nu_i^v$ are functions of the patch temperature.

**Theorem (unique disease-free equilibrium).** Let $X = \operatorname{diag}\big(d_i^h + \sum_{j \ne i} m_{ji}^S\big) - M^S$, where $M^S$ has off-diagonal entries $m_{ij}^S$ and zero diagonal. Then $X$ is a nonsingular M-matrix and the system has the unique disease-free equilibrium

$$S^{h*} = X^{-1} A^h > 0, \qquad S_i^{v*} = A_i^v / d_i^v.$$

**Theorem (threshold).** Order the infected variables as $(E^h, E^v, I^h, I^v)$. The new-infection matrix $F$ has only the blocks $\operatorname{diag}(b_i\beta_i^h S_i^{h*}/N_i^h)$ (from $I^v$ into $E^h$) and $\operatorname{diag}(b_i \beta_i^v S_i^{v*}/N_i^h)$ (from $I^h$ into $E^v$), and the transition matrix is block lower triangular,

$$V = \begin{pmatrix} V_{11} & 0 & 0 & 0\\ 0 & V_{22} & 0 & 0\\ V_{31} & 0 & V_{33} & 0\\ 0 & V_{42} & 0 & V_{44} \end{pmatrix},$$

with $V_{11}$, $V_{33}$ the movement-plus-exit M-matrices of the $E^h$ and $I^h$ classes, $V_{22} = \operatorname{diag}(\nu_i^v + d_i^v)$, $V_{31} = -\operatorname{diag}(\nu_i^h)$, $V_{42} = -\operatorname{diag}(\nu_i^v)$, $V_{44} = \operatorname{diag}(d_i^v)$. With $R_0 = \rho(F V^{-1})$, the disease-free equilibrium is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$. For isolated patches ($m \equiv 0$) it reduces to $R_0 = \max_i R_{0i}$ with

$$R_{0i}^2 = \frac{b_i^2\, \beta_i^h \beta_i^v\, \nu_i^h \nu_i^v\, S_i^{h*} S_i^{v*}}{d_i^v (N_i^{h*})^2\,(\gamma_i^h + d_i^h)(\nu_i^h + d_i^h)(\nu_i^v + d_i^v)}.$$

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

$X$ has nonpositive off-diagonal entries and each column sum equals $d_i^h > 0$ (outflows from patch $i$ reappear as inflows elsewhere), so $X$ is strictly column diagonally dominant, hence a nonsingular M-matrix with $X^{-1} \ge 0$ and positive diagonal, giving $S^{h*} > 0$. The Jacobian at the equilibrium is block upper triangular with diagonal blocks $-\operatorname{diag}(X, \operatorname{diag}(d_i^v))$ (stable) and $F - V$, where $F \ge 0$ and $V$ is a nonsingular M-matrix; the next-generation threshold theorem gives the stability dichotomy. For an isolated patch the host-vector cycle has two generations, so $R_{0i}$ is the geometric mean of the host-to-vector and vector-to-host reproduction numbers. With movement between two patches, $R_0$ is an explicit root of a quadratic in $R_{01}^2, R_{02}^2$ whose coefficients depend on the movement rates of exposed and infectious hosts, so movement can couple a subcritical patch to a supercritical one.

## Sources

- G. R. Phaijoo and D. B. Gurung, "Modeling impact of temperature and human movement on the persistence of dengue disease", Computational and Mathematical Methods in Medicine 2017 (2017) 1747134, Eqs. (1)–(15), Theorems 1–2, <https://doi.org/10.1155/2017/1747134>, PMCID PMC5651158.
- P. van den Driessche and J. Watmough, "Reproduction numbers and sub-threshold endemic equilibria for compartmental models of disease transmission", Mathematical Biosciences 180 (2002) 29–48, <https://doi.org/10.1016/S0025-5564(02)00108-6>.
