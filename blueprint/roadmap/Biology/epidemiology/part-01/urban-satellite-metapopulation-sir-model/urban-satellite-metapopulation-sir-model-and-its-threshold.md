# Urban–satellite metapopulation SIR model and its threshold

**Model.** An urban centre $W$ and satellite cities $1, \dots, n$ host SIR dynamics with births $b_x$,
common death rate $d$ and recovery rate $\gamma$. Because of their population sizes, the urban centre
has standard incidence $\beta_W S_W I_W / N_W$ and each satellite mass-action incidence
$\beta_i S_i I_i$. Individuals move from $W$ to city $i$ at rate $m_{iW}$ and back at rate $m_{Wi}$,
independently of disease status:

$$I_W' = \frac{\beta_W S_W I_W}{N_W} - (\gamma + d) I_W + \sum_{i=1}^{n} \bigl(m_{Wi} I_i - m_{iW} I_W\bigr), \qquad
I_i' = \beta_i S_i I_i - (\gamma + d) I_i + m_{iW} I_W - m_{Wi} I_i ,$$

and analogously for $S$ and $R$. Let $M$ be the movement matrix (off-diagonal entries $m_{Wi}$ in row
$W$ and $m_{iW}$ in row $i$, column sums zero). If all $m_{iW}, m_{Wi} > 0$, then $M$ is irreducible,
$-(M - cI)$ is a nonsingular M-matrix with $-(M - cI)^{-1} \gg 0$ for every $c > 0$, and the city
populations converge to $N^* = -(M - dI)^{-1} b \gg 0$.

**Next-generation matrices.** At the disease-free equilibrium,

$$F = \operatorname{diag}\bigl(\beta_W,\ \beta_1 N_1^*, \dots, \beta_n N_n^*\bigr), \qquad V = (\gamma + d) I - M,
\qquad \mathcal{R}_0 = \rho(F V^{-1}).$$

**Theorem.** If $\mathcal{R}_0 \le 1$, the disease-free equilibrium is globally asymptotically stable;
if $\mathcal{R}_0 > 1$, it is unstable, the system is uniformly persistent and an endemic equilibrium
exists.

**Proposition (localization).** Let $\mathcal{R}_0^W = \beta_W/(\gamma + d)$ and
$\mathcal{R}_0^i = \beta_i N_i^{**}/(\gamma + d)$ be the reproduction numbers of the isolated cities,
with $N_i^{**}$ the isolated equilibrium population. If $N_i^* = N_i^{**}$ for all $i$, then

$$\min\{\mathcal{R}_0^W, \mathcal{R}_0^1, \dots, \mathcal{R}_0^n\} \le \mathcal{R}_0 \le
\max\{\mathcal{R}_0^W, \mathcal{R}_0^1, \dots, \mathcal{R}_0^n\}.$$

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Global stability uses a Lyapunov function built from the Perron vector. Since $V$ is an irreducible
M-matrix, $V^{-1} \gg 0$ and $V^{-1}F \gg 0$ is primitive, with the same spectrum as $FV^{-1}$; let
$w \gg 0$ be its left Perron vector, $w V^{-1} F = \mathcal{R}_0 w$, equivalently
$w F^{-1} V = \mathcal{R}_0^{-1} w$. With $L = w F^{-1} I$ (that is, weights $w_W/\beta_W$ and
$w_i/(\beta_i N_i^*)$), the bounds $S_W \le N_W$ and $S_i \le N_i^*$ in the limiting region give

$$L' \le w F^{-1}(F - V) I = \bigl(1 - \mathcal{R}_0^{-1}\bigr)\, w\, I \le 0 \quad (\mathcal{R}_0 \le 1),$$

and LaSalle's principle finishes the argument. Persistence for $\mathcal{R}_0 > 1$ follows by
replacing $N(t)$ by its limit $N^*$ and using asymptotically autonomous systems. For the
localization, every column sum of $V$ equals $\gamma + d$, so $\mathbf{1}^{T} V^{-1} F$ is exactly the
vector of isolated-city reproduction numbers, and the spectral radius of a nonnegative matrix lies
between its smallest and largest column sums. Mobility therefore averages local transmission: under this population condition the coupled system
is supercritical whenever every city is, and subcritical whenever every city is.

## Sources

- J. Arino, S. Portet, "Epidemiological implications of mobility between a large urban centre and
  smaller satellite cities", Journal of Mathematical Biology 71 (2015) 1243-1265, model (1),
  Lemma 1, Propositions 1-3, Eqs. (8)-(14) and Theorems 1-2,
  <https://doi.org/10.1007/s00285-014-0854-z> (PMC7080072).
- M. Y. Li, Z. Shuai, "Global stability of an epidemic model in a patchy environment", Canadian
  Applied Mathematics Quarterly 17 (2009) 175-187.
