# Cycle-KL decomposition of entropy change in complex-balanced networks

**Setting.** A chemical reaction network has complexes $i$ with stoichiometric vectors $Y_i$ (column
$i$ of the species-by-complex matrix $Y$) and half-reaction rate constants $k_{ji}$ for reactions
$i \to j$, collected in an adjacency matrix $A$ on complexes (columns summing to zero). Mass-action
relaxation of species amounts $n$ reads $\dot n = Y A\, \psi(n)$ with $\psi_i(n) = n^{Y_i}$. Fixing a
positive fixed point $\underline n$, descale by $\hat A = A\, \operatorname{diag}\psi(\underline n)$ and
write $n = \underline n\, e^{\theta}$ componentwise, so $\psi_i(n/\underline n) = e^{\theta\cdot Y_i}$ and
$\dot n = Y \hat A\, \psi(n/\underline n)$. Fixed points fall into three nested classes:

| Class | Condition on the descaled matrix |
|---|---|
| general (current balance at each species) | $Y\hat A \mathbf 1 = 0$ |
| complex balanced | $\hat A \mathbf 1 = 0$ |
| detailed balanced | $\hat A^{\mathsf T} = \hat A$ |

**Statement.** Let the fixed point be complex balanced. Since $\mathbf 1^{\mathsf T}\hat A = 0$ and
$\hat A \mathbf 1 = 0$, the matrix $\hat A$ is a finite positive combination
$\sum_\alpha \bar\jmath_\alpha (P_\alpha - I_\alpha)$ of adjacency matrices of directed cycles $\alpha$ on
the complex graph, with coefficients $\bar\jmath_\alpha > 0$ equal to the stationary currents around the
cycles (2-cycles suffice under detailed balance). For the macrostate relative-entropy function
$\underline S_{\mathrm{eff}}$ (an $f$-divergence between Poisson product states, a Lyapunov function in this class), whose rate along relaxation trajectories is
$\theta\cdot\dot n$, one has

$$\dot{\underline S}{}^{\mathrm{rel}}_{\mathrm{eff}} = \theta\cdot\dot n = -\sum_\alpha \bar\jmath_\alpha \sum_{i \to j \in \alpha} e^{\theta\cdot Y_i}\log\frac{e^{\theta\cdot Y_i}}{e^{\theta\cdot Y_j}}
= -\sum_\alpha \bar\jmath_\alpha \Big(\sum_{i\in\alpha} e^{\theta\cdot Y_i}\Big)\, D_{\mathrm{KL}}\big(p_\alpha \,\|\, p_\alpha^{\leftarrow}\big) \le 0,$$

where $p_{i|\alpha} = e^{\theta\cdot Y_i}/\sum_{j\in\alpha} e^{\theta\cdot Y_j}$ is the normalized activity on
cycle $\alpha$ and $p_\alpha^{\leftarrow}$ is the same vector shifted one step along the cycle. Each cycle
contributes a term of the same sign, a finite decomposition stronger than the global convexity proof
of entropy decrease. Along escape (time-reversed) trajectories the analogous sum with the opposite
shift is nonnegative. Under detailed balance the two rates are equal and opposite; for merely
complex-balanced networks the antisymmetric part of the gradients,
$Y(\hat A - \hat A^{\mathsf T})\operatorname{diag}\psi\, (e^{\theta\cdot Y})^{\mathsf T}$, measures the
broken time-reversal symmetry (at $\theta = 0$, the antisymmetric part of $YAY^{\mathsf T}$). For
non-complex-balanced networks the stationary currents decompose only into balanced integer
hyperflows, which do not give sums of KL divergences of uniform sign.

## Depends on

- [Horn–Jackson inequality](../../complex-balancing-and-the-deficiency-zero-theore/helmholtz-rate-nonpos.md)

## Expansion

Writing $\hat A = \sum_\alpha \bar\jmath_\alpha (P_\alpha - I_\alpha)$ gives
$\theta\cdot Y\hat A\psi = \sum_\alpha\bar\jmath_\alpha\sum_{i\to j\in\alpha}(\theta\cdot Y_j - \theta\cdot Y_i)\,\psi_i$,
and $\theta\cdot Y_j - \theta\cdot Y_i = \log(\psi_j/\psi_i)$. Around a cycle the weights
$\psi_i$ and their shifted copies have the same total, so the log-sum inequality makes each cycle sum a
nonnegative multiple of a KL divergence between a distribution on the cycle and its rotation. The
existence of the cycle decomposition is exactly where complex balance enters: a nonnegative matrix
with zero row and column sums on a finite graph is a nonnegative combination of cycle matrices. The
same descaling applied to the microstate master equation (with the stationary distribution in place of
the fixed point) yields cycle decompositions proving non-negativity of the intrinsic relative-entropy
decrease and of the housekeeping entropy rate, for networks whose state-space cycles are suitably
finite.

## Sources

- E. Smith, "Intrinsic and extrinsic thermodynamics for stochastic population processes with multi-level large-deviation structure", Entropy 22(10) (2020) 1137, <https://doi.org/10.3390/e22101137> (PMC7597283). Sections 4.1–4.1.3 (Eqs. 35, 43–45), Section 5.1 (Table 3), Section 5.1.1 (Eqs. 50–57), Section 5.1.2 (Eqs. 58–59), Section 5.1.3.
