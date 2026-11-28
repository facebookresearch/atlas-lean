# Weak-selection isothermal theorem for death-Birth updating

**Theorem.** Let $G$ be a weighted, undirected, connected graph of size $N \ge 2$ with no self-loops which is **isothermal**: every vertex has the same weighted degree $w_i = \sum_j w_{ij}$, equivalently $\pi_i = 1/N$ for all $i$. Then for death-Birth updating with mutant fitness $1+\delta$,

$$\rho_G(1+\delta) = \rho_{K_N}(1+\delta) + O(\delta^2),$$

i.e. the fixation-probability curves of $G$ and of the complete graph are tangent at $r = 1$, and $G$ neither amplifies nor suppresses weak selection.

**Perturbation recipe.** If $G_\epsilon$ is a smooth family of weighted graphs with $G_0$ isothermal, then

$$\frac{dN_{\mathrm{eff}}}{d\epsilon}\Big|_{\epsilon=0} = -\sum_i \tau_i\,\frac{d\pi_i}{d\epsilon}\Big|_{\epsilon=0},$$

so lowering the relative weighted degree of vertices with large remeeting time $\tau_i$ (or raising it for small $\tau_i$) produces amplifiers of weak selection.

Unlike the Birth-death isothermal theorem, the equality is only first order: for $N \ge 4$ the cycle $C_N$ is isothermal, yet $\rho_{C_N}(r) < \rho_{K_N}(r)$ for all $r \ne 1$ (a reducer of fixation; for $N = 3$, $C_3 = K_3$ and the formula below gives $2r/(3(r+1))$ for both), with $\rho_{C_N}(r) = 2(r-1)/(3r - 1 + r^{-(N-3)} - 3r^{-(N-2)})$.

## Depends on

- [Coalescence-time formula for weak-selection fixation under death-Birth updating](coalescence-time-formula-for-weak-selection-fixation-under-death-birth-updating.md)

## Expansion

For an isothermal graph, Kac's formula $\sum_i \pi_i^2\tau_i = 1$ gives

$$N_{\mathrm{eff}} = \sum_i \frac1N\tau_i = N\sum_i \frac{1}{N^2}\tau_i = N\sum_i \pi_i^2\tau_i = N,$$

and the coalescence-time formula then matches the expansion $\rho_{K_N}(1+\delta) = 1/N + \delta(N-2)/(2N) + O(\delta^2)$. The perturbation identity follows by differentiating $N_{\mathrm{eff}} = \sum_i\pi_i\tau_i$ and Kac's identity at $\epsilon = 0$ and using $\pi_i = 1/N$ there. For example, decreasing one edge weight at the vertex of largest remeeting time in an unweighted 3-regular graph on 12 vertices produces an amplifier of weak selection, still with $N_{\mathrm{eff}} \approx 12.03 > 12$ after the edge is deleted.

## Sources

- B. Allen, C. Sample, R. Jencks, J. Withers, P. Steinhagen, L. Brizuela, J. Kolodny, D. Parke, G. Lippner, Y. A. Dementieva, "Transient amplifiers of selection and reducers of fixation for death-Birth updating on graphs", PLoS Computational Biology 16 (2020) e1007529, Eqs. (3), (11)–(13), Weak-Selection Isothermal Theorem and Fig 2, <https://doi.org/10.1371/journal.pcbi.1007529>, PMCID PMC6968840.
