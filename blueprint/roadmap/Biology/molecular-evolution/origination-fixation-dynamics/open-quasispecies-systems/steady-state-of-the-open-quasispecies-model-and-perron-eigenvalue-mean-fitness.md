# Steady state of the open quasispecies model and Perron-eigenvalue mean fitness

**Model.** Let $\mathbf{u}(t) = (u_1, \dots, u_n) \in \mathbb{R}^n_+$ count the individuals of $n$ types with replication rates (fitness landscape) $\mathbf{M} = \operatorname{diag}(m_1, \dots, m_n)$, $m_i \ge 0$, death rates $\mathbf{D} = \operatorname{diag}(d_1, \dots, d_n)$, $d_i > 0$, and column-stochastic mutation matrix $\mathbf{Q} = (q_{ij})$, $q_{ij} \ge 0$, $q_{ii} > 0$, $\sum_i q_{ij} = 1$ ($q_{ij}$ is the probability that replication of type $j$ yields type $i$). With total size $S = \sum_i u_i$ and resource saturation $e^{-\gamma S}$, $\gamma > 0$, the open quasispecies system is

$$\frac{d\mathbf{u}}{dt} = e^{-\gamma S(t)}\,\mathbf{Q}\mathbf{M}\,\mathbf{u}(t) - \mathbf{D}\,\mathbf{u}(t), \qquad \mathbf{u}(0) > 0.$$

A steady state $\bar{\mathbf{u}}$ satisfies the nonlinear eigenproblem

$$\mathbf{D}^{-1}\mathbf{Q}_m\,\bar{\mathbf{u}} = e^{\gamma S(\bar{\mathbf{u}})}\,\bar{\mathbf{u}}, \qquad \mathbf{Q}_m = \mathbf{Q}\mathbf{M},$$

and, because $\mathbf{Q}$ is column-stochastic, its steady-state mean fitness is

$$\bar f = e^{\gamma S(\bar{\mathbf{u}})} = \frac{\sum_i m_i \bar u_i}{\sum_i d_i \bar u_i}.$$

**Theorem.** Assume $\mathbf{D}^{-1}\mathbf{Q}_m$ is a positive matrix with Perron eigenvalue $\lambda$. Let $\eta > 1$ and restrict to the level set $S(\bar{\mathbf{u}}) = \gamma^{-1}\ln\eta$. A unique nontrivial steady state $\bar{\mathbf{u}} \in \mathbb{R}^n_+$ on this set exists if and only if $\lambda = \eta > 1$. Consequently a nontrivial steady state exists iff $\lambda > 1$; it is the Perron eigenvector scaled to total size $S = \gamma^{-1}\ln\lambda$, and the steady-state mean fitness equals the Perron eigenvalue, $\bar f = \lambda(\mathbf{D}^{-1}\mathbf{Q}\mathbf{M})$.

**Bounded adaptation.** If, during evolutionary adaptation, landscapes stay in $\{\mathbf{M} : \sum_i m_i \le K\}$ and $\lambda(\mathbf{D}^{-1}\mathbf{Q}_m) > 1$ throughout, then every steady state lies in the convex set $\{S(\bar{\mathbf{u}}) \le \gamma^{-1}\ln(K/\check d)\}$, $\check d = \min_i d_i$.

## Depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md)

## Expansion

At a steady state the scalar $e^{\gamma S}$ is an eigenvalue of the positive matrix $\mathbf{D}^{-1}\mathbf{Q}_m$ with a positive eigenvector, so by the Perron–Frobenius theorem it must be the Perron eigenvalue $\lambda$, and $S \ge 0$ forces $\lambda \ge 1$ (with $\lambda = 1$ only at $S = 0$). Conversely the Perron vector, normalized to total $\gamma^{-1}\ln\lambda$, solves the equation. The bound uses $\bar f = \sum m_i \bar u_i / \sum d_i \bar u_i \le K/\check d$. On a slow evolutionary time scale, where fitness landscape and mutation matrix change to maximize mean fitness, this identifies the quantity being maximized with the Perron eigenvalue, which recasts Fisher's fundamental theorem for open systems.

## Sources

- I. Samokhin, T. Yakushkina and A. S. Bratus, "Open quasispecies systems: new approach to evolutionary adaptation", *Chinese Journal of Physics* 77 (2022), 1770–1781, <https://doi.org/10.1016/j.cjph.2021.11.004>; preprint arXiv:2011.11742 (2020), Section 1.1 (open quasispecies model), Section 2 (steady-state equation, mean fitness identity, Theorems 2.1 and 2.2), <https://doi.org/10.48550/arXiv.2011.11742>.
