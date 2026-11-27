# Invariant-subspace coarse-graining of a transition matrix

Let $P \in \mathbb{R}^{N \times N}$ be a row-stochastic matrix, let $D$ be a positive definite diagonal matrix, and let $\chi \in \mathbb{R}^{N \times n}$ have full column rank $n$. Define the projected matrix

$$P_c = (\chi^{\top} D \chi)^{-1} \chi^{\top} D P \chi \in \mathbb{R}^{n \times n}.$$

**Theorem.** Suppose the column space of $\chi$ is invariant under $P$, i.e. $P\chi = \chi \Lambda$ for some $\Lambda \in \mathbb{R}^{n \times n}$. Then:

1. $P_c = \Lambda$; in particular $P_c$ does not depend on the choice of $D$.
2. **Projection commutes with propagation:** for every row vector $\rho \in \mathbb{R}^{1 \times N}$ and every integer $t \ge 0$,

$$(\rho P^{t})\, \chi = (\rho\, \chi)\, P_c^{\,t},$$

so propagating a cell density with $P$ and then projecting onto macrostates equals projecting first and propagating with $P_c$.
3. The spectrum of $P_c$ is the part of the spectrum of $P$ carried by the invariant subspace.
4. If in addition $\chi$ is a partition of unity, $\chi \mathbf{1}_n = \mathbf{1}_N$, then every row of $P_c$ sums to $1$. If moreover $P_c \ge 0$ entrywise, $P_c$ is the transition matrix of a Markov chain on the $n$ macrostates.

A real invariant subspace is obtained from a real Schur decomposition $P = Q R Q^{\top}$ ($Q$ orthogonal, $R$ quasi-upper-triangular) ordered so that the selected eigenvalues come first: the first $n$ Schur vectors $\tilde Q$ satisfy $P \tilde Q = \tilde Q \tilde R$, provided that a complex-conjugate pair is never split. Any $\chi = \tilde Q \mathcal{A}$ with invertible $\mathcal{A} \in \mathbb{R}^{n \times n}$ spans the same subspace.

## Proof sketch

From $P\chi = \chi\Lambda$, $\chi^{\top} D P \chi = (\chi^{\top} D \chi)\Lambda$, and $\chi^{\top} D \chi$ is invertible because $D$ is positive definite and $\chi$ has full column rank, giving item 1. Item 2 follows by induction from $P^{t}\chi = \chi \Lambda^{t}$. For item 4, $\chi \Lambda \mathbf{1}_n = P \chi \mathbf{1}_n = P \mathbf{1}_N = \mathbf{1}_N = \chi \mathbf{1}_n$, and full column rank gives $\Lambda \mathbf{1}_n = \mathbf{1}_n$. Choosing Schur vectors with real eigenvalues near $1$ captures metastable sets; choosing eigenvalues near the unit circle captures cycles. In generalized Perron cluster cluster analysis (GPCCA), the rotation $\mathcal{A}$ is chosen to make $\chi$ a nonnegative partition of unity with minimal overlap, by minimizing $n - \operatorname{tr}(\tilde D^{-1} \chi^{\top} D \chi)$ with $\tilde D$ the diagonal matrix of row sums of $\chi^{\top} D \chi$. CellRank then calls a macrostate terminal when its self-transition probability $(P_c)_{mm}$ is at least $0.96$, and initial when it receives the least mass $\chi^{\top}\pi$ of the stationary distribution $\pi$ of $P$. When the subspace is only approximately invariant, $P_c$ can have small negative entries, signalling a poor choice of $n$.

## Sources

- M. Lange, V. Bergen, M. Klein, et al., "CellRank for directed single-cell fate mapping", Nature Methods 19 (2022) 159–170, Methods sections "Generalized Perron Cluster Cluster Analysis", "Invariant subspaces of the transition matrix", "Projecting the transition matrix", "Properties of the invariant subspace projection", "Computing membership vectors" and "Determine terminal states", <https://doi.org/10.1038/s41592-021-01346-6> (PMC8828480).
- B. Reuter, K. Fackeldey, M. Weber, "Generalized Markov modeling of nonreversible molecular kinetics", Journal of Chemical Physics 150 (2019) 174103, <https://doi.org/10.1063/1.5064530>.
