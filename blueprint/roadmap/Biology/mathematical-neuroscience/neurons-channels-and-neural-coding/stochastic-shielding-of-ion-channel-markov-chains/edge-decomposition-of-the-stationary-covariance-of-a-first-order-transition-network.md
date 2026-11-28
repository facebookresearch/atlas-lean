# Edge decomposition of the stationary covariance of a first-order transition network

Let $N_{\mathrm{tot}}$ individuals (for example ion channels) move independently among $n$ states along $m$ directed edges $k : i(k) \to j(k)$ with per-capita rates $\alpha_k > 0$. Let $\zeta_k = e_{j(k)} - e_{i(k)}$ be the stoichiometry vector of edge $k$, $L = Q^{\top}$ the transposed generator ($L_{ij} \geq 0$ for $i \neq j$, columns summing to zero, $Lx = \sum_k \zeta_k \alpha_k x_{i(k)}$), $\pi$ the stationary distribution, $J_k = N_{\mathrm{tot}}\alpha_k\pi_{i(k)}$ the stationary flux of edge $k$, and $B_k$ the $n \times m$ matrix whose $k$-th column is $\sqrt{J_k}\,\zeta_k$ and whose other columns vanish, $B = \sum_k B_k$. The linear (Langevin, Ornstein–Uhlenbeck) approximation of the occupancy fluctuations is $dX = LX\,dt + \sum_k B_k\,dW$ with independent Brownian motions, one per edge.

Let $\mathcal{Y}$ be the set of real symmetric $n \times n$ matrices whose columns sum to zero.

**Lemma.** If $L$ has nonnegative off-diagonal entries, zero column sums, $\dim\ker L = 1$, and a nonnegative null vector, then for every $F \in \mathcal{Y}$ the Lyapunov equation $LC + CL^{\top} = F$ has a unique solution $C \in \mathcal{Y}$.

**Theorem.** For an irreducible network satisfying detailed balance (so $L$ has real eigenvalues and a biorthogonal eigenbasis), the stationary covariance $C$ of $X$ is the unique solution in $\mathcal{Y}$ of $LC + CL^{\top} = -BB^{\top}$, and it decomposes uniquely and linearly over edges:

$$C = \sum_{k=1}^m C_k, \qquad C_k = \int_0^\infty e^{tL} B_k B_k^{\top} \bigl(e^{tL}\bigr)^{\top}\,dt .$$

For a measurement vector $M$ (for example the indicator of conducting states), the **edge importance** of edge $k$ is its contribution $M^{\top} C_k M$ to the stationary variance of the observable $M^{\top}X$. The decomposition is exact for every irreducible first-order network, whatever its timescale separation or node occupancies.

## Expansion

The map $\mathcal{A}(C) = LC + CL^{\top}$ sends $\mathcal{Y}$ into $\mathcal{Y}$ because $\sum_i (LC + CL^{\top})_{ij} = \sum_k C_{kj}\sum_i L_{ik} + \sum_k L_{jk}\sum_i C_{ik} = 0$. All nonzero eigenvalues of $L$ have negative real part, and the only null direction is the stationary vector, whose left counterpart (the all-ones vector) annihilates every $\zeta_k$; the Fredholm alternative then gives existence and uniqueness on $\mathcal{Y}$. Since $BB^{\top} = \sum_k B_k B_k^{\top}$ and each $B_k B_k^{\top} \in \mathcal{Y}$, linearity splits the solution into one Lyapunov solution per edge, and each integral converges because $\mathbf{1}^{\top}\zeta_k = 0$ removes the zero mode. Ranking the edges by $M^{\top}C_kM$ tells which noise sources can be dropped with least effect on the observed variance.

## Sources

- D. R. Schmidt, R. F. Galán, P. J. Thomas, "Stochastic shielding and edge importance for Markov chains with timescale separation", *PLoS Computational Biology* 14(6) (2018) e1006206. Results, "Edge importance and decomposition of the stationary observed variance": Definition 1, Lemma 1 (Eq. 27), Theorem 1 (Eqs. 28–31); Methods, "Notation" (Eqs. 32–36) and "Proof of Lemma 1" (Eq. 47). <https://doi.org/10.1371/journal.pcbi.1006206>. PMCID: PMC6023243.
