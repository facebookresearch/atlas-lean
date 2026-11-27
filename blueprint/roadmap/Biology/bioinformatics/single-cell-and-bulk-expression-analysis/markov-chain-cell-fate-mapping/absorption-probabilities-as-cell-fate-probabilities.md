# Absorption probabilities as cell-fate probabilities

Let a finite Markov chain on cells have its states split into a set $\mathcal{R}$ made absorbing (all outgoing transitions of terminal-state cells removed) and a transient set $\mathcal{T}$, with transition matrix in block form

$$P = \begin{pmatrix} \tilde P & 0 \\ S & Q \end{pmatrix},$$

where $Q$ is the restriction to $\mathcal{T}$ and $S$ holds transitions from $\mathcal{T}$ to $\mathcal{R}$. Assume every transient state reaches $\mathcal{R}$ with positive probability; on a finite chain this is the same as almost sure absorption from every state, the hypothesis of the [absorption probabilities of a finite Markov chain](../../../../Probability/markov-chains/finite-markov-chains/absorption-probabilities-and-mean-absorption-tim.md).

**Theorem.** $I - Q$ is invertible, and for the fundamental matrix $M = (I - Q)^{-1}$:

1. $M_{ij}$ is the expected number of visits to $j \in \mathcal{T}$ before absorption, starting from $i \in \mathcal{T}$;
2. $B = MS$ has entries $B_{ir} = \Pr(\text{the first state of } \mathcal{R} \text{ reached is } r \mid X_0 = i)$, and each row of $B$ sums to $1$.

**Fate probabilities.** If $\mathcal{R}$ is partitioned into terminal index sets $R_1, \dots, R_{n_t}$, the fate probability of transient cell $i$ towards terminal state $t$ is

$$F_{it} = \sum_{r \in R_t} B_{ir}, \qquad F_{it} \ge 0, \quad \sum_{t=1}^{n_t} F_{it} = 1,$$

the probability that the chain started at $i$ is first absorbed in $R_t$. The column $F_{\cdot t}$ restricted to $\mathcal{T}$ is the absorption probability into $B = R_t$ of the finite-chain theorem, whose characterization $h = Ph$ off $\mathcal{R}$, $h = \mathbf{1}_{R_t}$ on $\mathcal{R}$ reads $(I - Q)\, F_{\cdot t} = S\, \mathbf{1}_{R_t}$ in block form; this page adds the fundamental-matrix expression and the reading of the absorption probabilities as cell fates.

## Depends on

- [Velocity-directed cell transition matrix](velocity-directed-cell-transition-matrix.md)

## Proof depends on

- [Absorption probabilities and mean times of a finite Markov chain](../../../../Probability/markov-chains/finite-markov-chains/absorption-probabilities-and-mean-absorption-tim.md)

## Proof sketch

Because every transient state reaches $\mathcal{R}$, $Q^{t} \to 0$, so the spectral radius of $Q$ is below $1$ and $M = \sum_{t \ge 0} Q^{t}$ converges; its $(i, j)$ entry sums the probabilities of being at $j$ at each step. A first-step decomposition gives $B = S + QB$, i.e. $(I - Q)B = S$, which is the block form of the finite-chain characterization applied to each singleton $\{r\}$, and $B\mathbf{1} = M S \mathbf{1} = M (I - Q)\mathbf{1} = \mathbf{1}$ since rows of $P$ sum to one. On a velocity-directed chain over a connected neighbour graph, every cell reaches every terminal set, so the hypothesis holds. CellRank takes, for each terminal macrostate, the cells with the largest membership in that macrostate as $R_t$, solves the sparse systems iteratively rather than inverting $I - Q$, and summarizes a cell's commitment by the entropy of its fate vector $F_{i\cdot}$ or by its Kullback–Leibler divergence from the average fate vector.

## Sources

- M. Lange, V. Bergen, M. Klein, et al., "CellRank for directed single-cell fate mapping", Nature Methods 19 (2022) 159–170, Methods, "Absorption probabilities disclose cell fates", "Computing absorption probabilities", Theorem 1 and "Quantifying multilineage potential through fate probabilities", <https://doi.org/10.1038/s41592-021-01346-6> (PMC8828480).
