# Perron-Frobenius equilibrium of the quasispecies and Crow-Kimura models

**Models.** Types $1,\dots,l$ have Wrightian fitnesses $w_i$ ($\mathbf{W} = \operatorname{diag}(w)$) and a column-stochastic mutation matrix $\mathbf{Q} = (q_{ij})$, $q_{ij}$ the probability that a type-$j$ parent produces a type-$i$ offspring. The frequency vector $\mathbf{p}$ on the simplex $S_l$ follows one of

$$\mathbf{p}(t+1) = \frac{\mathbf{QW}\,\mathbf{p}(t)}{\bar w(t)} \quad\text{(discrete quasispecies)}, \qquad \dot{\mathbf{p}} = \mathbf{QW}\mathbf{p} - \bar w\,\mathbf{p} \quad\text{(Eigen)},$$

$$\dot{\mathbf{p}} = \bigl(\mathbf{M} - \bar m(t)\mathbf{E}\bigr)\mathbf{p} + \boldsymbol{\mathcal{M}}\mathbf{p} \quad\text{(Crow-Kimura)},$$

where $\mathbf{M} = \operatorname{diag}(m)$ holds Malthusian fitnesses, $\boldsymbol{\mathcal{M}}$ is a mutation generator (non-negative off-diagonal rates, zero column sums), and $\bar w = (\mathbf{w},\mathbf{p})$, $\bar m = (\mathbf{m},\mathbf{p})$ are mean fitnesses.

**Theorem.** If $\mathbf{QW}$ and $\mathbf{M} + \boldsymbol{\mathcal{M}}$ are primitive (the latter after adding a common constant to the diagonal), each model has a unique strictly positive equilibrium $\hat{\mathbf{p}} \in S_l$, globally stable on $S_l$. It is the normalized Perron eigenvector of $\mathbf{QW}$, respectively $\mathbf{M} + \boldsymbol{\mathcal{M}}$, and the equilibrium mean fitness equals the dominant eigenvalue.

**Permutation-invariant landscape.** For binary sequences of length $N$ whose fitness $m_k$ depends only on the Hamming class $k$, and per-site mutation rate $\mu$, the Crow-Kimura problem reduces to $(\mathbf{M} + \mathbf{Q}_N)\mathbf{p} = \bar m\,\mathbf{p}$ with the tridiagonal $\mathbf{Q}_N$ (entries $(N-j)\mu$ above, $j\mu$ below, $-N\mu$ on the diagonal, in the class index). Its equilibrium and mean fitness satisfy

$$\lim_{\mu\to\infty}\mathbf{p}(\mu) = 2^{-N}\Bigl(\tbinom{N}{0},\tbinom{N}{1},\dots,\tbinom{N}{N}\Bigr), \qquad \lim_{\mu\to\infty}\bar m(\mu) = 2^{-N}\sum_{k=0}^N\tbinom{N}{k}m_k ,$$

and for a simple eigenvalue $\bar m'(\mu) = -2(\mathbf{D}_N\mathbf{x}(\mu),\mathbf{y}(\mu))$ in terms of normalized right and left eigenvectors of the symmetrized problem.

## Depends on

- [Master-sequence vector field of the single-peak quasispecies](master-field.md)

## Expansion

The un-normalized counts obey a linear system, $\mathbf{n}(t) = (\mathbf{QW})^t\mathbf{n}(0)$ or $\mathbf{n}(t) = e^{t(\mathbf{M}+\boldsymbol{\mathcal{M}})}\mathbf{n}(0)$, and the frequency dynamics is its projectivization. Primitivity gives a simple dominant eigenvalue with a positive eigenvector and $\lambda^{-t}\mathbf{A}^t \to \mathbf{v}\mathbf{w}^\top$, so every positive initial frequency converges to $\hat{\mathbf{p}}$. In the infinite-mutation limit selection is negligible and the equilibrium becomes the uniform distribution over the $2^N$ sequences, grouped into binomial Hamming classes; the single-peak error threshold describes how fast the master class loses its share as $\mu$ grows.

## Sources

- A. S. Bratus, S. Drozhzhin, T. Yakushkina, "Mathematical Models of Evolution and Replicator Systems Dynamics" (2026), Chapter 1: quasispecies equations, theorem on global stability of the quasispecies equilibrium, and the permutation-invariant Crow-Kimura limit theorem and corollary, <https://doi.org/10.48550/arXiv.2604.05720>.
