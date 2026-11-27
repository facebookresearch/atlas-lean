# Velocity-directed cell transition matrix

Let $N$ cells have expression profiles $x_i \in \mathbb{R}^{G}$ and RNA velocity vectors $v_i \in \mathbb{R}^{G}$, and let $\mathcal{G}$ be a symmetric $k$-nearest-neighbour graph on the cells with adjacency matrix $A \ge 0$ and neighbour sets $\mathcal{N}(i) = \{j : A_{ij} > 0\}$, each nonempty. Assume that $v_i$ and every state-change vector $x_j - x_i$, $j \in \mathcal{N}(i)$, are nonconstant vectors (not all coordinates equal), so that the Pearson correlation $c_{ij}$ between $v_i$ and $x_j - x_i$ is defined. For $\sigma > 0$ define

$$(P_v)_{ij} = \frac{e^{\sigma c_{ij}}}{\sum_{l \in \mathcal{N}(i)} e^{\sigma c_{il}}} \quad (j \in \mathcal{N}(i)), \qquad (P_v)_{ij} = 0 \text{ otherwise},$$

let $P_s$ be the row-normalized adjacency, $(P_s)_{ij} = A_{ij} / \sum_l A_{il}$, and for $\lambda \in [0, 1]$ set

$$P = (1 - \lambda)\, P_v + \lambda\, P_s .$$

Properties:

1. $P$ is row-stochastic and its support is exactly the edge set of $\mathcal{G}$: $P_{ij} > 0 \iff j \in \mathcal{N}(i)$.
2. Consequently the Markov chain with transition matrix $P$ is irreducible if and only if $\mathcal{G}$ is connected; when $\mathcal{G}$ has several connected components, each component is a closed communicating class.
3. If $|\mathcal{N}(i)| \ge 2$, then within $\mathcal{N}(i)$, $(P_v)_{ij}$ is strictly increasing in $c_{ij}$ with the other correlations held fixed; if $\mathcal{N}(i) = \{j\}$ is a single neighbour, $(P_v)_{ij} = 1$ whatever $c_{ij}$ is. As $\sigma \to \infty$ it concentrates on the neighbours of maximal correlation, while $\sigma \to 0$ gives the uniform distribution on $\mathcal{N}(i)$.

## Remarks

Each softmax row is a probability vector with strictly positive entries on $\mathcal{N}(i)$, and $P_s$ has the same support, so any convex combination of the two keeps that support; irreducibility of a finite chain depends only on the directed support graph, which here is the undirected graph $\mathcal{G}$ read in both directions. Transitions against the velocity therefore keep small positive probability, which is what makes the chain irreducible on a connected graph. The correlation $c_{ij}$ is the cosine of the angle between the mean-centred velocity and the mean-centred displacement. In CellRank the inverse temperature defaults to $\sigma = 1/\operatorname{median}\{|c_{ij}|\}$, and $\lambda \approx 0.2$ mixes in transcriptomic similarity for robustness to noisy velocities; uncertainty in $v_i$ can additionally be propagated by averaging the softmax over a distribution of velocity vectors.

## Sources

- M. Lange, V. Bergen, M. Klein, et al., "CellRank for directed single-cell fate mapping", Nature Methods 19 (2022) 159–170, Methods sections "Directing the KNN graph based on RNA velocity", "Transforming correlations into transition probabilities", "Automatically determine σ", "Emphasizing transcriptomic similarity" and "Handling reducible Markov chains", <https://doi.org/10.1038/s41592-021-01346-6> (PMC8828480).
