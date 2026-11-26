# Multispecies witness filtration

Let $P = P_0 \cup P_1 \cup \dots \cup P_m \subset \mathbb{R}^2$ be a labeled point cloud of $m + 1$ disjoint species (cell types), and let $\mathcal{D}_0$ be the Delaunay triangulation of the landmark species $P_0$, viewed as a simplicial complex with all faces. A point $p \in P_i$ is a **$P_i$-witness** of a simplex $\sigma = \{l_0, \dots, l_k\} \in \mathcal{D}_0$ if $d(p, l_j) \le d(p, l)$ for every vertex $l_j$ of $\sigma$ and every landmark $l \in P_0 \setminus \sigma$, that is, the vertices of $\sigma$ are among the nearest landmarks of $p$. Let $\mu^{\sigma}$ be the number of $P_i$-witnesses of $\sigma$ and $\mu_{\max} = \max_{\sigma \in \mathcal{D}_0} \mu^{\sigma}$, and set

$$\tilde\mu^{\sigma} = \frac{\mu_{\max} - \mu^{\sigma}}{\mu_{\max}} \in [0, 1].$$

The **multispecies witness filtration** $W^{\bullet}_{0,i}$ is the family of complexes $W^{\mu}_{0,i}$, $\mu \in [0, 1]$, containing every $\sigma \in \mathcal{D}_0$ with $\tilde\mu^{\sigma} \le \mu$ together with all its faces. Equivalently, a simplex $\tau$ enters at $\min\{\tilde\mu^{\sigma} : \tau \subseteq \sigma \in \mathcal{D}_0\}$, which makes $W^{\bullet}_{0,i}$ a valid filtration of $\mathcal{D}_0$ even when a face has fewer witnesses than a simplex containing it.

**Relational features.** For each pair $i < j$ in $\{1, \dots, m\}$, compare the diagrams $\mathrm{pd}_k(W^{\bullet}_{0,i})$ and $\mathrm{pd}_k(W^{\bullet}_{0,j})$, $k \in \{0, 1\}$, by the bottleneck distance and the 1-Wasserstein distance; this yields a feature vector with $2 \cdot 2 \cdot \binom{m}{2} = 2m(m-1)$ entries describing how differently the other species are arranged relative to $P_0$.

## Depends on

- [Dowker persistence of two cell populations](dowker-persistence-of-two-cell-populations.md)

## Expansion

The construction adapts lazy witness complexes, which approximate an intrinsic Delaunay triangulation of the landmarks, by fixing the triangulation of one species and letting each other species reweight it: regions of the $P_0$ tissue densely witnessed by species $i$ enter early. All filtrations live on the same complex, so differences between their diagrams isolate differences in how species are distributed relative to the landmarks rather than differences in the landmark geometry. The reason for defining entry values through cofaces is that a filtration requires every face of an included simplex to be present; using only the top-dimensional values $\tilde\mu^{\sigma}$ for every simplex would violate this. In agent-based tumor simulations, these distance vectors separated qualitatively different parameter regimes of the model.

## Sources

- B. J. Stolz, J. Dhesi, J. A. Bull, H. A. Harrington, H. M. Byrne, I. H. R. Yoon, "Relational Persistent Homology for Multispecies Data with Application to the Tumor Microenvironment", Bulletin of Mathematical Biology (2024), Section 3 (Definitions 1-3, Theorem 1), Section 4 (Definition 4, Theorem 2, Dowker filtration construction; Definitions 5-6, multispecies witness filtration), Section 5 (tumor microenvironment applications). <https://doi.org/10.1007/s11538-024-01353-6> (PMC11408586)
