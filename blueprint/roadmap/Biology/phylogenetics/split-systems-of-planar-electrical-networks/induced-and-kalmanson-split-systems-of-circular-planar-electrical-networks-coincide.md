# Induced and Kalmanson split systems of circular planar electrical networks coincide

**Setting.** A circular planar electrical network $N$ is a connected planar graph with positive edge conductances, embedded in a disk with $n$ boundary nodes labelled $1, \dots, n$ in circular order. Its resistance matrix $W(N)$ records effective resistances between boundary nodes; it is a Kalmanson metric for this circular order, hence equals the split metric $W_{ij} = \sum_{S \text{ separates } i, j} w(S)$ of a unique weighted circular split system, the *Kalmanson split system* $\mathcal R(N)$. Separately, a *grove* of $N$ is a spanning forest each of whose trees contains a boundary node; a 2-grove *respects* a split $A \mid B$ displayed by $N$ if its two trees span $A$ and $B$. The *induced split system* $\Sigma(N)$ assigns to each split displayed by $N$ the weight

$$w(A \mid B) = \frac{\sum_{\text{2-groves } F \text{ respecting } A \mid B} \prod_{e \in F} c_e}{\sum_{\text{spanning trees } T} \prod_{e \in T} c_e}.$$

**Theorem.**
1. For every connected circular planar electrical network $N$, $\mathcal R(N) = \Sigma(N)$: the splits displayed by the network, weighted by normalized 2-grove counts, are exactly the circular splits whose metric is the effective resistance.
2. With $N^*$ the planar dual network and $\mathcal X$ the graphical map that reads a split system off the network's edges via Kron reduction, $\mathcal X(N) = \mathcal R(N^*) = \Sigma(N^*)$ and $\mathcal X'(N^*) = \mathcal R(N) = \Sigma(N)$. Both identities extend to cactus networks (circular planar networks allowed to be disconnected, obtained by contracting boundary nodes).

## Expansion

By the matrix-tree theorem for groves (Kirchhoff, Kenyon–Wilson), the effective resistance between $i$ and $j$ equals the weighted count of 2-groves separating $i$ from $j$ divided by the spanning-tree count. Grouping 2-groves by the split they induce writes $W_{ij}$ as a sum of split weights over the splits separating $i$ and $j$, so $\Sigma(N)$ realizes the resistance metric; planarity makes these splits circular, and uniqueness of the circular split decomposition of a Kalmanson metric forces $\Sigma(N) = \mathcal R(N)$. This links phylogenetic split networks (NeighborNet-type circular split systems) to the compactified space of circular planar electrical networks.

## Sources

- S. L. Devadoss and S. Forcey, "Compactifications of phylogenetic systems and species of electrical networks", arXiv:2408.03431 (2024), Theorems 8, 11, 13 and 16, <https://doi.org/10.48550/arXiv.2408.03431>.
