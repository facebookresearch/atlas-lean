# Irreducibility of the bipartite host–vector contact network

**Setting.** In a multigroup vector-borne model with $n$ host groups and $n$ vector groups, let $L \in \mathbb{R}^{n\times n}_{\ge 0}$ record host infection by vectors ($L_{ij} > 0$ if vectors of group $j$ infect hosts of group $i$) and $M \in \mathbb{R}^{n\times n}_{\ge 0}$ record vector infection by hosts. The **host–vector contact network** is the directed graph of the block matrix

$$
\mathcal{M} = \begin{pmatrix} 0 & L \\ M & 0 \end{pmatrix},
$$

a bipartite graph on host nodes and vector nodes.

**Proposition.** $\mathcal{M}$ is irreducible if and only if:
1. both $LM$ and $ML$ are irreducible, and
2. $Lv \gg 0$ and $Mv \gg 0$ for some, hence every, vector $v \gg 0$, so that no row of $L$ or of $M$ vanishes.

In that case

$$
\rho(\mathcal{M})^2 = \rho(LM) = \rho(ML),
$$

and both $LM$ and $ML$ have strictly positive left and right eigenvectors for the eigenvalue $\rho(\mathcal{M})^2$.

**The two notions differ.** Irreducibility of $L$ or $M$ alone neither implies nor follows from irreducibility of $\mathcal{M}$. For

$$
C = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}, \qquad D = \begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix},
$$

$C$ is irreducible but $\begin{pmatrix} 0 & C \\ C & 0\end{pmatrix}$ is reducible (it splits into two disjoint host–vector cycles), while $D$ is reducible but $\begin{pmatrix} 0 & D^{t} \\ D & 0\end{pmatrix}$ is irreducible. So for an indirectly transmitted infection, a strongly connected movement pattern does not guarantee a strongly connected transmission structure.

## Expansion

Since $\mathcal{M}^2 = \mathrm{diag}(LM, ML)$, a path of even length in the bipartite graph between two host nodes is a path in the graph of $LM$, and similarly for vector nodes. If $\mathcal{M}$ is irreducible, every host node reaches every other host node through an even-length path, so $LM$ is irreducible, and likewise $ML$. No node can be a sink, so $L$ and $M$ have no zero rows. Conversely, conditions 1 and 2 let every host node reach some vector node and every vector node reach some host node; combined with the strong connectivity of $LM$ and $ML$ this connects all $2n$ nodes. The spectral identity holds because the eigenvalues of $\mathcal{M}$ are the square roots of those of $LM$ and $ML$. The Perron–Frobenius theorem applied to the irreducible products gives the positive eigenvectors.

## Sources

- Abderrahman Iggidr, Gauthier Sallet and Max O. Souza, "On the dynamics of a class of multi-group models for vector-borne diseases", arXiv:1409.1470 (2014), Section 2.3 (Definition 2.1, Hypothesis 2.1, Proposition 2.1 and the accompanying remarks), <https://doi.org/10.48550/arXiv.1409.1470>. Published version: Journal of Mathematical Analysis and Applications 441(2) (2016), 723–743, <https://doi.org/10.1016/j.jmaa.2016.04.003>; locators above refer to the arXiv version.
