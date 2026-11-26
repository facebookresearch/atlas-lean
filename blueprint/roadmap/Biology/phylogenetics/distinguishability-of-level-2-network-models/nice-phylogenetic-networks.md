# Nice phylogenetic networks

Let $N$ be an $n$-leaf semi-directed phylogenetic network on leaf set $X$, with $r$ reticulation vertices. For each reticulation vertex choose one of its two incoming reticulation edges to delete; the $2^r$ choices form a set $B_r$, and each $\sigma\in B_r$ yields a displayed tree $T_\sigma$ after suppressing degree-two vertices and deleting unlabelled pendant parts. $N$ is **nice** if for every $\sigma\in B_r$ the leaf set of $T_\sigma$ is exactly $X$.

A non-leaf vertex $v$ is a **funnel** of type $A$ if it is a child of two reticulation vertices and a parent of a reticulation vertex, and of type $B$ if it is a parent of two reticulation vertices. A network is **funnel-free** if it has no funnel.

**Facts.**
1. Every level-1 network is funnel-free (two reticulation vertices sharing a funnel would create two cycles through a common edge, contradicting level-1).
2. For a nice network evolving under a group-based Markov model (Jukes–Cantor JC, Kimura 2-parameter K2P, Kimura 3-parameter K3P) with reticulation parameters, the leaf distribution is a mixture over $\sigma\in B_r$ of tree distributions on the full leaf set $X$, so the discrete Fourier transform turns the parametrization into a monomial map in the Fourier coordinates and the network variety $V_N$ is a sum of toric varieties whose invariants can be computed.

## Expansion

Fourier coordinates of a group-based tree model factor as a product of edge parameters over the splits of the tree, but only if every displayed tree has the full leaf set; a displayed tree missing a leaf breaks this product form. Niceness is exactly the condition that keeps every mixture component a tree on $X$. Funnels are the local configurations in level-2 networks that can cut off a leaf in some displayed tree, which is why they are singled out.

## Sources

- M. Ardiyansyah, "Distinguishing Level-2 Phylogenetic Networks Using Phylogenetic Invariants", arXiv:2104.12479 (2021), Sections 3.1–3.2 (group-based models, Fourier transform), Definition 3.6 and Section 3.4 (nice and funnel-free networks), <https://doi.org/10.48550/arXiv.2104.12479>.
