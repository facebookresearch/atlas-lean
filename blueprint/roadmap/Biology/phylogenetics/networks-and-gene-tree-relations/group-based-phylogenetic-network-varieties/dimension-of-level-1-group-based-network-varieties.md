# Dimension of level-1 group-based network varieties

**Group-based models.** Fix a finite abelian group $G$ (states, e.g. $G = \mathbb{Z}/2 \times \mathbb{Z}/2$ for nucleotides) and a subgroup $B \le \mathrm{Aut}(G)$. In a group-based model the transition probability from state $a$ to state $b$ on an edge depends only on $b - a$, and parameters are identified along $B$-orbits of $G$; if $G$ has $l + 1$ orbits under $B$, each edge carries $l$ free parameters. The Jukes–Cantor, Kimura 2-parameter and Kimura 3-parameter models are of this form, and the Cavender–Farris–Neyman (CFN) model is the case $G = \mathbb{Z}/2$.

**Network model.** A level-1 phylogenetic network $N$ (cycles are vertex-disjoint) with $m$ edges and $c$ cycles carries one group-based transition matrix per edge and one mixing parameter per cycle; the leaf distribution is the mixture, over the trees displayed by $N$, of the tree models. The Zariski closure of the image of the parameterization is the **network variety** $V_N(G,B)$. Counting parameters gives the expected dimension $l(m - c) + 1$, which is always an upper bound.

**Theorem.** Let $N$ be a level-1 triangle-free phylogenetic network with $m$ edges and $c$ cycles, $G$ a finite abelian group with $|G| \ge 3$, $B \le \mathrm{Aut}(G)$, and $l + 1$ the number of $B$-orbits. Then

$$\dim V_N(G,B) = l(m - c) + 1.$$

**Theorem (CFN model).** Let $G = \mathbb{Z}/2$ and let $N$ be a level-1 network with $m$ edges, $c_{\ge 5}$ cycles of length at least 5, $c_4$ 4-cycles and $c_3$ 3-cycles. Then

$$\dim V_N(G) = m - (c_{\ge 5} + 2c_4 + 3c_3) + 1.$$

## Expansion

After the discrete Fourier transform on $G$, tree varieties of group-based models become toric, and cutting a tree at an internal edge corresponds to a toric fiber product of ideals. Network varieties are not toric, but the fiber-product decomposition still applies along cut edges, so the computation reduces to sunlet networks (a single cycle with one leaf hanging from each cycle vertex). The paper proves a general dimension formula for codimension-zero toric fiber products, $\dim(I \times_{\mathcal{A}} J) = \dim I + \dim J - |\mathcal{A}|$ for prime ideals under a maximal-independence condition on initial ideals, and computes sunlet dimensions with tropical lower bounds (rank of the parameterization's Jacobian at tropical points). Contracting 2-cycles and pendant structure does not change the variety. Knowing that different networks give varieties of the expected dimension, and that the varieties are distinct, is the input to generic identifiability of network topology from site-pattern distributions.

## Sources

- E. Gross, R. Krone, S. Martin, "Dimensions of level-1 group-based phylogenetic networks", Bulletin of Mathematical Biology (2024), Introduction (expected dimension $l(m-c)+1$, Theorems 1 and 2), Section 2 (Lemmas 3–6) and Section 3 (Theorem 9 on toric fiber products), <https://doi.org/10.1007/s11538-024-01314-z>, PMCID PMC11182832.
