# Generic identifiability of large-cycle K2P and K3P network models

**Networks.** A phylogenetic network on $[n]$ is a rooted acyclic digraph without parallel edges whose root has out-degree two, whose leaves are $[n]$, and whose other vertices have in/out-degree $(1,2)$ or $(2,1)$. A *$k$-cycle network* is a semi-directed network with a single reticulation vertex lying on a cycle of length $k$, obtained by attaching binary trees to the vertices of a $k$-cycle; *large-cycle networks* are the $k$-cycle networks with $k\ge4$. Under a group-based model, the network model $V_N$ is the Zariski closure of the image of $\psi_N = \lambda\psi_{T_1} + (1-\lambda)\psi_{T_2}$, $\lambda \in [0,1]$, where $T_1, T_2$ are obtained by deleting either reticulation edge and each $\psi_{T_i}$ uses the edge parameters $T_i$ inherits from $N$ (shared edges carry the same parameters). Unlike the 2-tree mixture model, the parameters of the two trees are not independent.

**Theorem.** For the Kimura 2-parameter (K2P) and Kimura 3-parameter (K3P) models, the semi-directed network parameter of large-cycle network models is generically identifiable: for distinct $n$-leaf large-cycle networks $N_1,N_2$,

$$\dim(V_{N_1}\cap V_{N_2})<\min(\dim V_{N_1},\dim V_{N_2}).$$

The key steps are: for a $k_1$-cycle network $N_1$ and a $k_2$-cycle network $N_2$ with $2\le k_1<k_2\le4$, $V_{N_2}\not\subseteq V_{N_1}$; distinct 4-leaf 4-cycle networks have mutually non-contained varieties; and each 5-leaf 4-cycle network variety is not contained in the 5-leaf 5-cycle (sunlet) variety.

## Depends on

- [Coordinate projection matroid certificate of generic identifiability](coordinate-projection-matroid-certificate-of-generic-identifiability.md)

## Expansion

The small-network non-containments are certified by coordinate sets that are independent in the matroid of one network variety but dependent in the other, computed from Jacobians of the Fourier parametrizations. These are exactly the base cases of the reduction of Gross and Long, who proved identifiability of large-cycle networks under the Jukes–Cantor model: their reduction lemmas carry over to K2P and K3P once the base cases hold, giving $V_{N_1}\not\subseteq V_{N_2}$ and $V_{N_2}\not\subseteq V_{N_1}$ for any two distinct large-cycle networks, and mutual non-containment of irreducible varieties gives the dimension inequality. The same computations also separate 3-cycle from 4-cycle networks, while trees can never be generically identified from cycle networks.

## Sources

- B. Hollering, S. Sullivant, "Identifiability in phylogenetics using algebraic matroids", arXiv:1909.13754 (2019), <https://doi.org/10.48550/arXiv.1909.13754>. Section 5 (Definitions 5.1, 5.2, 5.5, 5.6; Lemmas 5.7–5.9; Corollary 5.10; Remark 1).
