# Product theorem for independent regulatory modules

**Construction.** Let $G$ and $H$ be labelled directed graphs (microstate graphs of two regulatory modules, for example two enhancers), not necessarily strongly connected or at equilibrium. The *product graph* $G \times H$ has vertices $(i, j)$ with $i \in G$, $j \in H$; for every edge $i_1 \xrightarrow{a} i_2$ of $G$ and every vertex $j$ of $H$ it has the edge $(i_1, j) \xrightarrow{a} (i_2, j)$, and for every edge $j_1 \xrightarrow{b} j_2$ of $H$ and every vertex $i$ of $G$ it has the edge $(i, j_1) \xrightarrow{b} (i, j_2)$; there are no other edges. Equal labels encode independence: each module's transitions occur at rates unaffected by the other module's state.

**Theorem.** If $G$ and $H$ are strongly connected, then so is $G \times H$, and a basis vector of $\ker \mathcal L(G \times H)$ is the Kronecker product

$$\rho^{G \times H} = \rho^{G} \otimes \rho^{H}, \qquad (\rho^G \otimes \rho^H)_{(i,j)} = \rho^G_i\, \rho^H_j .$$

In general, if $\rho^{G,1}, \dots, \rho^{G,s}$ and $\rho^{H,1}, \dots, \rho^{H,r}$ are the terminal-component bases of $\ker \mathcal L(G)$ and $\ker \mathcal L(H)$, then the products $\rho^{G,k} \otimes \rho^{H,l}$ form a basis of $\ker \mathcal L(G \times H)$. Consequently steady-state microstate probabilities of independent modules factorize, $u^*_{(i,j)} = u^{*,G}_i\, u^{*,H}_j$, even far from equilibrium.

## Depends on

- [Laplacian dynamics and matrix-tree steady states of regulatory microstates](laplacian-dynamics-and-matrix-tree-steady-states-of-regulatory-microstates.md)

## Expansion

With lexicographic ordering of vertices, $\mathcal L(G \times H) = \mathcal L(G) \otimes I + I \otimes \mathcal L(H)$ (the Kronecker sum), so $\mathcal L(G \times H)(x \otimes y) = (\mathcal L(G) x) \otimes y + x \otimes (\mathcal L(H) y)$ vanishes whenever $x \in \ker \mathcal L(G)$ and $y \in \ker \mathcal L(H)$. Dimension counting of terminal components (the terminal components of $G \times H$ are products of terminal components) shows these products span the kernel. The practical gain is algebraic: for two strongly connected modules with $n$ and $m$ vertices, the matrix-tree formula on $G \times H$ gives polynomials of degree $nm - 1$ in the labels that share a large common factor, whereas the Kronecker formula gives degree $(n-1) + (m-1)$ directly.

## Sources

- T. Ahsendorf, F. Wong, R. Eils, J. Gunawardena, "A framework for modelling gene regulation which accommodates non-equilibrium mechanisms", BMC Biology (2014), Results, "Independence and the product theorem" (product graph construction, Eq. 14, Figure 9); full statement and proof in Additional file 1 B. <https://doi.org/10.1186/s12915-014-0102-4> (PMC4288563).
