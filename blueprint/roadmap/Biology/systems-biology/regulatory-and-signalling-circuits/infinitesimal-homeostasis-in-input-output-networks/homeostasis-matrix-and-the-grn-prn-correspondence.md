# Homeostasis matrix and the GRN–PRN correspondence

**Setting.** An input-output network $\mathcal G$ has nodes $\iota,\rho_1,\dots,\rho_{n-1},o$ (input, regulatory, output) and an admissible system $\dot x=f(x,\mathcal I)$ in which the input parameter $\mathcal I$ appears only in $f_\iota$, and $f_j$ depends on $x_k$ only if $k\to j$ is an edge or $k=j$. Suppose $X(\mathcal I)$ is a family of linearly stable equilibria, so the input-output function $o(\mathcal I)=X_o(\mathcal I)$ is smooth. $\mathcal I_0$ is a point of infinitesimal homeostasis if $o'(\mathcal I_0)=0$.

**Homeostasis matrix.** Delete from the Jacobian $J=(f_{j,k})$ (with $f_{j,k}=\partial f_j/\partial x_k$) the row of $\iota$ and the column of $o$; the result is the $n\times n$ homeostasis matrix $H$. By Cramer's rule,

$$\mathcal I_0\ \text{is a point of infinitesimal homeostasis}\iff \det H=0\ \text{at}\ (X(\mathcal I_0),\mathcal I_0).$$

By Frobenius–König theory there are permutation matrices $P,Q$ with $PHQ$ block upper-triangular with unique irreducible square diagonal blocks $B_1,\dots,B_m$, so $\det H=\prod_\eta\det B_\eta$ and each factor defines a homeostasis type. A block of size $k$ has $k$ or $k-1$ self-coupling entries $f_{j,j}$: the first gives appendage homeostasis (a subnetwork off every simple path from $\iota$ to $o$), the second structural homeostasis (a subnetwork between consecutive super-simple nodes, nodes lying on every simple $\iota\to o$ path).

**GRN–PRN correspondence.** In a gene regulatory network (GRN) each gene $\tau$ carries an mRNA and a protein concentration. The associated protein-mRNA network (PRN) $\mathcal R$ replaces $\tau$ by two nodes $\tau^R\to\tau^P$ and a regulation $\sigma\to\tau$ by $\sigma^P\to\tau^R$, giving a bipartite input-output network. Then:

- The homeostasis subnetworks of $\mathcal G$ and $\mathcal R$ correspond one-to-one, except that (a) each super-simple node $\rho$ of $\mathcal G$ corresponds to an extra $\mathcal R$-Haldane subnetwork $\{\rho^R\to\rho^P\}$, and (b) each single appendage node $\tau$ of $\mathcal G$ yields two appendage subnetworks $\{\tau^R\}$ and $\{\tau^P\}$ of $\mathcal R$ (null-degradation types).
- The homeostasis patterns of $\mathcal G$ (which nodes are simultaneously homeostatic) correspond exactly to the GRN-generating homeostasis patterns of $\mathcal R$; patterns of $\mathcal R$ triggered by Haldane or protein null-degradation subnetworks have no GRN counterpart.
- If the PRN is infinitesimally homeostatic at the output mRNA $o^R$, it is also homeostatic at the output protein $o^P$.

## Expansion

Differentiating $f(X(\mathcal I),\mathcal I)=0$ gives $J\,X'=-\partial_{\mathcal I}f=-f_{\iota,\mathcal I}e_\iota$, and Cramer's rule yields $o'=\pm f_{\iota,\mathcal I}\det H/\det J$ with $f_{\iota,\mathcal I}\ne0$ and $\det J\ne0$ at a stable equilibrium. Because the entries of $H$ are generic in the admissible class, the block decomposition of $H$ is determined by the graph alone, which is why homeostasis types are combinatorial. In the PRN, the extra Haldane factor is the linear coupling $f_{\rho^P,\rho^R}$ (translation rate), which a GRN model with one variable per gene cannot make vanish separately.

## Sources

- F. Antoneli, M. Golubitsky, J. Jin, I. Stewart, "Homeostasis in Gene Regulatory Networks", *International Journal of Biomathematics* (2025), 2550070, Section 2 (homeostasis matrix lemma, GRN–PRN subnetwork and pattern correspondence theorems), Appendices A–C, <https://doi.org/10.1142/s1793524525500706> (preprint arXiv:2309.06509).
