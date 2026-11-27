# Homeostasis in networks with multiple input nodes and multiple inputs

**Multiple input nodes, one parameter.** Let $\mathcal{G}$ have input nodes $\iota_1,\dots,\iota_n$, all receiving the same external parameter $\mathcal{I}$, regulatory nodes $\rho$ and an output node $o$ downstream of every input node, with admissible system $\dot x_\iota=f_\iota(X,\mathcal{I})$, $\dot x_\rho=f_\rho(X)$, $\dot x_o=f_o(X)$ and an asymptotically stable equilibrium branch $\tilde X(\mathcal{I})$. Let $J$ be the Jacobian and let the *generalized homeostasis matrix* $\langle H\rangle$ be $J$ with its last column replaced by $(-f_{\iota,\mathcal{I}},0,0)^{\top}$. Then

$$x_o'(\mathcal{I})=\frac{\det\langle H\rangle}{\det J},\qquad \det\langle H\rangle=\sum_{m=1}^{n}\pm f_{\iota_m,\mathcal{I}}\det H_{\iota_m},$$

where $H_{\iota_m}$ deletes the last column and the $\iota_m$ row of $J$; infinitesimal homeostasis at $\mathcal{I}_0$ is equivalent to $\det\langle H\rangle=0$ (Lemma 2.17).

**Augmented network (Theorem 2.19).** Form $\mathcal{G}^\diamond$ by adding a new input node $I$ with arrows $I\to\iota_j$ for all $j$, turning the old input nodes into regulatory nodes, and extend the vector field by an equation $\dot x_I=f_I(x_I,\mathcal{I})$ forcing $x_I(t)\to\mathcal{I}$. Then the homeostasis matrix $H^\diamond$ of the single-input-node network $\mathcal{G}^\diamond$ equals $\langle H\rangle$ up to sign. Consequently the single-input-node classification into appendage and structural subnetworks applies verbatim to $\mathcal{G}^\diamond$; the unique irreducible factor containing all the terms $f_{\iota_i,\mathcal{I}}$ (input counterweight homeostasis) appears as one of the structural blocks of $\mathcal{G}^\diamond$.

**Several parameters.** With parameters $\mathcal{I}=(\mathcal{I}_1,\dots,\mathcal{I}_N)$, let $\langle H_M\rangle$ be $J$ with its last column replaced by $(-f_{\iota,\mathcal{I}_M},0,0)^{\top}$. Then

$$\nabla x_o=\frac{1}{\det J}\big(\det\langle H_1\rangle,\dots,\det\langle H_N\rangle\big),$$

and $\mathcal{I}^0$ is a point of infinitesimal homeostasis if and only if $\det\langle H_M\rangle=0$ for every $M$ (Lemma 2.20). The irreducible factors of the vector determinant $\hat h=(\det\langle H_{\mathcal{I}_1}\rangle,\dots,\det\langle H_{\mathcal{I}_N}\rangle)$ are exactly the irreducible factors of $\nabla x_o$ that can induce homeostasis (Theorem 2.24). A block common to all components (a scalar factor of $\hat h$) is *pleiotropic*: its vanishing alone gives homeostasis with respect to every parameter. The remaining blocks are *coincidental*: homeostasis requires an $N$-tuple of them, one per parameter, to vanish simultaneously.

## Depends on

- [Determinant criterion for infinitesimal homeostasis](determinant-criterion-for-infinitesimal-homeostasis.md)
- [Appendage and structural homeostasis subnetworks](appendage-and-structural-homeostasis-subnetworks.md)

## Expansion

All three formulas are Cramer's rule applied to $J\,\partial_{\mathcal{I}_M}\tilde X=-\partial_{\mathcal{I}_M}F$, whose right-hand side is supported on the input rows. In the augmented network the variable $x_I$ tracks $\mathcal{I}$, so the derivatives $f_{\iota_j,x_I}$ play the role of $f_{\iota_j,\mathcal{I}}$; deleting the $I$ row and the $o$ column of the Jacobian of $\mathcal{G}^\diamond$ leaves precisely the columns of $\langle H\rangle$, which is the content of the theorem. The practical point is that a multi-input-node network can be fed to the single-input classification algorithm after adding one node, instead of being decomposed into a family of single-input subnetworks.

## Sources

- Xinni Lin, Fernando Antoneli, Yangyang Wang, "Automated Classification of Homeostasis Structure in Input-Output Networks", *Bulletin of Mathematical Biology* 88(7) (2026), 113, Lemma 2.17, Theorem 2.19, Lemma 2.20, Theorem 2.24 and Definitions 2.25 and 2.27 (Section 2.2), <https://doi.org/10.1007/s11538-026-01679-3> (preprint arXiv:2603.08882). The multiple-input-node theory it recasts is due to Madeira and Antoneli (2022).
