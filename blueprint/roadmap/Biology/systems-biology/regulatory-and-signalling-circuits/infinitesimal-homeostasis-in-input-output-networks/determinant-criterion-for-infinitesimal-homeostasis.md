# Determinant criterion for infinitesimal homeostasis

**Setting.** An input-output network $\mathcal{G}$ is a directed graph with an input node $\iota$, an output node $o$ and $n$ regulatory nodes $\rho=(\rho_1,\dots,\rho_n)$. An admissible system is a parameterized ODE $\dot X = F(X,\mathcal{I})$ on $X=(x_\iota,x_\rho,x_o)\in\mathbb{R}^{n+2}$ with external input $\mathcal{I}\in\mathbb{R}$, such that $f_j$ depends on $x_\ell$ only if $\mathcal{G}$ has an arrow $\ell\to j$, and $f_\iota$ is the only component depending on $\mathcal{I}$, with $f_{\iota,\mathcal{I}}\neq 0$ generically. Let $X_0$ be a linearly stable equilibrium at $\mathcal{I}_0$, so that a smooth branch of stable equilibria $X(\mathcal{I})$ exists near $\mathcal{I}_0$.

**Definition.** The input-output function is $\mathcal{I}\mapsto x_o(\mathcal{I})$. It exhibits *infinitesimal homeostasis* at $\mathcal{I}_0$ if $x_o'(\mathcal{I}_0)=0$, and *perfect homeostasis* (perfect adaptation) if $x_o'\equiv 0$.

**Homeostasis matrix.** Let $J$ be the $(n+2)\times(n+2)$ Jacobian of $F$ at the equilibrium and let $H$ be the $(n+1)\times(n+1)$ matrix obtained by deleting the first row (the $\iota$ equation) and the last column (the $x_o$ derivatives) of $J$:

$$H=\begin{pmatrix} f_{\rho,x_\iota} & f_{\rho,x_\rho}\\ f_{o,x_\iota} & f_{o,x_\rho}\end{pmatrix}.$$

**Statement.** At an asymptotically stable equilibrium,

$$x_o'(\mathcal{I}) = \pm\frac{f_{\iota,\mathcal{I}}}{\det J}\,\det H,$$

so $\mathcal{I}_0$ is a point of infinitesimal homeostasis if and only if $\det H=0$ there.

**Factorization into homeostasis blocks.** If $\mathcal{G}$ is a core network (every node is downstream of $\iota$ and upstream of $o$), then $\det H$ is not the zero polynomial in the entries $f_{\ell,x_j}$, and by Frobenius-König theory there are permutation matrices bringing $H$ to block upper-triangular form with irreducible diagonal blocks, giving a unique factorization

$$\det H=\det B_1\cdots\det B_m .$$

Generically (one input parameter), infinitesimal homeostasis occurs through exactly one block: $\det B_\eta=0$ and $\det B_\chi\neq 0$ for $\chi\neq\eta$. Each block determines a *homeostasis subnetwork* $\mathcal{K}_\eta\subseteq\mathcal{G}$, and the blocks split into appendage and structural types (see the classification article).

## Depends on

- [Perfect adaptation](../../integral-feedback-and-perfect-adaptation/has-perfect-adaptation.md)

## Expansion

Differentiate $F(X(\mathcal{I}),\mathcal{I})\equiv 0$ to get $J\,X'(\mathcal{I}) = -F_{\mathcal{I}} = -(f_{\iota,\mathcal{I}},0,\dots,0)^{\top}$. By Cramer's rule, $x_o'$ is the determinant of $J$ with its last column replaced by $-F_{\mathcal{I}}$, divided by $\det J$; expanding along that column, whose only nonzero entry sits in the $\iota$ row, leaves $\pm f_{\iota,\mathcal{I}}$ times the minor obtained by deleting the $\iota$ row and the $o$ column, which is $\det H$. Stability gives $\det J\neq 0$, and $f_{\iota,\mathcal{I}}\neq 0$ generically, so only $\det H$ can vanish. Because each entry of $H$ is a distinct formal variable $f_{\ell,x_j}$, the irreducible factors of $\det H$ as a polynomial correspond to the irreducible diagonal blocks of the Frobenius-König normal form, which is what makes the classification purely combinatorial.

## Sources

- Xinni Lin, Fernando Antoneli, Yangyang Wang, "Automated Classification of Homeostasis Structure in Input-Output Networks", *Bulletin of Mathematical Biology* 88(7) (2026), 113, Definition 2.2 and Lemma 2.3 (Section 2.1), <https://doi.org/10.1007/s11538-026-01679-3> (preprint arXiv:2603.08882). The factorization and core-network facts are recalled there from Wang, Huang, Antoneli and Golubitsky (2021) and Madeira and Antoneli (2022).
