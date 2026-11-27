# Infinitesimal homeostasis and the homeostasis matrix

**Setting.** An *input-output network* $\mathcal G$ is a directed graph with a distinguished input node $\iota$, output node $o$ and regulatory nodes $\rho=(\rho_1,\dots,\rho_n)$. An *admissible system* is a smooth family

$$\dot x_\iota=f_\iota(x_\iota,x_\rho,x_o,\mathcal I),\qquad \dot x_\rho=f_\rho(x_\iota,x_\rho,x_o),\qquad \dot x_o=f_o(x_\iota,x_\rho,x_o),$$

in which each $f_k$ depends only on $x_k$ and the variables of nodes with an arrow into $k$, and the external input parameter $\mathcal I\in\mathbb R$ enters only the input equation. Suppose $X^*(\mathcal I)$ is a family of linearly stable equilibria; the *input-output function* is $x_o(\mathcal I)$, the output coordinate of $X^*(\mathcal I)$. The system exhibits **infinitesimal homeostasis** at $\mathcal I_0$ if $x_o'(\mathcal I_0)=0$. Let $J$ be the $(n+2)\times(n+2)$ Jacobian of the system at $X^*$; the **homeostasis matrix** $H$ is the $(n+1)\times(n+1)$ matrix obtained from $J$ by deleting its first row (the $\iota$ equation) and last column (the $x_o$ derivatives).

**Theorem 2.3 (determinant formula).** $x_o'(\mathcal I)=\pm f_{\iota,\mathcal I}\,\det(H)/\det(J)$. Hence, generically ($f_{\iota,\mathcal I}\ne0$), infinitesimal homeostasis occurs at $\mathcal I_0$ if and only if $\det H=0$ there.

**Theorem 2.4 (core reduction).** Let $\mathcal G_c$ be the *core subnetwork*, consisting of the nodes that lie on some directed path from $\iota$ to $o$. The input-output function of $\mathcal G_c$ has infinitesimal homeostasis at $\mathcal I_0$ if and only if that of $\mathcal G$ does. Backward arrows (into $\iota$ or out of $o$) do not enter $H$, so core networks differing only in backward arrows are core equivalent (Corollary 2.5).

**Theorem 3.1 and Theorem 3.2 (homeostasis types).** At a hyperbolic equilibrium there are permutation matrices $P,Q$ with $PHQ$ block upper triangular, with irreducible square diagonal blocks $B_1,\dots,B_m$, so $\det H=\prod_\eta\det B_\eta$. Each $k\times k$ block has either $k$ self-coupling entries (an *appendage* block, given by the Jacobian of a strongly connected set of nodes off the main paths) or $k-1$ (a *structural* block, associated with a segment between consecutive super-simple nodes, the nodes through which every $\iota\to o$ path passes). Each way of making $\det H$ vanish is thus a homeostasis type tied to a subnetwork.

## Expansion

At equilibrium, implicit differentiation gives $J\,\frac{dX^*}{d\mathcal I}=-(f_{\iota,\mathcal I},0,\dots,0)^{\mathsf T}$; Cramer's rule for the output component replaces the last column of $J$ by the right-hand side, and expanding along that column leaves the minor obtained by deleting the first row and last column, which is $\det H$. Only couplings along forward paths appear in $H$, which is why the core subnetwork suffices. Structural blocks correspond to cancellation along feedforward paths (as in feedforward excitation), appendage blocks to a degenerate Jacobian of a regulatory loop (as in negative feedback); singularity theory of the scalar function $x_o(\mathcal I)$ then classifies chairs and other higher-codimension homeostasis points.

## Sources

- F. Antoneli, M. Golubitsky, J. Jin, I. Stewart, "Homeostasis in input-output networks: structure, classification and applications", *Mathematical Biosciences* 384 (2025), 109435, Theorem 2.3, Theorem 2.4, Corollary 2.5, Theorem 3.1, Theorem 3.2, <https://doi.org/10.1016/j.mbs.2025.109435> (preprint arXiv:2405.03861).
