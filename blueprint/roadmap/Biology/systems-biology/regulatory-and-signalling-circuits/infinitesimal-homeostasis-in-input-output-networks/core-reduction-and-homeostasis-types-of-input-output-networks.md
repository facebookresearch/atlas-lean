# Core reduction and homeostasis types of input-output networks

**Setting.** Input-output networks $\mathcal G$ (input node $\iota$, output node $o$, regulatory nodes $\rho$), admissible systems, the input-output function $x_o(\mathcal I)$ along a family of linearly stable equilibria, the homeostasis matrix $H$ and the determinant formula $x_o'(\mathcal I)=\pm f_{\iota,\mathcal I}\det H/\det J$ are as in [Determinant criterion for infinitesimal homeostasis](determinant-criterion-for-infinitesimal-homeostasis.md), as is the Frobenius–König factorization $\det H=\prod_\eta\det B_\eta$ into irreducible square diagonal blocks of $PHQ$, for permutation matrices $P,Q$. This page adds two facts.

**Theorem 2.4 (core reduction).** Let $\mathcal G_c$ be the *core subnetwork*, consisting of the nodes that lie on some directed path from $\iota$ to $o$. The input-output function of $\mathcal G_c$ has infinitesimal homeostasis at $\mathcal I_0$ if and only if that of $\mathcal G$ does. Backward arrows (into $\iota$ or out of $o$) do not enter $H$, so core networks differing only in backward arrows are core equivalent (Corollary 2.5).

**Theorem 3.2 (homeostasis types).** Each $k\times k$ irreducible diagonal block $B_\eta$ has either $k$ self-coupling entries $f_{j,x_j}$ (an *appendage* block, given by the Jacobian of a strongly connected set of nodes off the $\iota o$-simple paths) or $k-1$ (a *structural* block, associated with a segment between consecutive super-simple nodes, the nodes through which every $\iota\to o$ simple path passes). Each way of making $\det H$ vanish is thus a homeostasis type tied to a subnetwork.

## Depends on

- [Determinant criterion for infinitesimal homeostasis](determinant-criterion-for-infinitesimal-homeostasis.md)

## Expansion

Only couplings along forward paths appear in $H$, which is why the core subnetwork suffices. Structural blocks correspond to cancellation along feedforward paths (as in feedforward excitation), appendage blocks to a degenerate Jacobian of a regulatory loop (as in negative feedback); singularity theory of the scalar function $x_o(\mathcal I)$ then classifies chairs and other higher-codimension homeostasis points.

## Sources

- F. Antoneli, M. Golubitsky, J. Jin, I. Stewart, "Homeostasis in input-output networks: structure, classification and applications", *Mathematical Biosciences* 384 (2025), 109435, Theorem 2.4, Corollary 2.5, Theorem 3.2, <https://doi.org/10.1016/j.mbs.2025.109435> (preprint arXiv:2405.03861).
