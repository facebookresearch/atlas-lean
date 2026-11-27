# Reticulation-labelled Liu polynomial is a complete invariant of separable networks

**Setting.** A rooted binary phylogenetic network $N$ on $X = \{x_1,\dots,x_n\}$ is a rooted DAG without parallel arcs whose leaves are bijectively labelled by $X$, whose root has out-degree $2$, and whose other inner nodes are *tree nodes* (in-degree $1$, out-degree $2$) or *reticulations* (in-degree $2$, out-degree $1$). It is *internally labelled* when its $r$ reticulations are bijectively labelled by $\lambda_1,\dots,\lambda_r$. More generally, an *internally multi-labelled network* (IMLN) allows several leaves with the same label and nodes of in- and out-degree $1$ (elementary nodes) carrying reticulation labels.

Define $p : V(N) \to \mathbb{Z}[x_1,\dots,x_n,\lambda_1,\dots,\lambda_r,y]$ recursively:

$$p(u) = \begin{cases} \varphi(u) & u \text{ a leaf with label } \varphi(u),\\ y + p(v_1)\,p(v_2) & u \text{ a tree node with children } v_1, v_2,\\ \lambda_i\,p(v) & u \text{ has a single child } v \text{ and label } \lambda_i, \end{cases}$$

and $p(N) = p(\rho_N)$ at the root. On phylogenetic trees this is the Liu polynomial.

A node $v$ is a *strong descendant* of $u$ if some directed path from $u$ to $v$ passes only through reticulation or elementary nodes. A tree node $u$ with children $v^{(1)}, v^{(2)}$ is *separable* if both children are tree nodes, or some tree node $u_1 \neq u$ is a strong ancestor of $v^{(1)}$ (or $v^{(2)}$) and either of no other strong descendant of $u$ or of one of the strong descendants of that child. The network is *separable* if all its tree nodes are separable.

**Theorem.**

1. For IMLNs $N_1, N_2$ and a label permutation $\sigma$ fixing $X$ setwise, $p(N_1) = {}^{\sigma}p(N_2)$ if and only if $N_1$ and $N_2$ are equivalent modulo strong paths.
2. For any IMLN, $p(u)$ is irreducible exactly when $u$ is a tree node.
3. If $N_1, N_2$ are internally labelled separable phylogenetic networks and $p(N_1) = {}^{\sigma}p(N_2)$, then $N_1 \cong N_2$. Thus $p$ is a complete invariant of internally labelled separable networks up to isomorphism.
4. Every orchard network is separable, so the invariant is complete on orchard networks.
5. If all leaves carry the same label $x$, then $p(N_1) = p(N_2)$ already implies $N_1 \cong N_2$, giving an invariant in $r+2$ variables for unlabelled separable networks.

## Expansion

Unfolding each reticulation duplicates the subnetwork below it and turns the network into a multi-labelled tree, from which the network can be recovered by folding; $p$ is unchanged under unfolding, so it only sees the network up to the information carried along strong paths. Irreducibility of $y + p(v_1)p(v_2)$ lets one read off the tree nodes and their child polynomials by factoring. Separability guarantees that no two distinct tree nodes share the same child polynomial pair, so the bijection between tree nodes that equality of polynomials provides extends to an isomorphism of networks. Comparing unlabelled networks requires trying all bijective labellings of reticulations, but no permutation of leaf labels.

## Sources

- Joan Carles Pons, Tomás M. Coronado, Michael Hendriksen and Andrew Francis, "A polynomial invariant for a new class of phylogenetic networks", PLOS ONE 17 (2022), e0268181, <https://doi.org/10.1371/journal.pone.0268181>; numbering as in arXiv:2112.15179: Definitions 1–4, 24, 28, Proposition 18, Theorems 26, 35–37 and Proposition 38 (Section 4).
