# Extension space of a tree in BHV tree space

**Setting.** For a finite leaf set, Billera–Holmes–Vogtmann (BHV) tree space $\mathcal T^{N}$ is the space of metric phylogenetic trees on $[N]$ (no degree-two vertices, positive edge weights, leaf edges included). It is a union of nonnegative orthants, one for each maximal set of pairwise compatible splits, whose coordinates are the split lengths. For $\mathcal L\subset[N]$ with $|\mathcal L|=n$ and $\ell=N-n$, the **tree dimensionality reduction map** $\Psi_{\mathcal L}:\mathcal T^{N}\to\mathcal T^{\mathcal L}$ sends a tree to the subtree spanned by the leaves in $\mathcal L$, suppressing degree-two vertices and adding the lengths of the concatenated edges; equivalently, the additive distance matrix of $\Psi_{\mathcal L}(T)$ is the $\mathcal L\times\mathcal L$ submatrix of that of $T$.

For $T\in\mathcal T^{\mathcal L}$ with splits $P_1,\dots,P_{2n-3}$ and weights $\mathbf w$, and an orthant $\mathcal O$ of $\mathcal T^N$ with splits $Q_1,\dots,Q_{2N-3}$, let $M_T^{\mathcal O}$ be the $(2n-3)\times(2N-3)$ projection matrix with $m_{ij}=1$ if $\Psi_{\mathcal L}(Q_j)=P_i$ and $0$ otherwise. The **extension space** of $T$ in $\mathcal O$ is $\{\mathbf x^{\mathcal O}\ge0: M_T^{\mathcal O}\mathbf x^{\mathcal O}=\mathbf w\}$, and the extension space $E_T^N$ of $T$ in $\mathcal T^N$ is the union over the orthants $\mathcal O$ in the connection space $S_T^N$ (those whose topologies restrict to that of $T$).

**Results.**

1. *(Single leaf.)* For a leaf $g\notin\mathcal L$, the space $\Psi_{\bar g}^{-1}(T)$ of $g$-graftings of $T$ is the direct product of $\mathbb R_{\ge0}$ (the new leaf edge) and a piecewise-linear connected curve that is graph-isomorphic to $T$ and meets a strict subset of orthants, each in a one-dimensional linear piece.
2. *(Orthant support.)* An orthant $\mathcal O\subset\mathcal T^N$ contains a tree of $\Psi_{\mathcal L}^{-1}(T)$ if and only if $\Psi_{\mathcal L}(S(\mathcal O))=S(T)$, that is, deleting the labels outside $\mathcal L$ from the splits of $\mathcal O$ yields exactly the split set of $T$, with multiplicity.
3. *(Extension space equals preimage.)* $E_T^N=\Psi_{\mathcal L}^{-1}(T)\subset\mathcal T^N$.
4. *(Connectivity and dimension.)* If $T$ is binary, $E_T^N$ is connected, and for adjacent orthants $\mathcal O_1,\mathcal O_2\subset S_T^N$ one has $E_T^{\mathcal O_1\cap\mathcal O_2}=E_T^{\mathcal O_1}\cap\mathcal O_2=\mathcal O_1\cap E_T^{\mathcal O_2}$. In each orthant the solution set has dimension $(2N-3)-(2n-3)=2\ell$.
5. *(Complexity.)* The connection space has $\frac{(2(n+\ell)-5)!!}{(2n-5)!!}\in O(N^{\ell})$ topologies, all projection matrices are computed in $O(N^{\ell+2})$ time, and membership of a given $\bar x\in\mathcal T^N$ in $E_T^N$ is decided in $O(N)$ by checking $\Psi_{\mathcal L}(\bar x)=T$.
6. *(Distance zero.)* For extension spaces $E_{T,n,\ell}$ and $E_{T',n',\ell'}$ with $n+\ell=n'+\ell'=N$, $d(E_{T,n,\ell},E_{T',n',\ell'})=0$ if and only if some tree in $\mathcal T^N$ contains all splits of $T$ and of $T'$ with the lengths they have in $T$ and $T'$.

## Expansion

Each column of $M_T^{\mathcal O}$ has a single $1$ because every split of the larger tree restricts to exactly one split of $T$, so the linear system says that the lengths of the edges of the big tree that concatenate into an edge $e_i$ of $T$ sum to $w_i$. Since the restriction is a partition of the $2N-3$ splits into $2n-3$ classes and every $w_i>0$, each orthant contributes a product of simplices of total dimension $2\ell$. On a shared face of two orthants the zero coordinates drop out and the two systems coincide, which gives the gluing identity and connectivity. The analysis makes it possible to compare trees with different leaf sets inside one BHV space: a tree on fewer taxa is replaced by the set of all trees on the full taxon set that restrict to it.

## Sources

- Gillian Grindstaff and Megan Owen, "Geometric comparison of phylogenetic trees with different leaf sets", arXiv (2018), Section 2 (Definition 2.4, Proposition 2.5) and Section 3 (Lemma 3.3, Lemma 3.7, Definition 3.9, Proposition 3.10, Theorem 3.12, Proposition 3.13, Lemma 3.14, Lemma 3.17), <https://doi.org/10.48550/arXiv.1807.04235> Published version: SIAM Journal on Applied Algebra and Geometry 3 (2019) 691–720, <https://doi.org/10.1137/18M1235855>.
