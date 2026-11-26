# TBR distance between a phylogenetic tree and an unrooted network

**Setting.** Let $X=\{1,\dots,n\}$. An *unrooted binary phylogenetic network* on $X$ is a connected multigraph whose leaves are bijectively labelled by $X$ and whose other vertices have degree $3$; it is *proper* if every cut-edge separates two labelled leaves. Its *reticulation number* is $r=|E|-(|V|-1)$, and tier $r$ is the set of proper networks with reticulation number $r$ (trees are tier $0$). $N$ *displays* a tree $T$ if a subdivision of $T$ is a subgraph of $N$ with matching leaf labels; $D(N)$ is the set of displayed trees.

A *TBR* move on networks is one of: $\mathrm{TBR}^0$ (move one edge, pruning and regrafting both endpoints, or move a pendant leaf edge), $\mathrm{TBR}^+$ (add an edge between two subdivided edges) and $\mathrm{TBR}^-$ (delete an edge), always staying among proper networks. $d_{\mathrm{TBR}}$ is the length of a shortest TBR sequence.

**Theorem.** Let $T$ be a tree and $N$ a network in tier $r$.

1. $T\in D(N)$ if and only if $d_{\mathrm{TBR}}(T,N)=r$; then $N$ reaches $T$ by $r$ edge deletions. More generally, if $N$ displays a network $N'$ in tier $r'$, then $d_{\mathrm{TBR}}(N',N)=r-r'$.
2. $d_{\mathrm{TBR}}(T,N)=\min_{T'\in D(N)} d_{\mathrm{TBR}}(T,T')+r$.
3. Any two trees displayed by $N$ satisfy $d_{\mathrm{TBR}}(T_1,T_2)\le r$.
4. For networks $N,N'$ with reticulation numbers $r\ge r'$, $d_{\mathrm{TBR}}(N,N')\le \min\{d_{\mathrm{TBR}}(T,T'):T\in D(N),\,T'\in D(N')\}+r$, and $d_{\mathrm{TBR}}(N,N')\le r$ if they display a common tree.
5. No shortest TBR sequence ever applies a deletion before an addition, and the space of trees is an isometric subgraph of the space of networks under TBR (a shortest sequence between two trees never leaves tier $0$).
6. Computing the TBR distance between two networks of the same tier $r$ is NP-hard, for every $r$.

## Expansion

A single move changes the reticulation number by at most one, so $d_{\mathrm{TBR}}(T,N)\ge r$, and deleting edges of $N$ outside an embedding of $T$ (one at a time, choosing an edge whose removal keeps the network proper) gives $r$ deletions when $T\in D(N)$. An addition followed by a deletion can be merged into one $\mathrm{TBR}^0$, and a $\mathrm{TBR}^0$ followed by an addition can be reordered, so shortest paths never dip down a tier and come back. If $d_{\mathrm{TBR}}(N,N')=k$, every tree displayed by $N$ is within TBR distance $k$ of a tree displayed by $N'$; combining this with item 1 and with the isometry of tree space (proved through agreement forests) gives the exact formula of item 2. For item 6, attach $r$ parallel "handcuff" edges to a new cherry of two trees; the resulting networks display exactly one tree each, so their TBR distance equals the tree distance, which is NP-hard to compute.

## Sources

- R. Janssen, J. Klawitter, "Rearrangement operations on unrooted phylogenetic networks", arXiv:1906.04468 (2019), Lemma 4.5, Corollaries 4.6, 4.8, 4.9 and 4.12, Lemma 4.7, Theorem 4.13, Theorem 6.1, Theorem 7.3, <https://doi.org/10.48550/arXiv.1906.04468>.
