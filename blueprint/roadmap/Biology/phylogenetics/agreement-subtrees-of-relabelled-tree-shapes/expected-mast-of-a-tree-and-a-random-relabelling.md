# Expected maximum agreement subtree of a tree and a random relabelling is order square root

For rooted binary leaf-labelled trees $T_1,T_2$ on the same $n$ leaves, $\mathrm{mast}(T_1,T_2)$ is the largest $|Y|$ such that the restrictions $T_1|_Y$ and $T_2|_Y$ are isomorphic as leaf-labelled trees.

**Theorem.** Let $T_1$ be any rooted binary tree with $n$ leaves and let $T_2$ be obtained from $T_1$ by a uniformly random relabelling of its leaves (equivalently, $T_1,T_2$ are independent and uniform among labelled trees with the same tree shape). Then

$$\frac{1-e^{-1}}{4}\sqrt n \;\le\; \mathbb{E}\bigl[\mathrm{mast}(T_1,T_2)\bigr],$$

and for every $\lambda>e\sqrt2$ there is $m$ such that $\mathbb{E}[\mathrm{mast}(T_1,T_2)]\le\lambda\sqrt n$ for all $n\ge m$. Hence $\mathbb{E}[\mathrm{mast}(T_1,T_2)]=\Theta(\sqrt n)$ for every tree shape.

**Upper bound in general.** For any *exchangeable* distribution on rooted binary trees with $n$ leaves (invariant under leaf relabelling, not necessarily sampling consistent), if $T_1,T_2$ are drawn independently from it, then for every $\lambda>e\sqrt2$, $\mathbb{E}[\mathrm{mast}(T_1,T_2)]\le\lambda\sqrt n$ for all large $n$.

**Blob decomposition.** A *cherry blob* of a rooted binary tree is the set of leaves below a vertex (a clade), an *edge blob* is a nonempty difference $C_1\setminus C_2$ of two clades, and a $k$-*blobification* is a family of pairwise disjoint blobs each of size between $k$ and $2k-2$. Every rooted binary leaf-labelled tree with $n$ leaves has a $k$-blobification with at least $n/(4k)$ blobs.

The $\sqrt n$ lower bound holds for *every* shape, including caterpillars and balanced trees; the shape only changes constants.

## Expansion

1. Lower bound: take a $\sqrt n$-blobification with at least $\sqrt n/4$ blobs. Choosing one leaf from each blob gives an unlabelled *scaffold tree* that is the same for $T_1$ and its relabelling; each blob of $T_1$ receives, with probability at least $1-e^{-1}$, some leaf label that lies in the corresponding blob of $T_2$, and these leaves form a common agreement subtree, so its expected size is at least $(1-e^{-1})\sqrt n/4$.
2. Upper bound: by exchangeability the marginal of the induced subtree on any $s$-set is exchangeable, and the collision probability of an exchangeable law on rooted binary shapes with $s$ leaves is at most $2^{s-1}/s!$; a first-moment bound over all $\binom{n}{s}$ subsets gives $\mathbb{P}(\mathrm{mast}\ge s)\le\binom{n}{s}2^{s-1}/s!$, which vanishes for $s=\lambda\sqrt n$ with $\lambda>e\sqrt2$.

## Sources

- P. Misra, S. Sullivant, *Bounds on the expected size of the maximum agreement subtree for a given tree shape*, arXiv:1809.04488 (Proposition 2.4, Theorem 2.6, Theorem 3.7, Corollary 3.8 and Theorem 3.9). <https://doi.org/10.48550/arXiv.1809.04488>
