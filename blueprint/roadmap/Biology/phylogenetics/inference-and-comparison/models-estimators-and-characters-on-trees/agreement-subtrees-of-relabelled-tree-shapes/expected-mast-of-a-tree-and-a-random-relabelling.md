# Expected maximum agreement subtree of a tree and a random relabelling is order square root

For rooted binary leaf-labelled trees $T_1,T_2$ on the same $n$ leaves, $\mathrm{mast}(T_1,T_2)$ is the largest $|Y|$ such that the restrictions $T_1|_Y$ and $T_2|_Y$ are isomorphic as leaf-labelled trees.

**Theorem.** Let $T_1$ be any rooted binary tree with $n\ge2$ leaves and let $T_2$ be obtained from $T_1$ by a uniformly random relabelling of its leaves (equivalently, $T_1,T_2$ are independent and uniform among labelled trees with the same tree shape). Then, with $k=\lceil\sqrt n\,\rceil$,

$$
\mathbb{E}\bigl[\mathrm{mast}(T_1,T_2)\bigr]\;\ge\;\bigl(1-e^{-1}\bigr)\frac{n}{4\lceil\sqrt n\,\rceil}\;\ge\;\frac{1-e^{-1}}{8}\sqrt n ,
$$

where the first bound equals $\frac{1-e^{-1}}{4}\sqrt n$ when $n$ is a perfect square. For every $\lambda>e\sqrt2$ there is $m$ such that $\mathbb{E}[\mathrm{mast}(T_1,T_2)]\le\lambda\sqrt n$ for all $n\ge m$. Hence $\mathbb{E}[\mathrm{mast}(T_1,T_2)]=\Theta(\sqrt n)$ for every tree shape.

**Upper bound in general.** For any *exchangeable* distribution on rooted binary trees with $n$ leaves (invariant under leaf relabelling, not necessarily sampling consistent), if $T_1,T_2$ are drawn independently from it, then for every $\lambda>e\sqrt2$, $\mathbb{E}[\mathrm{mast}(T_1,T_2)]\le\lambda\sqrt n$ for all large $n$.

**Blob decomposition.** A *cherry blob* of a rooted binary tree is the set of leaves below a vertex (a clade), an *edge blob* is a nonempty difference $C_1\setminus C_2$ of two clades, and, for an integer $k$, a $k$-*blobification* is a family of pairwise disjoint blobs each of size between $k$ and $2k-2$. For every integer $k$ with $2\le k\le n$, every rooted binary leaf-labelled tree with $n$ leaves has a $k$-blobification with at least $n/(4k)$ blobs. The range matters: for $k=1$ no blob has size between $1$ and $0$, and for $k>n$ no blob has $k$ leaves, while $n/(4k)>0$ in both cases.

The $\sqrt n$ lower bound holds for *every* shape, including caterpillars and balanced trees; the shape only changes constants.

## Expansion

1. Lower bound: blob sizes are integers, so the blobification is taken with the integer $k=\lceil\sqrt n\,\rceil$, which satisfies $2\le k\le n$ for $n\ge2$ and $k^2\ge n$. It has $s\ge n/(4k)$ blobs. Choosing one leaf from each blob gives an unlabelled *scaffold tree* that is the same for $T_1$ and its relabelling. The blob of $T_2$ at the same scaffold position is a uniformly random set of the same size, at least $k$, so it meets the blob of $T_1$ with probability at least $1-(1-k/n)^k\ge1-e^{-k^2/n}\ge1-e^{-1}$. One common leaf from each meeting pair spans a common agreement subtree, so its expected size is at least $(1-e^{-1})s\ge(1-e^{-1})n/(4\lceil\sqrt n\,\rceil)$, and $\lceil\sqrt n\,\rceil\le2\sqrt n$ gives the second bound. The choice $k\approx\sqrt n$ balances the number of blobs ($\approx n/k$) against the meeting probability (bounded below once $k^2\ge n$).
2. Upper bound: by exchangeability the marginal of the induced subtree on any $s$-set is exchangeable, and the collision probability of an exchangeable law on rooted binary shapes with $s$ leaves is at most $2^{s-1}/s!$; a first-moment bound over all $\binom{n}{s}$ subsets gives $\mathbb{P}(\mathrm{mast}\ge s)\le\binom{n}{s}2^{s-1}/s!$, which vanishes for $s=\lambda\sqrt n$ with $\lambda>e\sqrt2$.

## Sources

- P. Misra, S. Sullivant, *Bounds on the expected size of the maximum agreement subtree for a given tree shape*, SIAM Journal on Discrete Mathematics 33 (2019) 2316–2325, <https://doi.org/10.1137/18M1213695>; preprint arXiv:1809.04488 (Proposition 2.4, Lemma 2.5, Theorem 2.6, Theorem 3.7, Corollary 3.8 and Theorem 3.9). Theorem 2.6 is printed with the constant $\frac{1-e^{-1}}4\sqrt n$ and a $\sqrt n$-blobification; the bound above makes the integer choice of $k$ explicit.
