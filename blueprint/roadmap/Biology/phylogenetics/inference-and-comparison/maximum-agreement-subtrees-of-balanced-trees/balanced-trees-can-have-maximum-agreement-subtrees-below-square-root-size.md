# Balanced trees can have maximum agreement subtrees below square-root size

**Setting.** A rooted binary phylogenetic $X$-tree is *balanced* if $|X|=2^m$ and its height is $m$ (a complete binary tree with labelled leaves). For trees $\mathcal S,\mathcal T$ on the same leaf set and $Y\subseteq X$, $\mathcal S|Y$ is an *agreement subtree* if the restrictions $\mathcal S|Y$ and $\mathcal T|Y$ (minimal subtrees on $Y$ with degree-two vertices suppressed) are isomorphic as leaf-labelled trees; $\mathrm{mast}(\mathcal S,\mathcal T)$ is the largest such $|Y|$. Martin and Thatte conjectured that two balanced trees on $n$ leaves always satisfy $\mathrm{mast}\ge n^{1/2}$.

**Theorem (counterexample).** For every $c>0$ there are balanced rooted binary phylogenetic $X$-trees $\mathcal S,\mathcal T$, $n=|X|$, with

$$\mathrm{mast}(\mathcal S,\mathcal T)<c\,n^{1/2}.$$

Explicitly, for every positive integer $k$ there are balanced trees on $|X|=2^{2^{k+1}-k-2}$ leaves with $\mathrm{mast}(\mathcal S,\mathcal T)=2^{2^k-k}$; since $(2^{2^{k+1}-k-2})^{1/2}=2^{2^k-k/2-1}$, the ratio $\mathrm{mast}/n^{1/2}=2^{1-k/2}\to0$.

**Theorem (lower bound).** For any two balanced rooted binary phylogenetic $X$-trees with $n=|X|$,

$$\mathrm{mast}(\mathcal S,\mathcal T)\ge n^{0.17}>n^{1/6}.$$

## Expansion

The construction is recursive: the leaves are arranged so that each top-level split of $\mathcal S$ is spread evenly across the subtrees of $\mathcal T$ and vice versa, at every scale, which forces any agreement subtree to lose a constant factor of leaves at each of about $\log\log n$ levels relative to $\sqrt n$. The lower bound comes from choosing, at each level, the better of following a common subtree or combining agreement subtrees from the two halves, which yields a recursion with solution $n^{0.17}$. For random (uniform) binary trees the MAST exponent is a separate question, known to be strictly below $1/2$.

## Sources

- Magnus Bordewich, Simone Linz, Megan Owen, Katherine St. John, Charles Semple and Kristina Wicke, "On the maximum agreement subtree conjecture for balanced trees", arXiv:2005.07357 (2020), Section 1, Theorems 1.1 and 1.3; Theorem 4.6 (explicit construction); Section 5 (proof of the lower bound, Theorem 1.3), <https://doi.org/10.48550/arXiv.2005.07357>.
