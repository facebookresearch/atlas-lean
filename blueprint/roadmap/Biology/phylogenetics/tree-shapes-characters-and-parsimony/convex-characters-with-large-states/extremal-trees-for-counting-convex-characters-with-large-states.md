# Extremal trees for counting convex characters with large states

**Definitions.** Let $\mathcal T$ be an unrooted binary phylogenetic tree with $n$ labelled leaves (taxa). A *character* is a partition of the taxa into states; it is *convex* if the minimal subtrees spanning the different states are vertex-disjoint (the character evolves on $\mathcal T$ with no homoplasy). For $k\ge1$ let $g_k(\mathcal T)$ be the number of convex characters in which every state contains at least $k$ taxa. It is known that $g_1(\mathcal T)$ and $g_2(\mathcal T)$ do not depend on the topology: they are the $(2n-1)$-th and $(n-1)$-th Fibonacci numbers. A *caterpillar* $\mathrm{Cat}_n$ is a tree with exactly two cherries. A tree is *fully $k$-loaded* if it is obtained from a scaffold tree on $\lceil n/(k-1)\rceil$ taxa by replacing each leaf by a subtree on $k-1$ taxa, except possibly one leaf replaced by a subtree on $n\bmod(k-1)$ taxa.

**Theorem (maximum).** For all $k\ge1$ and every tree $\mathcal T$ on $n$ taxa, $g_k(\mathcal T)\le g_k(\mathrm{Cat}_n)$. For $n>k\ge2$,

$$g_k(\mathrm{Cat}_n)=g_k(\mathrm{Cat}_{n-1})+g_k(\mathrm{Cat}_{n-k}),$$

so the maximum is $\Theta(\alpha^n)$ with $\alpha$ the positive real root of $x^k-x^{k-1}-1$.

**Theorem (minimum).** For $n\ge k$, every fully $k$-loaded tree minimizes $g_k$, and for $n\ge k\ge2$

$$\min_{\mathcal T}g_k(\mathcal T)=\Big\lfloor\frac{\phi^{\lceil n/(k-1)\rceil-1}}{\sqrt5}+\frac12\Big\rfloor,\qquad\phi=\tfrac{1+\sqrt5}2,$$

the $(\lceil n/(k-1)\rceil-1)$-th Fibonacci number, which grows as $\Theta(\phi^{n/(k-1)})$.

## Expansion

If $\mathcal T$ has a split $A|B$ with $|A|=k$, a $g_k$ character either has $A$ as a state (counted by $g_k(\mathcal T\setminus A)$) or has a state strictly containing $A$, which after deleting one taxon $x\in A$ is a $g_k$ character of $\mathcal T\setminus\{x\}$; hence $g_k(\mathcal T)=g_k(\mathcal T\setminus A)+g_k(\mathcal T\setminus\{x\})$. Caterpillars always contain such a split with both remainders again caterpillars, giving the recurrence, and an induction that *linearizes* subtrees (replacing a subtree by a caterpillar segment) compares an arbitrary tree with the caterpillar, giving the maximum. In a fully $k$-loaded tree every peripheral cluster of $k-1$ taxa is too small to be a state on its own, so each must be absorbed into a larger state; the count reduces to $g_2$ of the scaffold tree, a Fibonacci number by topological neutrality of $g_2$. Bounds on $g_k$ control the running time of algorithms that enumerate convex characters, e.g. for maximum-parsimony distance and agreement-forest problems.

## Sources

- Steven Kelk and Ruben Meuwese, "Sharp Upper and Lower Bounds on a Restricted Class of Convex Characters", The Electronic Journal of Combinatorics 29 (2022), P1.50, <https://doi.org/10.37236/10589>; numbering as in arXiv:2107.10871: Lemmas 3 and 4, Theorem 6, Corollary 7, the definition of fully $k$-loaded trees, Theorem 14 and Corollary 15.
