# Weighted symmetry of Young tableaux with walls and holes

**Definitions.** Let $n\ge0$ and $0\le k,\ell\le n$. A *Young tableau with walls and holes of type $(n,k,\ell)$* is a bijective filling by $[n+k+\ell]$ of a three-row diagram with $k$ left-justified cells in the top row, $n$ left-justified cells in the middle row, and $\ell$ cells placed in arbitrary columns among the first $n$ positions of the bottom row (the empty bottom positions are *holes*); a wall separates two consecutive bottom positions unless both are holes. The top and middle rows increase from left to right and every column increases from bottom to top, while no order is imposed between distinct bottom cells. Let $d_{n,k,\ell}$ be the number of such tableaux.

Write $\mathrm{TC}_{n,k}$ for the set of rooted binary tree-child networks with $n$ labeled leaves and $k$ reticulation vertices, and let $c_{n,k}$ count the Pons–Batle constrained words in which $k$ letters appear three times and $n-k$ letters twice (equivalently, three-row tableaux with walls of row lengths $(k,n,n)$, so $c_{n,k}=a_{n,k}=d_{n,k,n}$). Let $b_{n,k}=d_{n,n,k}$.

**Theorem (weighted symmetry).** For $n\ge0$ and $0\le k,\ell\le n$,

$$2^{\ell}\,(n-\ell+1)!\;d_{n,k,\ell}\;=\;2^{k}\,(n-k+1)!\;d_{n,\ell,k}.$$

The proof is an explicit involution on *decorated* tableaux $(T;\varepsilon,\rho)$, where $\varepsilon$ assigns $L$ or $R$ to each filled bottom cell and $\rho$ bijectively labels the holes plus one extra symbol by $[n-\ell+1]$; decorated tableaux of type $(n,k,\ell)$ are in bijection with decorated binary networks having $n-k+1$ roots and $n-\ell+1$ leaves, and reversing all edges exchanges the two counts.

**Corollary (Fuchs–Yu identity and Pons–Batle formula).** Taking $\ell=n$,

$$2^{\,n-k}\,a_{n,k}=(n-k+1)!\;b_{n,k},$$

and together with the bijection $2^{n-k}|\mathrm{TC}_{n+1,k}|=(n+1)!\,b_{n,k}$ this gives

$$|\mathrm{TC}_{n,k}|=\frac{n!}{(n-k)!}\,c_{n-1,k},\qquad |\mathrm{TC}_{n,k}|=(n-k+1)\,|\mathrm{TC}_{n,k-1}|+\frac{n(2n+k-3)}{n-k}\,|\mathrm{TC}_{n-1,k}| ,$$

the second from $c_{n,k}=c_{n,k-1}+(2n+k-1)c_{n-1,k}$.

## Expansion

The weights $2^{\ell}$ and $(n-\ell+1)!$ count exactly the decorations of a type-$(n,k,\ell)$ tableau (a side for each of the $\ell$ bottom cells and a labeling of the $n-\ell$ holes plus one marker), so the identity says that decorated tableaux of types $(n,k,\ell)$ and $(n,\ell,k)$ are equinumerous. Reading a decorated tableau in increasing order of entries builds a decorated binary network edge by edge (top entries, bottom entries and two kinds of middle entries correspond to four edge types), and a canonical postorder of edges inverts the construction; reversing every edge of the network swaps roots with leaves and hence $k$ with $\ell$. An independent proof derives the two recurrences $G_{n,k,\ell}=G_{n,k-1,\ell}+(n-\ell+1)G_{n-1,k,\ell}+2(n+k+\ell-1)G_{n-1,k,\ell-1}$ and its mirror image for the weighted counts $G_{n,k,\ell}=2^{\ell}(n-\ell+1)!\,d_{n,k,\ell}$ and checks they are exchanged by $k\leftrightarrow\ell$.

## Sources

- Z. Lin, F. Liu, J. Liu, "A symmetry on Young tableaux with walls and holes", arXiv:2611.15038 (2026), Section 1 (Definition 1.1, Theorem 1.2 and the reduction to the Fuchs–Yu identity and the Pons–Batle formula), Lemmas 2.1–2.2, Theorems 3.3 and 3.6. <https://doi.org/10.48550/arXiv.2611.15038>
