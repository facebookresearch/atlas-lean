# Subtree-size profile of the GFB tree

**Setting.** For $n\ge1$ let $T_n^{gfb}$ be the greedy-from-the-bottom tree (repeatedly join two smallest trees of a forest of $n$ single leaves) and $T_n^{c}$ Fill's *complete tree*: take the fully balanced tree with $2^{\lfloor\log_2 n\rfloor}$ leaves, order its leaves left to right, and replace leaves by cherries from left to right until there are $n$ leaves. Write $\log=\log_2$.

**Lemma (complete = GFB).** $T_n^{gfb}=T_n^c$ for all $n\ge1$. Writing $T_n^{gfb}=(T_a,T_b)$ with $n_a\ge n_b$ and $\ell_n=\lfloor\log n\rfloor$, one has $n_b=2^{\ell_n-1}$ if $n\le3\cdot2^{\ell_n-1}$, and $n_a=2^{\ell_n}$ otherwise.

**Theorem (subtree sizes, Section 4.3).** Let $a_n(i)$ be the number of pending subtrees of $T_n^{gfb}$ with $i$ leaves and $k_i=\lceil\log i\rceil$. Then

$$a_n(i)=\begin{cases}\lfloor n/i\rfloor & i=2^{k_i}\text{ and }\big(n\bmod i=0\text{ or }n\bmod i\ge2^{k_i-1}\big),\\ \lfloor n/i\rfloor-1 & i=2^{k_i}\text{ and }0<n\bmod i<2^{k_i-1},\\ 1 & i\ne2^{k_i}\text{ and }(n-i)\bmod 2^{k_i-1}=0,\\ 0 & i\ne2^{k_i}\text{ and }(n-i)\bmod2^{k_i-1}>0.\end{cases}$$

**Corollary (minimum values).** For $c>-2$, $\pi_c(T_n^{gfb})=\prod_{i=2}^n(i+c)^{a_n(i)}$; this gives closed forms for the minimum $\widehat s$-shape statistic ($c=-1$, OEIS A132862) and the minimum $Q$-shape statistic ($c=0$).

## Depends on

- [GFB trees minimize concave subtree-size indices](gfb-trees-minimize-concave-subtree-size-indices.md)

## Expansion

In the complete-tree picture every pending subtree is either a fully balanced tree (size a power of two) or one of the at most $\lceil\log n\rceil$ subtrees on the path from the root to the boundary between replaced and unreplaced leaves. Fully balanced subtrees of size $i=2^{k}$ tile the leaf sequence in blocks of $i$, giving $\lfloor n/i\rfloor$ of them except when the last block is cut by the cherry boundary in its first half. A non-power-of-two size occurs at most once, on that boundary path, exactly when $n-i$ is a multiple of $2^{k_i-1}$. The product formula then just regroups $\prod_v(n_v+c)$ by subtree size.

## Sources

- S. Cleary, M. Fischer, K. St. John, "The GFB Tree and Tree Imbalance Indices", *Bulletin of Mathematical Biology* 87(10) (2025), 145, Section 2 (definitions of GFB and complete trees), Section 4.3 (complete-tree lemma, subtree-size theorem and product corollary), <https://doi.org/10.1007/s11538-025-01522-1> (preprint arXiv:2502.12854).
