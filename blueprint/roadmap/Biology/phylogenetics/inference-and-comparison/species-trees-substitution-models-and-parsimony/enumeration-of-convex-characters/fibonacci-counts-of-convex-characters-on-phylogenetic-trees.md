# Fibonacci counts of convex characters on phylogenetic trees

**Setting.** Let $\mathcal{T}$ be an unrooted binary phylogenetic tree on a taxon set $X$, $|X| = n \ge 2$. A character $f : X \to \mathcal{C}$ (identified with the partition of $X$ it induces) is **convex** on $\mathcal{T}$ if it has an extension to all vertices in which every state induces a connected subtree, i.e. it can evolve on $\mathcal{T}$ with no homoplasy. Let $g_k(\mathcal{T},r)$ be the number of convex $r$-state characters in which every state occurs on at least $k$ taxa, $g_k(\mathcal{T}) = \sum_r g_k(\mathcal{T},r)$, and let $F(m)$ be the Fibonacci numbers, $F(1) = F(2) = 1$.

**Theorem.**
1. For $n \ge 2$ and $r \ge 1$, $g_2(\mathcal{T},r)$ does not depend on the topology of $\mathcal{T}$:

$$g_2(\mathcal{T},r) = \binom{n-r-1}{r-1}.$$

2. Summing over $r$, $g_2(\mathcal{T}) = F(n-1)$, and the classical count $g_1(\mathcal{T},r) = \binom{2n-r-1}{r-1}$ sums to $g_1(\mathcal{T}) = F(2n-1)$; in particular $g_2(n) = g_1(n/2)$ for even $n$.
3. For every fixed $k$, $g_k(\mathcal{T})$ can be computed by dynamic programming in $O(k^2 n)$ time and $O(kn)$ space, and its characters can be listed in $O(g_k(\mathcal{T})\,k^2 n)$ total time or sampled uniformly in $O(k^2 n)$ time. For $k \ge 3$ the count depends on the topology.
4. (Maximum parsimony distance.) For two unrooted binary trees on the same $n$ taxa, $d_{MP}(\mathcal{T}_1,\mathcal{T}_2) = \max_f |l_f(\mathcal{T}_1) - l_f(\mathcal{T}_2)|$, with $l_f$ the Fitch parsimony score, can be computed in $\Theta(\phi^n n^2)$ time, $\phi = (1+\sqrt5)/2$; listing convex characters also enumerates all agreement forests of two trees, giving TBR distance in $\Theta(2.619^n\,\mathrm{poly}(n))$ time.

## Expansion

For part 1, root the argument at a cherry $\{x,y\}$, which every binary tree with $n \ge 4$ has. Because every state has at least two taxa, $x$ and $y$ share a state. If that state is exactly $\{x,y\}$, deleting the cherry leaves a $g_2$ character with $r-1$ states on $n-2$ taxa; otherwise, collapsing the cherry to one taxon leaves a $g_2$ character with $r$ states on $n-1$ taxa. Hence $g_2(\mathcal{T},r) = g_2(\mathcal{T}'',r-1) + g_2(\mathcal{T}',r)$, which is Pascal's rule for $\binom{n-r-1}{r-1}$ whatever the shape of the tree, and the diagonal sums of Pascal's triangle are Fibonacci numbers. For part 4, an optimal character for $d_{MP}$ can be taken convex on $\mathcal{T}_1$ or $\mathcal{T}_2$ with every state on at least two taxa, so it suffices to score the $2F(n-1) = \Theta(\phi^n)$ such characters with Fitch's algorithm.

## Sources

- Steven Kelk, Georgios Stamoulis, "A note on convex characters, Fibonacci numbers and exponential-time algorithms", Advances in Applied Mathematics 84 (2017), 34–46, <https://doi.org/10.1016/j.aam.2016.10.003>. Published version of arXiv:1508.02598, cited next; locators there refer to the arXiv version.
- Steven Kelk, Georgios Stamoulis, "A note on convex characters, Fibonacci numbers and exponential-time algorithms", arXiv:1508.02598 (2015), Section 2 (definitions and the count of convex characters), Theorem 1, Corollary 2, Theorem 3, Theorem 4, Corollary 5, Theorems 6 and 7, <https://doi.org/10.48550/arXiv.1508.02598>.
