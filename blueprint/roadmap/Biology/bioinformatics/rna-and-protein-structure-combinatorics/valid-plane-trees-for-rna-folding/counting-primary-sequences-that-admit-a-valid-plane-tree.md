# Counting primary sequences that admit a valid plane tree

Let $\mathcal A$ be a complementary alphabet of size $2m$, and let $S(n,m)$ be the set of all $(2m)^{2n}$ words of length $2n$ over $\mathcal A$. A word $P$ is a *valid primary sequence* if it admits at least one [$P$-valid plane tree](greedy-valid-plane-tree-and-connectivity-of-the-local-move-graph.md), i.e. a non-crossing perfect matching of its positions that pairs only complementary letters; let $\mathcal P(n,m)$ be the set of such words.

**Theorem.**

*(1)* (Exact count)

$$|\mathcal P(n,m)|=\sum_{\lambda=(\lambda_1,\dots,\lambda_k)\models n}(2m)^k(2m-1)^{n-k}\prod_{i=1}^kC_{\lambda_i-1},$$

where the sum runs over compositions $\lambda$ of $n$ and $C_r$ is the $r$-th Catalan number.

*(2)* (Vanishing proportion) For fixed $m$, $\displaystyle\lim_{n\to\infty}\frac{|\mathcal P(n,m)|}{|S(n,m)|}=0$.

*(3)* (Gap in the number of valid trees) If a word of length $2n$ has $k$ valid plane trees with $k\neq C_n$, then $k\le C_{n-1}$. For $n\ge3$, the number of words in $\mathcal P(n,m)$ with exactly $C_{n-1}$ valid plane trees is $4m(2m-1)n$; at $n=2$ it is $4m(2m-1)$. This corrects Corollary 4.5 of the source, which prints the count $2m(2m-1)(2n)$ with no range on $n$; its argument counts each word twice when $n-1=1$. Also, for $m=1$ exactly $2n$ words have a unique valid plane tree.

## Depends on

- [Greedy valid plane tree and connectivity of the local-move graph](greedy-valid-plane-tree-and-connectivity-of-the-local-move-graph.md)

## Expansion

By the greedy characterization, $P$ is valid exactly when the stack reduction $B\overline B\to\varnothing$ empties the word, so valid words are the words of a Dyck-type language with $m$ pairs of complementary letters. Decomposing a valid word into its irreducible blocks (stretches that return to an empty stack) gives a composition $\lambda$ of $n$; each block of $\lambda_i$ pairs has an outer pair with $2m$ letter choices, a Catalan number $C_{\lambda_i-1}$ of inner shapes, and $2m-1$ choices for each inner opening letter, since it may be anything except the complement of the letter below it on the stack. Comparing this count with $(2m)^{2n}$ shows that the constraint of complementary pairing at every matched position becomes exponentially rare as $n$ grows. The extreme case $k=C_n$ (every plane tree valid) requires all odd positions to carry one letter and all even positions its complement, and the next achievable value is $C_{n-1}$, attained only by words that deviate from this pattern in one odd and one even position.

## Sources

- Frances Black, Elizabeth Drellich, Julianna Tymoczko, "Valid plane trees: Combinatorial models for RNA secondary structures with Watson-Crick base pairs", arXiv:1501.03238 (2015), Proposition 4.3, Corollary 4.5, Proposition 4.6, Theorems 5.2–5.3, <https://doi.org/10.48550/arXiv.1501.03238>.
