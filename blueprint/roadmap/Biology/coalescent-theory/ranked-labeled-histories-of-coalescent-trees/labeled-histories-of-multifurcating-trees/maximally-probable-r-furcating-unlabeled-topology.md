# Maximally probable $r$-furcating unlabeled topology

**Setting.** A rooted $r$-furcating labeled topology $T$ has every internal vertex with exactly $r$ children; it has $n = w(r-1) + 1$ leaves for some $w \ge 1$ internal vertices. A labeled history is an ordering of the internal vertices consistent with ancestry (a sequence of $r$-way branchings producing $T$). Under the Yule-Harding model, or the coalescent read backwards, all labeled histories are equally likely, so the probability of $T$ is proportional to its number of labeled histories $N(T)$.

**Counting formula.** With $m(v)$ the number of leaves below internal vertex $v$ (so the subtree at $v$ has $(m(v)-1)/(r-1)$ internal vertices, and this is the hook-length count of labeled histories specialized to $r$-furcating trees),

$$N(T) = \frac{\bigl(\frac{n-1}{r-1}\bigr)!}{\prod_{v \in V^0(T)} \frac{m(v)-1}{r-1}}, \qquad N(T) = 1 \text{ for } n = 1 .$$

**Theorem.** Fix $r \ge 2$, $w \ge 1$, $n = w(r-1)+1$. The unique unlabeled $r$-furcating topology whose labelings maximize $N(T)$ is

$$U_n^* = (s-1)\,U^*_{r^{p-1}} \oplus U^*_{r^{p-1}+b} \oplus (r-s)\,U^*_{r^p},$$

joining $r$ maximal subtrees at the root, where

$$p = \lfloor \log_r n \rfloor, \qquad s = \Bigl\lfloor \frac{r^{p+1} - n}{r^p - r^{p-1}} \Bigr\rfloor, \qquad b = n - \bigl[s\,r^{p-1} + (r-s)\,r^p\bigr].$$

It coincides with the $r$-ary Huffman tree for uniform weights. For $r = 2$ this recovers the Harding-Hammersley-Grimmett result $U_n^* = U_t^* \oplus U_{n-t}^*$ with $t = 2^{\lfloor \log_2((n-1)/3)\rfloor + 1}$ for $n \ge 3$.

## Depends on

- [Labeled histories of at-most-r-furcating trees](labeled-histories-of-at-most-r-furcating-trees.md)

## Related topics

- [Maximally probable at-most-r-furcating topologies are bifurcating](maximally-probable-at-most-r-furcating-topologies-are-bifurcating.md): the case $r = 2$.

## Proof idea

Maximizing $N(T)$ is minimizing $\sum_v \log\frac{m(v)-1}{r-1}$, a sum of a concave function of clade sizes over internal vertices. Huffman's algorithm minimizes the weighted external path length $\sum_v m(v)$, and majorization (Schur-convexity of separable convex sums) transfers its optimality to any such separable objective, so the maximally probable shape is the Huffman tree, as balanced as the leaf count permits: full complete $r$-ary subtrees of sizes $r^{p-1}$ and $r^p$ with one intermediate subtree absorbing the remainder $b$.

## Sources

- E. H. Dickey and N. A. Rosenberg, "Maximally probable tree topologies with multifurcation: a connection to Huffman trees", Journal of Applied Probability, in press (accepted; no DOI assigned yet). Numbering as in the preprint "Maximally probable tree topologies with $r$-furcation", arXiv:2602.07426v1, <https://arxiv.org/abs/2602.07426v1>: Proposition 2, Theorem 1 (cited), Proposition 5, Proposition 17 and Theorem 19.
