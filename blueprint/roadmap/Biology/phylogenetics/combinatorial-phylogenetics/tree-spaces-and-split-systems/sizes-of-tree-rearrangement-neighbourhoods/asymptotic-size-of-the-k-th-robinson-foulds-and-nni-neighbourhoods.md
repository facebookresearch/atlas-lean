# Asymptotic size of the k-th Robinson–Foulds and NNI neighbourhoods

**Setting.** Let $UB(n)$ be the set of unrooted binary phylogenetic trees on leaf set $\{1,\dots,n\}$, and $UB(n,c)$ those with exactly $c$ cherries (paths of length two whose endpoints are both leaves). For a tree $T$ let $\Sigma(T)$ be its set of splits. The Robinson–Foulds distance is $\delta_{RF}(T_1,T_2)=\tfrac12|\Sigma(T_1)\setminus\Sigma(T_2)|+\tfrac12|\Sigma(T_2)\setminus\Sigma(T_1)|$, equivalently the least $m$ such that contracting $m$ edges in each tree gives the same tree. The NNI distance $\delta_{NNI}$ is the least number of nearest neighbour interchanges (swapping two subtrees across an internal edge) turning one tree into the other. For a metric $\delta_\theta$ the $k$-th neighbourhood is $N^k_\theta(T)=\{T'\in UB(n):\delta_\theta(T,T')=k\}$.

**Theorem.** Let $T\in UB(n)$ with $n\ge4$, and fix $k\in\mathbb{Z}^+$. Then

$$|N^k_{RF}(T)|=\frac{2^k n^k}{k!}\Big(1+C_{T,k}\,n^{-1}+O(n^{-2})\Big),\qquad -\frac{5k^2+7k}{4}\le C_{T,k}\le 4k^2-7k,$$

$$|N^k_{NNI}(T)|=\frac{2^k n^k}{k!}\Big(1+D_{T,k}\,n^{-1}+O(n^{-2})\Big),\qquad -\frac{3k(k+1)}{2}\le D_{T,k}\le 3k(k-2).$$

So to first order both neighbourhood sizes depend only on $n$ and $k$, and shape enters at relative order $1/n$.

The source's Appendix (Theorem A.1) also prints an exact formula for the third NNI neighbourhood, $|N^3_{NNI}(T)|=\frac43 n^3-8n^2-\frac{70}{3}n+8cn+12\,p_3(T)+164$ for $T\in UB(n,c)$, with $p_3(T)$ the number of distinct internal paths of length three; this page does not state it, because it is false as printed: for $n=5$ ($c=2$, $p_3=0$) it gives $94$, more than the $15$ trees in $UB(5)$, and a brute-force count for $n=4,\dots,9$ differs from it by exactly $46c$ in every class.

## Expansion

A tree has $n-3$ internal edges and each admits two NNI moves (or two RF-unit resolutions), so choosing $k$ distinct, pairwise non-adjacent internal edges and one of two moves on each produces $\binom{n-3}{k}2^k\sim (2n)^k/k!$ trees, which is the leading term. The work is bounding the corrections: sequences of NNI moves on distinct non-adjacent edges commute, moves on edges that are later undone collapse to shorter sequences, and sets of moves that differ in which edges they touch yield disjoint sets of trees because they change different splits. Adjacent-edge configurations, of which there are $O(n^{k-1})$, account for the $1/n$ term, and counting them in the extreme shapes gives the bounds on $C_{T,k}$ and $D_{T,k}$.

## Sources

- Jamie V. de Jong, Jeanette C. McLeod, Mike Steel, "Neighbourhoods of phylogenetic trees: exact and asymptotic counts", arXiv:1508.03774 (2015); SIAM Journal on Discrete Mathematics 30 (2016): Section 3 (main Robinson–Foulds theorem), Section 4 (main NNI theorem and its corollaries on disjoint and commuting move sequences). <https://doi.org/10.48550/arXiv.1508.03774> Published version: SIAM Journal on Discrete Mathematics 30 (2016) 2265–2287, <https://doi.org/10.1137/15m1035070>.
