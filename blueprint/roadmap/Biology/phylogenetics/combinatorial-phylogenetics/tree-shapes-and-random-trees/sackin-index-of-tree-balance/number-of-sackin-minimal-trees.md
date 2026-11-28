# Number of trees with minimal Sackin index

**Setting.** Let $s(n)$ be the number of (unlabelled) rooted binary trees with $n$ leaves that minimize the [Sackin index](extremal-values-of-the-sackin-index.md), $k = \lceil \log_2 n \rceil$, and write a binary tree as $T = (T_a, T_b)$ with $n_a \ge n_b$ leaves in its two maximal pending subtrees.

**Theorem.**
1. (Recursive characterization) $T$ has minimum Sackin index if and only if $T_a$ and $T_b$ have minimum Sackin index and $n_a - n_b \le \min\{n - 2^{k-1},\, 2^k - n\}$.
2. (Recursion) $s(1) = 1$ and, for $n > 1$,

$$s(n) = \sum_{\substack{n_a + n_b = n \\ n/2 < n_a \le 2^{k-1},\; n_b \ge 2^{k-2}}} s(n_a)\,s(n_b) + f(n), \qquad f(n) = \begin{cases} 0 & n \text{ odd},\\ \binom{s(n/2)+1}{2} & n \text{ even}. \end{cases}$$

3. (Uniqueness) The Sackin minimizer is unique if and only if $n \in \{2^m - 1, 2^m, 2^m + 1\}$ for some $m \in \mathbb{N}$.
4. (Ordered trees) The number of rooted binary ordered trees with $n$ leaves and minimal Sackin index is

$$ot(n) = \binom{2^{k-1}}{n - 2^{k-1}},$$

and the number of ordered trees with maximal Sackin index is $2^{n-2}$ for $n \ge 2$.

## Depends on

- [Extremal values of the Sackin index](extremal-values-of-the-sackin-index.md)

## Expansion

Since a minimizer has leaves only at depths $k-1$ and $k$, both pending subtrees must themselves be minimizers whose depth profiles fit inside depth $k-1$; the bound on $n_a - n_b$ is exactly the condition that neither subtree is forced below depth $k$ nor leaves an unused slot at depth $k-2$. The recursion sums over admissible splits, with the even term $f(n)$ counting unordered pairs of minimizers of size $n/2$ (with repetition). For ordered trees, a minimizer is a complete tree of depth $k-1$ in which exactly $n - 2^{k-1}$ of the $2^{k-1}$ depth-$(k-1)$ positions are split into cherries, giving the binomial coefficient. The values of $s(n)$ for $n = 1,\ldots,16$ are $1,1,1,1,1,2,1,1,1,3,3,5,3,3,1,1$.

## Sources

- Mareike Fischer, "Extremal values of the Sackin tree balance index", arXiv:1801.10418 (2018), Section 3, Theorem 3, Corollaries 1, 2 and 5, Theorem 7, Remark 5, <https://doi.org/10.48550/arXiv.1801.10418>. Published version: Annals of Combinatorics 25 (2021) 515–541, <https://doi.org/10.1007/s00026-021-00539-2>.
