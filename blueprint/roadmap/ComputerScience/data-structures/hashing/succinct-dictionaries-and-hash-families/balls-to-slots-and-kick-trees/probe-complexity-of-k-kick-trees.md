# Probe complexity of k-kick trees under 3-wise independence

Consider the $k$-kick tree with $M = 2^{m_0}$ slots and $1 \le k \le \log^* M - 1$, where the pairs (leaf, depth cap) of the balls are drawn from a 3-wise independent family, and the operation sequence is fixed in advance (oblivious adversary). Then:

1. every insertion moves at most $k + 1$ balls (switching cost at most $k+1$), deterministically;
2. inserting a new ball when fewer than $M$ balls are present gives it expected probe complexity $O(\log^{(k+1)} M)$;
3. over any valid operation history, the expected total probe complexity of the balls present at the end is $O(|A| \log^{(k+1)} M)$, where $A$ is the set of those balls.

Here $\log^{(i)}$ never drops below $1$, so the bounds are at least constant. For fully random hashing, (2) and (3) are Lemma 1 and Theorem 2 of the source; the source also proves (Theorem 3), for a variant that diverts balls to special slots and hashes the rest to subarrays of size $\sqrt{M}$, each a $k$-kick tree, average probe complexity $O(\log^{(k+1)} M)$ with probability $1 - 2^{-M^{\Omega(1)}}$ at any given moment, using fully independent hashing.

## Proof sketch

Claim (1) holds because a moved ball keeps its depth and an insertion moves at most one ball per depth below its own. For (2), if $j$ is the largest index with $g_0(x), \dots, g_j(x)$ unsaturated, the new ball $x$ gets probe complexity $O(\log s_{s(x)} + \log s_j)$. The first term has expectation $O(\log^{(k+1)} M)$ from the distribution of $s(x)$ alone. For the second, $g_{i+1}(x)$ can be saturated only if at least $s_{i+1}$ present balls $y$ satisfy $g_{i+1}(y) = g_{i+1}(x)$ and $s(y) \ge i+1$; the number $Y$ of such balls has mean at most $s_{i+1} - s_{i+1}/(\log^{(i+1)} M)^2$. The source bounds $\Pr[Y \ge s_{i+1}]$ by a Chernoff bound; under 3-wise independence the indicators are pairwise independent given $x$'s hash, so $\mathrm{Var}(Y) \le s_{i+1}$ and Chebyshev's inequality gives $\Pr[Y \ge s_{i+1}] = O(1/(\log^{(i+1)} M)^2)$, which suffices because $\sum_{i < k} \log s_i / (\log^{(i+1)} M)^2 = O(\sum_{i<k} 1/\log^{(i+1)} M) = O(1)$. Claim (3) follows by linearity of expectation, since each ball's depth, and hence its probe-complexity bound, is fixed at its insertion.

## Depends on

- [k-kick tree balls-to-slots scheme](k-kick-tree.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)
- [Iterated logarithm and log-star](../dictionary-specifications/iterated-logarithm.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
