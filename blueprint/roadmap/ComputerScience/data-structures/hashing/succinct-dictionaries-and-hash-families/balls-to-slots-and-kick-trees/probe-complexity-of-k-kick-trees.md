# Probe complexity of k-kick trees

Consider the $k$-kick tree with $M = 2^{m_0}$ slots and $1 \le k \le \log^* M - 1$, with fully random hashing: the leaves and depth caps of all balls are independent and distributed as in the definition. Let the operation sequence be fixed in advance by an oblivious adversary that keeps at most $M$ balls present at a time. Then:

1. every insertion moves at most $k + 1$ balls (switching cost at most $k+1$), deterministically;
2. inserting a new ball when fewer than $M$ balls are present gives it expected probe complexity $O(\log^{(k+1)} M)$;
3. at any moment, the expected total probe complexity of the balls present is $O(|A| \log^{(k+1)} M)$, where $A$ is the set of those balls; that is, the expected average probe complexity is $O(\log^{(k+1)} M)$.

Here $\log^{(i)}$ never drops below $1$, so the bounds are at least constant. Claims (2) and (3) are Lemma 1 and Theorem 2 of the source. The source also proves (Theorem 3), for a variant that diverts balls to special slots and hashes the rest to subarrays of size $\sqrt{M}$, each a $k$-kick tree, average probe complexity $O(\log^{(k+1)} M)$ with probability $1 - 2^{-M^{\Omega(1)}}$ at any given moment, again with fully independent hashing.

## Proof sketch

Claim (1) holds because a moved ball keeps its depth and an insertion moves at most one ball per depth below its own. For (2), if $j$ is the largest index with $g_0(x), \dots, g_j(x)$ unsaturated, the new ball $x$ gets probe complexity $O(\log s_{s(x)} + \log s_j)$. The first term has expectation $O(\log^{(k+1)} M)$ from the distribution of $s(x)$ alone. For the second, $g_{i+1}(x)$ can be saturated only if at least $s_{i+1}$ present balls $y$ satisfy $g_{i+1}(y) = g_{i+1}(x)$ and $s(y) \ge i+1$; the number $Y$ of such balls has mean at most $s_{i+1} - s_{i+1}/(\log^{(i+1)} M)^2$, and, the hashes of distinct balls being independent, a Chernoff bound makes $\Pr[Y \ge s_{i+1}]$ small enough that $\sum_{i < k} \log s_i \cdot \Pr[g_{i+1}(x) \text{ saturated}] = O(1)$. Claim (3) follows by linearity of expectation, since each ball's depth, and hence its probe-complexity bound, is fixed at its insertion.

## Depends on

- [k-kick tree balls-to-slots scheme](k-kick-tree.md)
- [Iterated logarithm and log-star](../dictionary-specifications/iterated-logarithm.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602 (Section 3.1: Lemma 1, Theorem 2 and Theorem 3).
