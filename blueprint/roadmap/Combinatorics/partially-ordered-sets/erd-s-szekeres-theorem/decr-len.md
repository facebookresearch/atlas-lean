# Length of the longest decreasing subsequence ending at a point

For a real sequence $f$
indexed by $\{0, \dots, N-1\}$ and an index $p$, this is the largest $k$ such that $f$ has a
strictly decreasing subsequence of length $k$ ending at $p$, that is, indices
$i_1 < \dots < i_k = p$ with $f(i_1) > \dots > f(i_k)$. The maximum exists: $k = 1$ qualifies, and
every such $k$ is at most $N$.
