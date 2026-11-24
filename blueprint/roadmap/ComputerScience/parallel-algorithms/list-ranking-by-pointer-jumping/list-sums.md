# Suffix sums by pointer jumping on arrays

Given a partial successor function
$\mathrm{succ}$ on nodes $0, \dots, n-1$ and values $x_v$ in an additive monoid $M$, this is
the array of sums obtained after $\lceil \log_2 n \rceil$ rounds (the least $k$ with
$n \le 2^k$) of pointer jumping on arrays, starting from the pointers $\mathrm{succ}(v)$ and the
sums $x_v$.

When every list ends, entry $v$ is the suffix sum of node $v$.
