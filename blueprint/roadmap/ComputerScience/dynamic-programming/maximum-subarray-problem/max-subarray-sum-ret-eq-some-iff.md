# Correctness of Kadane's algorithm

Let $\alpha$ be an additive monoid with a linear order
such that $a \le b$ implies $a + c \le b + c$. For every list $L$ over $\alpha$ and every
$m \in \alpha$, Kadane's algorithm returns $m$ on $L$ if and only if $m$ is the maximum sum of a
nonempty contiguous sublist of $L$: some nonempty contiguous sublist of $L$ has sum $m$, and
every nonempty contiguous sublist of $L$ has sum at most $m$.
