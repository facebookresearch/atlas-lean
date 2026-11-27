# Binary search is correct

Let $p$ be a test on natural numbers and $lo \le hi$ natural numbers. Suppose that $p$ holds on an
initial segment of $\{lo, \dots, hi - 1\}$: for all $i, j$ with $lo \le i \le j < hi$, if $p(j)$ is
true then $p(i)$ is true. Then the result $k$ of the binary search for $p$ on $lo, hi$ satisfies
$lo \le k \le hi$, $p(i)$ is true for every $i$ with $lo \le i < k$, and $p(i)$ is false for every
$i$ with $k \le i < hi$.
