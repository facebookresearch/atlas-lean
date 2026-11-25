# Binary binomial interpolated triangle

For real numbers $a_0, a_1, \alpha, \beta$, a real
array $(a_{n,k})_{n,k \ge 0}$ is the binary binomial interpolated triangle
$BT(a_0, a_1, \alpha, \beta; \alpha, \beta)$ when $\alpha\beta \ne 0$, $|a_0| + |a_1| \ne 0$,
$a_{0,0} = a_0$, $a_{1,0} = a_1$, $a_{n,0} = \alpha\, a_{n-1,0} + \beta\, a_{n-2,0}$ for every
$n \ge 2$, and $a_{n,k} = \alpha\, a_{n,k-1} + \beta\, a_{n-1,k-1}$ for all $1 \le k \le n$.
Entries $a_{n,k}$ with $k > n$ are not constrained.
