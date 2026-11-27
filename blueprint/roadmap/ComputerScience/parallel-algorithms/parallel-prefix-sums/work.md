# Work of the Kogge–Stone scan

The total work of $K$ rounds on $n$ positions is
$\sum_{k=0}^{K-1} \max(n - 2^k, 0)$, the sum over the rounds $k < K$ of the work
$\max(n - 2^k, 0)$ of round $k$.
