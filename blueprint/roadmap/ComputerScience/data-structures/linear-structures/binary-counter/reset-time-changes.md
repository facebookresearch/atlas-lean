# Reset cost is the Hamming distance

Let $b = (b_0, \dots, b_{k-1})$ be a $k$-bit counter
and $b' = (b'_0, \dots, b'_{k-1})$ the counter returned by resetting $b$. The cost of resetting
$b$ equals the number of indices $i < k$ with $b_i \ne b'_i$.
