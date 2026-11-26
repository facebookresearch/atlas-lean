# Absolute-deviation minimizers of a sample are the median interval

Let $n \ge 1$ and let $x_{(1)} \le \dots \le x_{(n)}$ be the order statistics of a sample of real numbers, counting repeated observations with their multiplicities. The function $f(m) = \sum_i |x_i - m|$ attains its minimum exactly on the closed interval $[x_{(\lceil n/2 \rceil)},\ x_{(\lfloor n/2 \rfloor + 1)}]$. For odd $n$ this is the single point $x_{((n+1)/2)}$; for even $n$ it is the interval between the two middle order statistics, a single point when they are equal.

To see this, pair each order statistic with the one at its reverse index. For a pair with endpoints $a \le b$, the contribution $|a-m| + |b-m|$ equals $b-a$ on $[a,b]$ and is strictly larger outside. Every paired interval contains the median interval, and the middle pair has exactly that interval. Summing all pairs counts each deviation twice, so the middle pair forces a strict increase outside the median interval.

For $n = 0$ there are no middle order statistics, and every real number minimizes the empty sum.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
