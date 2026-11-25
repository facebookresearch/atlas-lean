# Formula for the non-simplex numbers

Let $k$ satisfy $1 < k \le 5$, $k = 7$ or $k = 9$.
For every integer $n \ge 1$, put $R = \lfloor (k!\, n)^{1/k} \rfloor$ and let
$t = n + R - \lfloor k/2 \rfloor$, an integer. Then the $n$-th positive integer that is not a
$k$-simplex number $\binom{j + k - 1}{k}$ with $j \ge 1$ equals $t + 2$ if
$\binom{R + \lceil k/2 \rceil + 1}{k} \le t + 1$; otherwise it equals $t$ if
$t < \binom{R + \lceil k/2 \rceil}{k}$, and $t + 1$ if not.

## Sources

- Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025), Article A95, Theorem 12, Equation (9).
