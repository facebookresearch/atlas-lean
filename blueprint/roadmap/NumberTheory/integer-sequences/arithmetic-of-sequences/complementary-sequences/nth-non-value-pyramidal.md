# Formula for the non-pyramidal numbers

Let $3 \le k \le 8$, and for $j \ge 1$ let
$P(k, j) = j (j + 1) ((k - 2) j - (k - 5))/6$ be the $k$-gonal pyramidal numbers. For every
integer $n \ge 1$, put $s = \lfloor \sqrt[3]{6n/(k - 2)} \rfloor$. Then the $n$-th positive
integer that is not of the form $P(k, j)$ with $j \ge 1$ equals $n + s + 1$ if
$6n \ge s^3 (k - 2) + 3 s^2 (k - 1) + s (2k - 1) + 6$; otherwise it equals $n + s - 1$ if
$6n \le s (s - 1) (s (k - 2) + k + 1)$, and $n + s$ if not.

## Sources

- Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025), Article A95, Theorem 9, Equation (6).
