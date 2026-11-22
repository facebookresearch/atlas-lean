# Goormaghtigh solutions with $\gcd(m - 1, n - 1) > 1$ and $m \le 50$

Let $x, y, m, n$ be
natural numbers with $2 \le x < y$, $n > 2$, $m \le 50$ and $\gcd(m - 1, n - 1) > 1$, and suppose

$$N = \sum_{i=0}^{m-1} x^i = \sum_{i=0}^{n-1} y^i,$$

that is, $N = (x^m - 1)/(x - 1) = (y^n - 1)/(y - 1)$. Then $N = 31$ or $N = 8191$.

The paper prints the side conditions of its Equation (1) as $y > x \ge 2$ and $n > m > 2$. Since
$y > x$, equal repunits force $m > n$ (the paper's own solution
$31 = 1 + 2 + 4 + 8 + 16 = 1 + 5 + 25$ has $m = 5 > n = 3$), so the printed $n > m$ is read as
$m > n$; that inequality follows from the other hypotheses and is not assumed. The paper quotes
this result as part of Theorem 4 of Bennett, Garbuz and Marten (2020).

## Sources

- Jon Grantham, *No New Goormaghtigh Primes up to 10^700*, INTEGERS 24 (2024), Article A98, Theorem 1.
