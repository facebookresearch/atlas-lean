# Ramanujan's recurrence for the series in Entry 12

Fix a complex number $a$. For an
integer $r$ and a complex number $n$, let

$$F_r(n) = \sum_{k=0}^{\infty} \frac{(n+k)^{r+k}}{a^k\, k!},$$

where the sum is taken to be $0$ if the series is not summable. Suppose that $|a| > e$, or that
$a = e$ and $r \le -2$, and that $n + k \ne 0$ for every natural number $k$ with $r + k < 0$.
Then

$$F_{r+1}(n) = n F_r(n) + \frac{1}{a} F_{r+1}(n+1).$$

## Sources

- Berndt, Ramanujan's Notebooks Part I, Chapter 3, definition (12.1) and Entry 12, printed pp. 66-67 / PDF pp. 76-77. Proves `Wanted` entry `ramanujan_part1_ch3_entry12`.
