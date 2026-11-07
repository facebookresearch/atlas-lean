# Recovering a doubly exponential sequence from its reciprocal sum

Let $\beta \ge 0$ and
$r$ be real numbers, and let $(a_n)_{n \ge 0}$ be a sequence of positive integers with
$|a_n^2 / a_{n+1} - \beta| \le 1/3$ for all $n$ and $\sum_n 1 / a_n = r$. Write
$x_n = r - \sum_{k\lt n} 1 / a_k$. Then for every $n$ with $a_n \ge 8 (\beta + 1/3)^2$ we have
$a_n = \lfloor x_n^{-1} + \beta + 1/2 \rfloor$, that is, $a_n$ is the integer nearest to
$x_n^{-1} + \beta$, with halves rounded up. Moreover, if $a_n^2 / a_{n+1} \to \beta$, then
$|x_n^{-1} + \beta - a_n| \to 0$.

## Sources

- Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential Sequences*, INTEGERS 26 (2026), Article A28, Theorem 1 (`integers-2026-A28-thm-1`).
