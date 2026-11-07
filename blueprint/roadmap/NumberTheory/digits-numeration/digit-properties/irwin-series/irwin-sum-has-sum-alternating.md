# Alternating series for the Irwin sum

Let $b > 1$ and $d < b$ be natural numbers, let
$(u_{j;m})_{j, m \in \mathbb{N}}$ be a family of real numbers satisfying the ordinary moment
recurrence for $b$ and $d$, and let $k$ and $l \ge 1$ be natural numbers. For a natural number
$n$ write $c(n)$ for the number of occurrences of the digit $d$ in the base-$b$ expansion of $n$,
and let $H^{(k)}_{b,d}$ be the Irwin sum, the sum of $1/n$ over the positive integers $n$ with
$c(n) = k$. Then the family of real numbers indexed by $m \ge 1$

$$
(-1)^m \sum_{\substack{b^{l-1} \le n < b^l \\ c(n) \le k}} \frac{u_{k - c(n);m}}{n^{m+1}}
$$

is summable, with sum

$$
H^{(k)}_{b,d} - \sum_{\substack{1 \le n < b^{l-1} \\ c(n) = k}} \frac{1}{n} -
b \sum_{\substack{b^{l-1} \le n < b^l \\ c(n) \le k}} \frac{1}{n}.
$$

## Sources

- Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Theorem 1.
