# Complete asymptotic expansion of Watson's alternating cosecant sum

For natural numbers $N$
and $n$ let $C_n = \sum_{l=1}^{n-1} (-1)^{l+1} / \sin(\pi l / n)$ and

$$
M_N(n) = \frac{2 n \log 2}{\pi} + 2 \sum_{r=1}^{N-1}
\frac{(-1)^{r+1} (2^{2r-1} - 1)(2^{2r} - 1) \pi^{2r-1} B_{2r}^2}{r \, (2r)! \, n^{2r-1}},
$$

where $B_{2r}$ is the $2r$-th Bernoulli number. For every $N \ge 2$ there is a real constant
$K \ge 0$ such that for every even $n \ge 2$,

$$
|C_n - M_N(n)| \le \frac{K}{n^{2N-1}}.
$$

In other words, $C_n = M_N(n) + O(n^{1-2N})$ as $n \to \infty$ through even values.

## Sources

- Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 2.
