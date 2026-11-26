# Generating function of the $L^\ast$-block-sum counts

Let $L = (e_1, \dots, e_N)$ be a
list of natural numbers with $N \ge 2$ and $e_1 \ne 0$. For each $k$ let $C_k$ be the number of
coefficient functions that are sums of disjoint proper $L^*$-blocks with support intervals inside
$[1, k]$ (the zero function included), and put
$f(x) = 1 - \sum_{k=1}^{N-1} e_k x^k - (1 + e_N) x^N$. Then there is a real $r > 0$ such that for
every real $x$ with $-r < x < r$ the series $\sum_{k \ge 0} C_k x^k$ converges absolutely, with
sum $(1 - x^N) / f(x)$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Proposition 5 (arXiv:2308.12872v1, Section 4.1).
