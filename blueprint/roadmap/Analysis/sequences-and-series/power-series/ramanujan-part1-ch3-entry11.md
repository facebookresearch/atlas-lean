# Recurrence for the coefficients of $e^{f(x)}$

Let $(A_k)_{k \ge 1}$ and $(p_n)_{n \ge 0}$
be sequences of real numbers, let $R > 0$, and let $f : \mathbb{R} \to \mathbb{R}$. Suppose that
for every real $x$ with $|x| < R$ the series $\sum_{k \ge 1} A_k x^k / k$ is summable with sum
$f(x)$ and the series $\sum_{n \ge 0} p_n x^n$ is summable with sum $e^{f(x)}$. Then for every
integer $n \ge 1$,

$$n p_n = \sum_{k=1}^{n} A_k p_{n-k}.$$

## Sources

- Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 11, printed p. 66 / PDF p. 76. Proves `Wanted` entry `ramanujan_part1_ch3_entry11`.
