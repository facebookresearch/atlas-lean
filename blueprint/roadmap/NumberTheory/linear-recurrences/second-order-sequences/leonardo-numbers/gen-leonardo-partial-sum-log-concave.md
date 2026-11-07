# Log-concavity of partial sums of generalized Leonardo numbers

Let $k \ge 1$ be an
integer, let $L_{k,n}$ be the generalized Leonardo numbers, and let
$R_n = \sum_{i=0}^{n} L_{k,i}$. Then $R_{n-1} R_{n+1} \le R_n^2$ for every integer $n \ge 2$.

The inequality fails at $n = 1$: there $R_0 = 1$, $R_1 = 2$ and $R_2 = k + 4$, so
$R_1^2 - R_0 R_2 = -k < 0$. The paper states it for every $n \ge 1$, although its identity
$R_n^2 - R_{n-1} R_{n+1} = (k+1)^2 (F_n + (-1)^n) + k(k+1)(n F_n - 2 F_{n+1}) + k^2$, with
$F_n$ the Fibonacci numbers, gives the same value $-k$ at $n = 1$.

## Sources

- Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 2.
