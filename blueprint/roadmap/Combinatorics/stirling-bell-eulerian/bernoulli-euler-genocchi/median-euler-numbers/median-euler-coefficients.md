# The list of the first Euler coefficients

Let $\varepsilon_N$ be $1$ if $N$ is odd and $0$
if $N$ is even. For each natural number $n$, this is the list $[c_0, c_1, \dots, c_n]$ of integers
with $c_0 = 1$ and, for $1 \le N \le n$, $c_N = \varepsilon_N - \sum_j \binom{N}{j} c_{N-j}$, where
the sum runs over the even $j$ with $2 \le j \le N$. The Euler coefficient $E_n$ is its last entry
$c_n$. The list is built one entry at a time, so each step reuses the earlier values.

The recurrence comes from $\cosh x \cdot (\operatorname{sech} x + \tanh x) = 1 + \sinh x$.
