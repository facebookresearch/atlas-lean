# Shapley weight

For $n$ players and a coalition size $1 \le s \le n$, the Shapley weight is

$$w(n, s) = \frac{(s - 1)!\,(n - s)!}{n!}.$$

The same expression defines $w(n, s)$ for all natural numbers $n$ and $s$, with truncated
subtraction: $(s - 1)! = 0! = 1$ when $s = 0$ and $(n - s)! = 0! = 1$ when $s \ge n$; for example
$w(n, 0) = 1$.

In a uniformly random order of the $n$ players, it is the probability that a given player $i$
arrives just after the other members of a given coalition $S \ni i$ of size $s$, so that the
players up to and including $i$ form exactly $S$.

## Sources

- R. Serrano, "Cooperative games: core and Shapley value", CEMFI Working Paper 0709 (2007), §4.1, coefficient in the formula for $Sh_i(N, v)$ (secondary source).
