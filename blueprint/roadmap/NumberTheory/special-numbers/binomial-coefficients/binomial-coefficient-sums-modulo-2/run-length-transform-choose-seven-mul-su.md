# Rampersad–Wiebe Theorem 12

Let $(p_j)_{j \ge 0}$ be the shifted Padovan sequence,
$p_0 = 1$, $p_1 = 0$, $p_2 = 1$ and $p_{j+3} = p_{j+1} + p_j$, and let $T$ be the run length
transform of $S(i) = p_{i+2}$, i.e. of $1, 1, 1, 2, 2, 3, 4, 5, \dots$ (the Padovan numbers,
OEIS A000931, from offset $5$). Then for every natural number $n$,
$\sum_{k=0}^{n} \left(\binom{7k - n}{n + k} \binom{n}{k} \bmod 2\right) = T(n)$, where a binomial
coefficient $\binom{a}{b}$ with $a < 0$ is $0$.

Equivalently, a negative top entry $7k - n$ may be replaced by $0$, since the bottom entry $n + k$
is then positive.

## Sources

- Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Theorem 12.
