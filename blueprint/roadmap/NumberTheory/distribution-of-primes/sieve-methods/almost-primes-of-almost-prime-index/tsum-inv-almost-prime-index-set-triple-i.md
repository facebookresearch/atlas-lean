# Exponential decay of reciprocal sums over triple almost prime index sets

A $k$-almost
prime is a positive integer with exactly $k$ prime factors counted with multiplicity. For positive
integers $a$ and $b$ let $N_{ab}$ be the set of $a$-almost primes whose index in the increasing
enumeration of the $a$-almost primes (starting at $1$) is a $b$-almost prime, and for positive
integers $k_1, k_2, k$ let $N_{k_1 k_2 k}$ be the set of $k_1$-almost primes whose index in the
increasing enumeration of the $k_1$-almost primes lies in $N_{k_2 k}$. Fix positive integers $k_1$
and $k_2$. Then, as $k \to \infty$,

$$
\sum_{n \in N_{k_1 k_2 k}} \frac{1}{n} = O\left( e^{-k/2} \right).
$$

This is the case $m = 2$ of the paper's bound $\ll (e^{k/2})^{-(m-1)}$ for the reciprocal sum of
$N_{k_1 \cdots k_m k}$, the only case its proof supports. For $m = 3$ and $k_1 = k_2 = k_3 = 1$,
with $p_n$ the $n$th prime, the single term $1/p_{p_{p_{2^k}}}$ is $\gg 2^{-k} k^{-3}$ because
$p_n < n (\log n + \log \log n)$ for $n \ge 6$, and $e^{k} 2^{-k} k^{-3} \to \infty$, so the
printed bound fails for $m = 3$.

## Sources

- Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*, INTEGERS 24 (2024), Article A99, Theorem 9, case `m = 2` (`integers-2024-A99-thm-9`).
