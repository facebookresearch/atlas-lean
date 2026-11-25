# Rational form of the power-weighted geometric sum

For positive integers $t$ and $k$,
the following identity holds in $\mathbb{Z}[X]$:

$$(1 - X)^{t+1} \sum_{n=1}^{k} n^t X^n =
\sum_{n=1}^{t} \Bigl(\sum_{i=0}^{n-1} (-1)^i \binom{t+1}{i} (n - i)^t\Bigr) X^n +
\sum_{m=1}^{t+1} \Bigl(\sum_{i=m}^{t+1} (-1)^i \binom{t+1}{i} (k + m - i)^t\Bigr) X^{k+m}.$$

Equivalently, for every $x \ne 1$ the value $h_t^k(x) = \sum_{n=1}^{k} n^t x^n$ is the
right-hand side at $x$ divided by $(1 - x)^{t+1}$, which is the form the source states.

## Sources

- Chandan Kumar Vishwakarma and Rajesh P. Singh, *A Congruence Identity on Ordered Partitions Using Permutation Polynomials*, INTEGERS 24 (2024), Article A12, Lemma 4.
