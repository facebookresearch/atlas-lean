# Converting a lower bound for $\pi(x)$ into a truncated series

Let $\pi(x)$ be the number
of primes $p \le x$. Let $n \ge 1$ be an integer, let $a_0, \dots, a_n$ be reals with $a_0 > 0$
and $a_1, \dots, a_n < 0$, and let $x_0 > 0$. Suppose that for every real $x \ge x_0$ the
denominator $D(x) = a_0 \log x + \sum_{i=1}^{n} a_i / \log^{i-1} x$ is positive and
$\pi(x) > x / D(x)$. Let $b_0 = 1/a_0$ and $b_k = -\frac{1}{a_0} \sum_{i=1}^{k} a_i b_{k-i}$ for
$1 \le k \le n$. Then for every real $x \ge x_0$,
$\pi(x) > \sum_{k=0}^{n} \frac{b_k x}{\log^{k+1} x}$.

The recursion uses $b_{k-i}$, the index of the paper's proof: it turns the first row of Table 5
into the Table 6 coefficients $1, 1, 2, 5.975666, 23.975666, \dots$. The source record of the
statement prints $b_{k-1}$ instead, which would give $b_3 = 9.951332$ there.

## Sources

- Christian Axler, *Effective Estimates for Some Functions Defined over Primes*, INTEGERS 24 (2024), Article A34, Proposition 6.
