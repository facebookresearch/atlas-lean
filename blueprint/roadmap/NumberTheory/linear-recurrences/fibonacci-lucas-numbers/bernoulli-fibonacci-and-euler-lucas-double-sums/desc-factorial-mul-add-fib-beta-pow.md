# Derivatives of the Bernoulli–Fibonacci expansion of $(x + \beta)^m$

Let
$\beta = (1 - \sqrt{5})/2$, let $B_k$ be the Bernoulli numbers with $B_1 = -1/2$, let $F_k$ be the
Fibonacci numbers, and write $a^{\underline{s}} = a(a-1)\cdots(a-s+1)$ for the falling factorial.
Then for all natural numbers $s \le m$ and every real number $x$,

$$
m^{\underline{s}} (x + \beta)^{m-s} = \sum_{n=0}^{m} \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k}
\binom{m}{n} B_k \frac{F_{n-k+1}}{n-k+1} (m-n)^{\underline{s}} x^{m-n-s},
$$

where the terms with $m - n < s$ are $0$ because $(m-n)^{\underline{s}} = 0$ there.

This is the paper's Corollary 4, obtained by differentiating Theorem 1 $s$ times; the printed
falling factorial of $m - n + 1$ is off by one, and the identity is written here multiplied
through by $m^{\underline{s}}$.

## Sources

- Fatima Zohra Bensaci, Rachid Boumahdi, and Laala Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers", Corollary 4.
