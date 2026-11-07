# Counting primes of semiprime index

A semiprime is a product of exactly two primes counted
with multiplicity. Let $p_i$ denote the $i$th prime ($p_1 = 2$), and for real $x$ let $N_{1,2}(x)$
be the number of primes $p_i \le x$ whose index $i$ is a semiprime. Let $\beta$ be the
Meissel–Mertens constant, $\gamma$ the Euler–Mascheroni constant, $\log$ the natural logarithm, and

$$
c_1 = \beta - 1 - \gamma - \sum_{p} \frac{\log p}{p (p - 1)},
$$

the sum running over all primes $p$. Then, as $x \to \infty$,

$$
N_{1,2}(x) = \frac{x}{\log^2 x} \left( \log \log x + \beta +
\frac{(\log \log x + \beta)(\log \log x + 1) + c_1}{\log x} \right) +
O\left( \frac{x (\log \log x)^3}{\log^4 x} \right).
$$

## Sources

- Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*, INTEGERS 24 (2024), Article A99, Theorem 1 (`integers-2024-A99-thm-1`).
