# Explicit estimate for the reciprocal sum of the semiprimes

A semiprime is a product of
exactly two primes counted with multiplicity; for real $x$ let $S(x)$ be the sum of $1/n$ over the
semiprimes $n \le x$. Let $\beta$ be the Meissel–Mertens constant, $\gamma$ the Euler–Mascheroni
constant and $\log$ the natural logarithm, and put

$$
P(2) = \sum_{p} \frac{1}{p^2}, \qquad \zeta(2) = \frac{\pi^2}{6}, \qquad
\alpha_1 = \gamma + \sum_{p} \frac{\log p}{p (p - 1)},
$$

the sums running over all primes $p$. Then for every real $x > 1$ the error

$$
E(x) = S(x) - \frac{(\log \log x + \beta)^2}{2} - \frac{P(2) - \zeta(2)}{2} -
\frac{\alpha_1}{\log x}
$$

satisfies $|E(x)| < (\log x)^{-3/2}$.

## Sources

- Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*, INTEGERS 24 (2024), Article A99, Lemma 2 (quoting Bayless et al.).
