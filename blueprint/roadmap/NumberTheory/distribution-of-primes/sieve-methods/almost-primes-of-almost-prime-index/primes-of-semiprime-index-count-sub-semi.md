# Primes of semiprime index eventually outnumber semiprimes of prime index

A semiprime is
a product of exactly two primes counted with multiplicity. Let $p_i$ denote the $i$th prime
($p_1 = 2$) and $s_i$ the $i$th semiprime ($s_1 = 4$). For real $x$ let $N_{1,2}(x)$ be the number
of primes $p_i \le x$ whose index $i$ is a semiprime, and $N_{2,1}(x)$ the number of semiprimes
$s_i \le x$ whose index $i$ is prime. Then $N_{2,1}(x) < N_{1,2}(x)$ for all sufficiently large
$x$, and, with $\log$ the natural logarithm, as $x \to \infty$

$$
N_{1,2}(x) - N_{2,1}(x) = \frac{x \log \log x \, \log \log \log x}{\log^3 x} +
O\left( \frac{x \log \log x}{\log^3 x} \right).
$$

This is the form
$\frac{x \log \log x \, \log \log \log x}{\log^3 x} (1 + O(1 / \log \log \log x))$ with the main
factor multiplied out.

## Sources

- Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*, INTEGERS 24 (2024), Article A99, Corollary 1 (`integers-2024-A99-cor-1`).
