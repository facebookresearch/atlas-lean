# Polynomial Fermat congruence characterizes primes

Let $n \ge 2$ and let $a$ be an integer with $\gcd(a, n) = 1$. Then $n$ is prime if and only if

$$
(X + a)^n \equiv X^n + a \pmod{n}
$$

as polynomials in $\mathbb{Z}[X]$, that is, all coefficients of $(X+a)^n - X^n - a$ are divisible by $n$.

## Proof sketch

The coefficient of $X^i$ for $0 < i < n$ is $\binom{n}{i} a^{n-i}$. If $n$ is prime these binomials vanish mod $n$ and $a^n \equiv a$ by Fermat. If $q^k \parallel n$ for a prime $q < n$, then $q^k \nmid \binom{n}{q}$ and $q \nmid a$, so the coefficient of $X^q$ is nonzero mod $n$.

## Depends on

- [The primality decision problem](../../../TheoryOfComputation/polynomial-time-problems/aks-primality-test/primes-dec.md)

## Sources

- M. Agrawal, N. Kayal and N. Saxena, "PRIMES is in P", Annals of Mathematics 160(2), 2004.
- G. H. Hardy and E. M. Wright, "An Introduction to the Theory of Numbers", 6th ed., Oxford University Press, 2008.
