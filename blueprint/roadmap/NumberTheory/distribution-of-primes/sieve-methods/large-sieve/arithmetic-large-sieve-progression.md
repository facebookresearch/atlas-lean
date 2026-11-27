# Arithmetic large sieve for primes in a progression

Let $N$, $z$, $q$ and $a$ be natural
numbers with $z > 0$ and $q > 0$, and let $S$ be a finite set of natural numbers less than $N$
such that for every $n \in S$ the number $qn + a$ is prime and greater than $z$. Write $\mu$ for
the Möbius function and $\varphi$ for Euler's totient function. Then

$$
\left(\sum_{r=1}^{z} \frac{\mu(r)^2}{\varphi(r)\,(N + 3rz/2)}\right) |S|^2
\le \frac{q}{\varphi(q)}\,|S|.
$$

## Sources

- Montgomery–Vaughan, *The large sieve* (1973), Corollary 1 and Lemma 3, equations (2.7) and (3.2), lines 322–461. The Farey fractions are weighted by the denominator-dependent spacing from `weightedLargeSieve`.
