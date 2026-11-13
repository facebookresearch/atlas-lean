# Chowla's conjecture over $\mathbb{F}_q(T)$ for large $q$

Let $p$ be an odd prime, let $k \ge 1$
be a natural number, and let $q$ be a power of $p$ with $q > p^2 k^2 e^2$, where $e$ is Euler's
number; write $\mathbb{F}_q$ for the finite field with $q$ elements. Let
$h_1, \dots, h_k \in \mathbb{F}_q[T]$ be distinct polynomials. Then, as the real number $X$ tends
to $\infty$,

$$\sum_{f \text{ monic},\ |f| \le X} \mu(f + h_1)\,\mu(f + h_2) \cdots \mu(f + h_k) = o(X),$$

where the sum runs over the monic $f \in \mathbb{F}_q[T]$ of norm $|f| = |\mathbb{F}_q[T]/(f)|$ at
most $X$, and $\mu$ is the Möbius function of $\mathbb{F}_q[T]$: $\mu(g) = (-1)^r$ if $g$ is
squarefree with $r$ irreducible factors, and $\mu(g) = 0$ otherwise.

## Sources

- W. Sawin and M. Shusterman, `On the Chowla and twin primes conjectures over 𝔽_q[T]`, Annals of Math, 196 (2) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_chowla_and_twin_prime_over_fq_t` of the lean-eval benchmark.
