# Shor's order-to-factor reduction

Let $N$, $a$ and $r$ be natural numbers with $N > 1$ and
$a \ge 1$. Suppose $a^r \equiv 1 \pmod{N}$, $r$ is even, $a^{r/2} \not\equiv 1 \pmod{N}$ and
$a^{r/2} \not\equiv -1 \pmod{N}$. Then $d = \gcd(a^{r/2} - 1, N)$, the value computed by the
classical post-processing, is a nontrivial factor of $N$: $d$ divides $N$ and $1 < d < N$.

In the algorithm $r$ is the multiplicative order of $a$ modulo $N$, so the hypothesis
$a^{r/2} \not\equiv 1 \pmod{N}$ is the minimality of the order, and the hypothesis
$a^{r/2} \not\equiv -1 \pmod{N}$ is the "good unit" condition. This module assumes that
condition; it does not prove its prevalence among units.

## Sources

- P. W. Shor, Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer, SIAM J. Comput. 26 (1997), 1484–1509, Section 5; M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge University Press, 2000, Section 5.3.
