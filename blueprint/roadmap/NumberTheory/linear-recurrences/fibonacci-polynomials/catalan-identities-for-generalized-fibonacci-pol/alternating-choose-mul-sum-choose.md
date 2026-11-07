# Alternating sum of binomial row sums

For all natural numbers $\ell$ and $n$,

$$\sum_{i=0}^{n} (-1)^i \binom{\ell}{i} \sum_{j=0}^{n-i} \binom{n-i}{j}
  = \sum_{i=0}^{n} (-1)^i \binom{i+\ell-n-1}{i},$$

where on the right $\binom{a}{i} = a(a-1)\cdots(a-i+1)/i!$ is the binomial coefficient with
integer upper index $a$. For $n < \ell$ the upper index $i + \ell - n - 1$ is nonnegative and this
is the ordinary binomial coefficient, the case used in Theorem 4.4.

## Sources

- Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas, *Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article florez11012023, Lemma 4.3 (`fq-2024-florez11012023-lem-4.3`).
