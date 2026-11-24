# Miller–Rabin non-witnesses are exactly the bases to which n is a strong pseudoprime

Let $n > 1$ be odd and not prime, and let $a$ be any natural number. Then $n$ is a
[strong pseudoprime](../../../NumberTheory/primes-primality/primality-tests-pseudoprimes/strong-pseudoprimes/is-strong-pseudoprime.md) to the base $a \bmod n$ if and only if the
[Miller–Rabin witness test](witness.md) applied to $a$ and $n$ reports no witness.

The two sides are two definitions of the same notion, one number-theoretic (congruences on
$a^u, a^{2u}, \dots$ in $\mathbb{Z}/n\mathbb{Z}$) and one algorithmic (the squaring loop on
residues). No range condition on $a$ is needed, since both sides depend only on $a \bmod n$. The
uniqueness of the decomposition $n - 1 = 2^t u$ with $u$ odd matches the existential in the
[definition of strong pseudoprimes](../../../NumberTheory/primes-primality/primality-tests-pseudoprimes/strong-pseudoprimes/is-strong-pseudoprime-iff.md) with the split computed by the test.

## Informally uses

- [The Miller–Rabin non-witnesses, by congruences](witness-eq-false-iff.md): the characterisation
  of the test's answer that is compared with the definition.

## Sources

- M. O. Rabin, *Probabilistic algorithm for testing primality*, Journal of Number Theory 12 (1980), 128–138, note added on 10 May 1978 (p. 137): the squaring chain $x_0, \dots, x_l$ that the
  witness test computes.
- S. S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024), Article A23,
  Section 1, Congruences (2) and (3) (the definition of strong pseudoprimes).
