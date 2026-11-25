# Rabin's 1/4 bound for strong pseudoprimes

Let $n > 1$ be odd and not prime. Then $n$ is a
[strong pseudoprime](../../../NumberTheory/primes-primality/primality-tests-pseudoprimes/strong-pseudoprimes/is-strong-pseudoprime.md) to at most $\lfloor (n - 1)/4 \rfloor$ of the
bases $a = 1, \dots, n - 1$: writing $n - 1 = 2^t u$ with $u$ odd, at most $\lfloor (n - 1)/4 \rfloor$
of these $a$ satisfy $a^u \equiv 1$ or $a^{2^i u} \equiv -1 \pmod n$ for some $i < t$. So one
uniformly random base exposes $n$ as composite with probability at least $3/4$.

## Comparison with the source

Rabin's Theorem 1 (p. 130) states that for every composite $n > 4$ at least $3(n - 1)/4$ of the
$1 \le b < n$ are witnesses $W_n(b)$, where $W_n(b)$ means $b^{n-1} \not\equiv 1 \pmod n$ or
$1 < \gcd(b^{(n-1)/2^i} - 1, n) < n$ for some $2^i \mid n - 1$. The note added on 10 May 1978
(p. 137) deduces from it the Proposition stated above: for odd composite $n > 4$, at least
$3(n - 1)/4$ of the $1 \le x < n$ have $x_l \ne 1$ or, for some $i$, $x_i = 1$ with
$x_{i-1} \ne n - 1$, where $x_0 = x^m \bmod n$, $x_i = x_{i-1}^2 \bmod n$ and $n - 1 = 2^l m$.
The proof of the Proposition chooses $i - 1$ as the last index with $x_{i-1} \ne 1$, so it
establishes the condition with $x_{i-1} \notin \{1, n - 1\}$ as well; that is the condition whose
negation defines strong pseudoprimes, and the one counted here.

- The statement covers odd $n$ only. Rabin's Theorem 1 also covers even composite $n > 4$ for his
  gcd-based witnesses.
- The integer bound $\lfloor (n - 1)/4 \rfloor$ is equivalent to Rabin's real bound, since the
  count is an integer.
- The constant $1/4$ is attained: for $n = 9$ exactly $2$ of the $8$ bases $1, \dots, 8$ (namely $1$ and $8$) are non-witnesses. For a
  Carmichael number $n = pqr$ with
  $p \equiv q \equiv r \equiv 3 \pmod 4$, exactly $\tfrac34 \varphi(n)$ of the units are witnesses
  (p. 133), and Rabin lists $652969351 = 271 \cdot 811 \cdot 2971$, with a witness fraction of
  $0.7513$.

## Informally uses

- [At most a quarter of the bases are non-witnesses](card-nonwitnesses-le-quarter.md): the bound
  for the bases on which the test procedure finds no witness.
- [Miller–Rabin non-witnesses are exactly the bases to which n is a strong pseudoprime](is-strong-pseudoprime-iff-witness-eq-fal.md):
  translates that bound into the language of strong pseudoprimes.

## Background

- [Monier's formula for the number of strong pseudoprime bases](../../../NumberTheory/primes-primality/primality-tests-pseudoprimes/strong-pseudoprimes/card-strong-pseudoprime-bases.md):
  the exact count, from which the $1/4$ bound can also be read off.

## Sources

- M. O. Rabin, *Probabilistic algorithm for testing primality*, Journal of Number Theory 12 (1980), 128–138: Theorem 1 (p. 130), the Carmichael example (p. 133) and the Proposition in the
  note added on 10 May 1978 (p. 137).
- L. Monier, *Evaluation and comparison of two efficient probabilistic primality testing
  algorithms*, Theoretical Computer Science 12 (1980), 97–108, proved the same bound
  independently. This attribution is taken from secondary sources; the paper was not consulted.
