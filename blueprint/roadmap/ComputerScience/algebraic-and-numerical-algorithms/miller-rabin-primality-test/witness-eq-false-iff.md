# The Miller–Rabin non-witnesses, by congruences

Let $n > 2$ and write $n - 1 = 2^t u$ with $u$ odd. For every natural number $a$, the
[Miller–Rabin witness test](witness.md) reports no witness if and only if
$a^u \equiv 1 \pmod n$ or $a^{2^i u} \equiv -1 \pmod n$ for some $i < t$.

In Rabin's notation ($x_0 = a^u \bmod n$ and $x_i = x_{i-1}^2 \bmod n$), these are the bases whose
squaring chain reaches $1$ either from the start or through the value $n - 1$; the hypothesis
$n > 2$ excludes $n - 1 = 1$.

## Informally uses

- [What a non-witness satisfies](witness-eq-false-imp.md): the forward direction.
- [Converse for the squaring loop](witness-loop-eq-false-of.md): the converse direction for the loop.

## Sources

- M. O. Rabin, *Probabilistic algorithm for testing primality*, Journal of Number Theory 12 (1980), 128–138, note added on 10 May 1978 (p. 137).
