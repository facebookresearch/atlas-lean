# Primitive recursion in System F

For a System F type $\sigma$, let
$$r_\sigma = \lambda y{:}\sigma.\, \lambda f{:}\sigma \to \omega \to \sigma.\, \lambda n{:}\omega.\, \pi_1\big(n\, (\sigma \wedge \omega)\, (\lambda v.\, \langle f\, (\pi_1 v)\, (\pi_2 v),\ \mathrm{succ}\, (\pi_2 v) \rangle)\, \langle y, c_0 \rangle\big)$$
with the [definable products, numerals and successor](definable-connectives-and-data-types-in-system-f.md). Then $r_\sigma\, M\, N\, c_0 =_\beta M$ and
$r_\sigma\, M\, N\, (\mathrm{succ}\, c_n) =_\beta N\, (r_\sigma\, M\, N\, c_n)\, c_n$ for every Church numeral $c_n$, so the recursor of Gödel's System T, with its equations on
numerals, is definable in System F.

## Depends on

- [Definable connectives and data types in System F](definable-connectives-and-data-types-in-system-f.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 12.4, Proposition 12.4.4 (proof left as Exercise 12.7.8) and the sentence before it.
