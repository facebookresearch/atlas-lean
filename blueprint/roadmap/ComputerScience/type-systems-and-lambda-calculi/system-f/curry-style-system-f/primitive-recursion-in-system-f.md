# Primitive recursion in System F

For a System F type $\sigma$, let

$$r_\sigma = \lambda y{:}\sigma.\, \lambda f{:}\sigma \to \omega \to \sigma.\, \lambda n{:}\omega.\, \pi_1\big(n\, (\sigma \wedge \omega)\, (\lambda v.\, \langle f\, (\pi_1 v)\, (\pi_2 v),\ \mathrm{succ}\, (\pi_2 v) \rangle)\, \langle y, c_0 \rangle\big)$$

with the [definable products, numerals and successor](definable-connectives-and-data-types-in-system-f.md). Then $r_\sigma\, M\, N\, c_0 =_\beta M$ and
$r_\sigma\, M\, N\, (\mathrm{succ}\, c_n) =_\beta N\, (r_\sigma\, M\, N\, c_n)\, c_n$ for every Church numeral $c_n$, so a recursor with the equations of Gödel's System T on
numerals is definable in System F. Here the step function takes the recursive value before the predecessor, the order of the source; the recursor of
[the System T pages](../../system-t/godel-s-system-t.md), with $\mathrm{R}\, u\, v\, (\mathrm{S}\, t) \to v\, t\, (\mathrm{R}\, u\, v\, t)$, takes them in the other order and is $\lambda y\, g.\, r_\sigma\, y\, (\lambda a\, b.\, g\, b\, a)$.

## Depends on

- [Definable connectives and data types in System F](definable-connectives-and-data-types-in-system-f.md)
- [Gödel's System T](../../system-t/godel-s-system-t.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 12.4, Proposition 12.4.4 (proof left as Exercise 12.7.8) and the sentence before it.
