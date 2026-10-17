---
article_id: af_a932aad691eb119e2679bed1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.puiseux_theorem
---

# Puiseux theorem

Puiseux's theorem (https://en.wikipedia.org/wiki/Puiseux_series):
The set of Puiseux series over an algebraically closed field of characteristic
zero is itself an algebraically closed field (the field of Puiseux series).
Puiseux series are modelled as `HahnSeries Rat K`. The Puiseux field is carried
as the bounded-denominator subfield of `HahnSeries Rat K` (the union over `n`
of `K((t ^ (1 / n)))`, i.e. each series has support denominators dividing some
`n` depending on the series), and it is the algebraic closure of the field of
formal Laurent series, which itself is the field of fractions of the ring of
formal power series.

Proof: Newton polygon plus Hensel lifting, first in the rational Hahn field and
then with the ramification bounded inside a power-series level.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Alg Closed rat](is-alg-closed-rat.md)
- [Exists monic coprime factorization of is Adic Complete nat Degree](../../../NumberTheory/MathlibExt/part-06/hensel-factorization/exists-monic-coprime-factorization-of-is-2.md)

## Sources

- [MathlibExt, MathlibExt.FieldTheory.PuiseuxTheorem](../../../../sources/v2/MathlibExt.md)
