---
article_id: af_2df697f9ddc511fa00120ebe
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.spherical_law_of_cosines
---

# Spherical law of cosines

Spherical law of cosines: a spherical triangle on the unit sphere
with side lengths `a`, `b`, `c` and spherical angle `C` opposite side `c`
satisfies `cos c = cos a * cos b + sin a * sin b * cos C`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Spherical law of cosines general](spherical-law-of-cosines-general.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Spherical.SphericalLawOfCosines](../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Spherical_law_of_cosines (statement `spherical-cosines-s1`). It follows from `spherical_law_of_cosines_general`; the hypotheses `hc` and `hC` are unused and keep the source's shape. Proves `Wanted` entry `spherical_law_of_cosines`.
