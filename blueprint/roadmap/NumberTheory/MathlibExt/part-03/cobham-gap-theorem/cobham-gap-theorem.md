---
article_id: af_ba1b48e2e22ad3669b5b76a0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.cobham_gap_theorem
---

# Cobham gap theorem

Cobham's gap theorem: for a strictly monotone enumeration `x` of a
`k`-recognizable set of naturals, either the limsup of the consecutive ratios
`x (i+1) / x i` (in `ENNReal`, so an unbounded limsup is `⊤`) exceeds `1`,
or the consecutive gaps `x (i+1) - x i` are uniformly bounded.

## Depends on

- [Is Base Recognizable](../base-recognizable/is-base-recognizable.md)

## Proof depends on

- [Cobham gap theorem general](cobham-gap-theorem-general.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.CobhamGapTheorem](../../../../../sources/v2/MathlibExt.md)
- Kärki–Lacroix–Rigo gap theorem, lines 979–995 of <https://cs.uwaterloo.ca/journals/JIS/VOL13/Rigo/rigo6.tex>.
