---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.wolstenholme_harmonic_power_sum
---

# Wolstenholme Power Sums

For odd `ν ≥ 1` and prime `p ≥ ν + 4`, the `ν`-th harmonic power sum through
`p - 1` vanishes modulo `p²`. Inverses are taken in `ZMod (p ^ 2)`, where every
`t < p` is a unit.

The source notes there (lines 108–111) that this is Theorem 131 of Hardy and
Wright, a generalization of the 1862 Wolstenholme congruence, first studied by
Leudesdorf.
Proves `Wanted` entry `wolstenholme_harmonic_power_sum`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.WolstenholmePowerSums](../../../../sources/v2/MathlibExt.md)
- Christian Ballot, "On a Congruence of Kimball and Webb Involving Lucas Sequences," Journal of Integer Sequences 17 (2014), Article 14.1.3, Theorem (label thm:L), lines 94–99, https://cs.uwaterloo.ca/journals/JIS/VOL17/Ballot/ballot7.tex
