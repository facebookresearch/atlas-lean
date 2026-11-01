---
article_id: af_acd420effff28a64a8776be9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.TranscendenceWanted.gelfondSchneider_real_rpow
---

# Gelfond Schneider real rpow

`Real.rpow` specialization of Gelfond–Schneider: if `α β : ℝ` satisfy `0 < α`, `α ≠ 1`,
`IsAlgebraic ℚ α`, `IsAlgebraic ℚ β` and `Irrational β`, then `Real.rpow α β` is transcendental
over `ℚ`. Source: A. O. Gelfond, Sur le septième problème de Hilbert, Dokl. Akad. Nauk SSSR 2
(1934) 1–6 and T. Schneider 1935 independent; textbook in Baker, Transcendental Number Theory

## Depends on

This node has no prerequisites.

## Proof depends on

- [Gelfond Schneider complex exp](gelfond-schneider-complex-exp.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.GelfondSchneider](../../../../../sources/v2/MathlibExt.md)
