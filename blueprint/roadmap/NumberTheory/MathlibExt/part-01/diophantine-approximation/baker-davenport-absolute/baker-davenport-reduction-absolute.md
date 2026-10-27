---
article_id: af_426cda306aea4aae258c2dce
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bakerDavenport_reduction_absolute
---

# Baker Davenport reduction absolute

Absolute-value Baker–Davenport reduction lemma.

Concept `baker_davenport_reduction_absolute`, semantic id
`jis_grounded_3d649f47290c78b9a73677c9`.

Here `|x - round x|` formalizes distance to the nearest integer, and this
declaration is the absolute-value variant of the cited lemma: the final linear
form `(r : ℝ) * kappa - (s : ℝ) + mu` appears inside absolute-value bars with
a two-sided strict inequality.
It follows from `bakerDavenport_reduction_absolute_general`. The hypotheses `hM`,
`hkappa`, `j` and `hq`, and the positivity conditions on `r`, `s`, `w` and the linear form,
are unused and keep the source's shape; `hqM` only supplies `0 < q`.
Proves `Wanted` entry `bakerDavenport_reduction_absolute`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Baker Davenport reduction absolute general](baker-davenport-reduction-absolute-gener.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.DiophantineApproximation.BakerDavenportAbsolute](../../../../../../sources/v2/MathlibExt.md)
- Eric F. Bravo, Carlos A. Gomez, and Florian Luca, "Product of Consecutive Tribonacci Numbers With Only One Distinct Digit," Journal of Integer Sequences 22 (2019), Article 19.6.3, Lemma `bd`, lines 285–292. Source URL `https://cs.uwaterloo.ca/journals/JIS/VOL22/Gomez/gomez3.tex`. Source-file SHA-256 `06ab2807874c97cf44007c561d48576611214b0fa0ab6ed55c61470d8ba7c0e6`; exact-span SHA-256 `cc488ea946e7229300ad0b1a00befe1e523c8a5b97331a1d79e04c8f40429fe4`.
