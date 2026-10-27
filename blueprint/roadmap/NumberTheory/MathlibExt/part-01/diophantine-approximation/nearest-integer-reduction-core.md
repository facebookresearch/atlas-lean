---
article_id: af_cd06ef0766b1d54ec9764105
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.nearestInteger_reduction_core
---

# Baker Davenport Nearest Integer Core

Nearest-integer Baker–Davenport reduction core: a named reusable arithmetic
prerequisite stage extracted from Lemma `bd` (lines 285--292) of Eric F. Bravo,
Carlos A. Gómez, and Florian Luca, "Product of Consecutive Tribonacci Numbers
With Only One Distinct Digit", Journal of Integer Sequences 22 (2019),
Article 19.6.3.

Source URL `https://cs.uwaterloo.ca/journals/JIS/VOL22/Gomez/gomez3.tex`,
source-file SHA-256
`06ab2807874c97cf44007c561d48576611214b0fa0ab6ed55c61470d8ba7c0e6`,
exact span SHA-256
`cc488ea946e7229300ad0b1a00befe1e523c8a5b97331a1d79e04c8f40429fe4`.
Task `jis_rank27_nearest_integer_reduction_core`,
semantic id `jis_grounded_3d649f47290c78b9a73677c9`.

Scope: the printed lemma defines nearest-integer distance by
`‖x‖ = |x - round x|` and `ε := ‖μq‖ - M‖κq‖`; this stage records the
reverse-triangle inequality used by the reduction argument. It does not claim
to formalize the full lemma. The source's irrationality, continued-fraction,
`q > 6M`, and logarithmic hypotheses belong to the later wrapper and are
deliberately omitted from this arithmetic stage, as are the source's
`0 < q` and `0 < ε`, which the inequality does not need. The explicit `heq` equality
hypothesis is necessary: a prior default-valued epsilon binder did not assert
the definition and made the statement false.
Proves `Wanted` entry `nearestInteger_reduction_core`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.DiophantineApproximation.BakerDavenportNearestIntegerCore](../../../../../sources/v2/MathlibExt.md)
