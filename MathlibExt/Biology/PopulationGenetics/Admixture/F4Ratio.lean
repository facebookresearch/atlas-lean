/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatistics
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Bias of the f4-ratio estimator under misspecification

The correctly specified f4-ratio theorem is
`FStatistics.DriftModel.f4_ratio`. This file records what happens without
that theorem's f4-equality hypothesis
`f4(A, O; Y, C) = f4(A, O; B, C)`. In applications this equality is supplied
by a sister relationship between the unsampled source `Y` and sampled
reference `B`, but `DriftModel` has no topology or sister predicate: the
results below characterize the scalar f4 equality itself, which can also
hold accidentally. If `X = α Y + (1 - α) C` in lineage weights, then

`f4(A, O; X, C) / f4(A, O; B, C)
  = α * (f4(A, O; Y, C) / f4(A, O; B, C))`.

Thus, for a nonzero denominator, the ratio equals `α` exactly when `α = 0`
or the f4-equality condition `f4(A, O; Y, C) = f4(A, O; B, C)` required by
`f4_ratio` holds. At a zero
denominator the ratio is undefined mathematically; Lean's value `x / 0 = 0`
is a junk value and is excluded by the nonzero-denominator hypotheses.

A two-edge example whose reference has weight on only the first edge gives
ratio `2α`, hence a
value outside `[0, 1]` when `α > 1/2`.

## References

* N. Patterson et al., *Ancient admixture in human history*, Genetics 192
  (2012), 1065–1093, f4-ratio estimation.
-/

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Biology.PopulationGenetics.Admixture

/-- Bias factor of the f4-ratio estimator, in the real-number form that the
drift-model glue instantiates with `fX = f4(A, O; X, C)`, `fY = f4(A, O; Y, C)`
and `fB = f4(A, O; B, C)`: if the numerator is `α` times the statistic of the
unsampled source `Y` (`fX = α * fY`, the conclusion of
`DriftModel.f4_admixture_right` for `X = α Y + (1 - α) C`) and the denominator
`fB` is nonzero, the ratio `fX / fB` is `α` times the factor `fY / fB`. For
`fB = 0` the ratio is undefined; Lean's value `fX / 0 = 0` is junk and is not
covered by this statement. -/
theorem ratio_eq_mul_div_of_eq_mul {α fX fY fB : ℝ} (hX : fX = α * fY) (hB : fB ≠ 0) :
    fX / fB = α * (fY / fB) := by
  rw [hX]
  ring

/-- Exactly when the f4-ratio estimator is unbiased: with `fX = α * fY` and a
nonzero denominator `fB`, the ratio `fX / fB` equals `α` if and only if `α = 0`
or the f4-equality condition `fY = fB`
(`f4(A, O; Y, C) = f4(A, O; B, C)`) required by `f4_ratio` holds. For
`α ≠ 0` this says exactly that the ratio equals `α` iff that f4 equality
holds; the disjunct `α = 0` is needed, since then the ratio is `0 = α` for
every `fY`. -/
theorem ratio_eq_iff_of_eq_mul {α fX fY fB : ℝ} (hX : fX = α * fY) (hB : fB ≠ 0) :
    fX / fB = α ↔ α = 0 ∨ fY = fB := by
  rw [hX, div_eq_iff hB]
  constructor
  · intro h
    have hsub : α * fY - α * fB = 0 := sub_eq_zero.mpr h
    have hfactor : α * (fY - fB) = α * fY - α * fB := by ring
    have hzero : α * (fY - fB) = 0 := by rw [hfactor]; exact hsub
    rcases mul_eq_zero.mp hzero with hα | hdiff
    · exact Or.inl hα
    · exact Or.inr (sub_eq_zero.mp hdiff)
  · rintro (rfl | rfl)
    · ring
    · rfl

/-- A misspecified f4 ratio outside `[0, 1]`. Two edges of the same nonzero
drift length `ℓ`, with lineage weights `wA = (1, 1)`, `wO = wC = (0, 0)`,
unsampled source `wY = (1, 1)`, sampled reference `wB = (1, 0)` (weight only
on the first of the two edges carrying `wY`), and admixed target
`wX = α wY + (1 - α) wC`. In
the drift-model form `f4(P, Q; R, S) = ∑ e, (wP e - wQ e) * (wR e - wS e) * len e`,
the ratio `f4(A, O; X, C) / f4(A, O; B, C)` equals `2 * α`, which exceeds `1`
when `α > 1 / 2`. -/
theorem sum_ratio_eq_two_mul_of_split_reference {α ℓ : ℝ} {len wA wO wX wY wB wC : Fin 2 → ℝ}
    (hℓ : ℓ ≠ 0) (hlen : len = ![ℓ, ℓ]) (hwA : wA = ![1, 1]) (hwO : wO = ![0, 0])
    (hwY : wY = ![1, 1]) (hwB : wB = ![1, 0]) (hwC : wC = ![0, 0])
    (hwX : wX = α • wY + (1 - α) • wC) :
    (∑ e, (wA e - wO e) * (wX e - wC e) * len e) /
        (∑ e, (wA e - wO e) * (wB e - wC e) * len e) = 2 * α := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [hwA, hwO, hwB, hwC, hlen, hwX, hwY, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

end MathlibExt.Biology.PopulationGenetics.Admixture

namespace MathlibExt.Biology.PopulationGenetics.FStatistics

open MeasureTheory

/-- Bias factor for the f4-ratio estimator in the drift model: without the
f4-equality hypothesis of `f4_ratio`, the ratio is `α` times
`f4(A, O; Y, C) / f4(A, O; B, C)`. -/
theorem DriftModel.f4_ratio_eq_mul_div {Ω P E : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [Fintype E] (M : DriftModel μ E P)
    {A O X Y B C : P} {α : ℝ}
    (h : M.weight X = α • M.weight Y + (1 - α) • M.weight C)
    (hB : f4 μ M.freq A O B C ≠ 0) :
    f4 μ M.freq A O X C / f4 μ M.freq A O B C =
      α * (f4 μ M.freq A O Y C / f4 μ M.freq A O B C) :=
  MathlibExt.Biology.PopulationGenetics.Admixture.ratio_eq_mul_div_of_eq_mul
    (M.f4_admixture_right h) hB

/-- The f4 ratio recovers `α` exactly when `α = 0` or the f4-equality
condition `f4(A, O; Y, C) = f4(A, O; B, C)` required by `f4_ratio` holds.
This characterizes the scalar equality, not a phylogenetic sister
relationship, for which the drift model has no predicate. -/
theorem DriftModel.f4_ratio_eq_iff {Ω P E : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [Fintype E] (M : DriftModel μ E P)
    {A O X Y B C : P} {α : ℝ}
    (h : M.weight X = α • M.weight Y + (1 - α) • M.weight C)
    (hB : f4 μ M.freq A O B C ≠ 0) :
    f4 μ M.freq A O X C / f4 μ M.freq A O B C = α ↔
      α = 0 ∨ f4 μ M.freq A O Y C = f4 μ M.freq A O B C :=
  MathlibExt.Biology.PopulationGenetics.Admixture.ratio_eq_iff_of_eq_mul
    (M.f4_admixture_right h) hB

/-- In the two-edge split-reference configuration of
`Admixture.sum_ratio_eq_two_mul_of_split_reference`, the drift-model f4 ratio
is `2α`. -/
theorem DriftModel.f4_ratio_eq_two_mul_of_split_reference {Ω P : Type*}
    {m : MeasurableSpace Ω} {μ : Measure Ω}
    (M : DriftModel μ (Fin 2) P) {A O X Y B C : P} {α ℓ : ℝ}
    (hℓ : ℓ ≠ 0) (hl : M.len = ![ℓ, ℓ])
    (hA : M.weight A = ![1, 1]) (hO : M.weight O = ![0, 0])
    (hY : M.weight Y = ![1, 1]) (hBw : M.weight B = ![1, 0])
    (hC : M.weight C = ![0, 0])
    (h : M.weight X = α • M.weight Y + (1 - α) • M.weight C) :
    f4 μ M.freq A O X C / f4 μ M.freq A O B C = 2 * α := by
  rw [M.f4_freq, M.f4_freq]
  exact MathlibExt.Biology.PopulationGenetics.Admixture.sum_ratio_eq_two_mul_of_split_reference
    hℓ hl hA hO hY hBw hC h

end MathlibExt.Biology.PopulationGenetics.FStatistics
