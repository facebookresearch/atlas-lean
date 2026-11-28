/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.FStatistics
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

The f4-equality itself has a graph criterion: `f4(A, O; Y, C) = f4(A, O; B, C)`
if and only if the weighted overlap
`∑ e, (w A e - w O e) * (w Y e - w B e) * len e` vanishes, equivalently if and
only if `f4(A, O; Y, B) = 0`. In particular it holds when no edge separates
both `A` from `O` and `Y` from `B`.

## References

* N. Patterson et al., *Ancient admixture in human history*, Genetics 192
  (2012), 1065–1093, f4-ratio estimation.
-/

@[expose] public section

open scoped BigOperators symmDiff

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

/-- When the population f4 ratio recovers `α`: with `fX = α * fY` and a
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

/-- A split-reference f4 ratio that can lie outside `[0, 1]`. Two edges of the same nonzero
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

/-- Bias factor for the f4-ratio estimator in the drift model: if `X = α Y + (1 - α) C` in
lineage weights and `f4(A, O; B, C) ≠ 0`, then, without the f4-equality hypothesis of
`f4_ratio`, the ratio is `α` times `f4(A, O; Y, C) / f4(A, O; B, C)`. -/
theorem DriftModel.f4_ratio_eq_mul_div {Ω P E : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [Fintype E] (M : DriftModel μ E P)
    {A O X Y B C : P} {α : ℝ}
    (h : M.weight X = α • M.weight Y + (1 - α) • M.weight C)
    (hB : f4 μ M.freq A O B C ≠ 0) :
    f4 μ M.freq A O X C / f4 μ M.freq A O B C =
      α * (f4 μ M.freq A O Y C / f4 μ M.freq A O B C) :=
  MathlibExt.Biology.PopulationGenetics.Admixture.ratio_eq_mul_div_of_eq_mul
    (M.f4_admixture_right h) hB

/-- If `X = α Y + (1 - α) C` in lineage weights and `f4(A, O; B, C) ≠ 0`, the f4 ratio
recovers `α` exactly when `α = 0` or the f4-equality condition
`f4(A, O; Y, C) = f4(A, O; B, C)` required by `f4_ratio` holds.
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

/-! ### The sister condition -/

variable {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E]

/-- The difference of the two f4 statistics in the sister condition of
`DriftModel.f4_ratio` is the length-weighted sum of products of the `A`–`O` and
`Y`–`B` weight contrasts, the dot product of the contrasts scaled by `√len` (on a
tree with binary weights, the contrasts are supported on the two paths):
`f4(A,O;Y,C) - f4(A,O;B,C)` equals
`∑ e, (w A e - w O e) * (w Y e - w B e) * len e`. The reference population `C`
cancels. -/
theorem DriftModel.f4_sub_f4_eq_sum (M : DriftModel μ E P) (A O Y B C : P) :
    f4 μ M.freq A O Y C - f4 μ M.freq A O B C =
      ∑ e, (M.weight A e - M.weight O e) * (M.weight Y e - M.weight B e) * M.len e := by
  rw [M.f4_freq, M.f4_freq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- **Graph criterion for the f4-ratio sister condition**: in a drift model,
`f4(A,O;Y,C) = f4(A,O;B,C)` if and only if
`∑ e, (w A e - w O e) * (w Y e - w B e) * len e = 0`. -/
theorem DriftModel.f4_sister_iff_sum_eq_zero (M : DriftModel μ E P) (A O Y B C : P) :
    f4 μ M.freq A O Y C = f4 μ M.freq A O B C ↔
      ∑ e, (M.weight A e - M.weight O e) * (M.weight Y e - M.weight B e) * M.len e = 0 := by
  rw [← sub_eq_zero, M.f4_sub_f4_eq_sum]

/-- The sister condition `f4(A,O;Y,C) = f4(A,O;B,C)` holds if and only if
`f4(A,O;Y,B) = 0`: the criterion sum is itself an f4 statistic. -/
theorem DriftModel.f4_sister_iff_f4_eq_zero (M : DriftModel μ E P) (A O Y B C : P) :
    f4 μ M.freq A O Y C = f4 μ M.freq A O B C ↔ f4 μ M.freq A O Y B = 0 := by
  rw [M.f4_sister_iff_sum_eq_zero, M.f4_freq]

/-- Sufficient condition for the sister equality: if every edge separating
`Y` from `B` (every edge with `w Y e ≠ w B e`) has a zero `A`–`O` weight
contrast (`w A e = w O e`; on a tree, it lies off the `A`–`O` path), i.e.
`(w A e - w O e) * (w Y e - w B e) = 0` for every edge,
then `f4(A,O;Y,C) = f4(A,O;B,C)`. Cancellation between edges can also give the
equality, so this is not necessary. -/
theorem DriftModel.f4_sister_of_disjoint (M : DriftModel μ E P) (A O Y B C : P)
    (h : ∀ e, (M.weight A e - M.weight O e) * (M.weight Y e - M.weight B e) = 0) :
    f4 μ M.freq A O Y C = f4 μ M.freq A O B C :=
  (M.f4_sister_iff_f4_eq_zero A O Y B C).mpr (M.f4_eq_zero_of_disjoint h)

/-- Binary-loading form of the sufficient condition: if the lineage symmetric
difference of `A` and `O` (on a tree, the `A`–`O` path) is disjoint from that
of `Y` and `B`, then `f4(A,O;Y,C) = f4(A,O;B,C)`. -/
theorem DriftModel.f4_sister_of_lineage_disjoint [DecidableEq E] (M : DriftModel μ E P)
    (hM : M.HasBinaryLoadings) (A O Y B C : P)
    (h : Disjoint (M.lineage A ∆ M.lineage O) (M.lineage Y ∆ M.lineage B)) :
    f4 μ M.freq A O Y C = f4 μ M.freq A O B C := by
  refine M.f4_sister_of_disjoint A O Y B C fun e => ?_
  by_cases h1 : M.weight A e - M.weight O e = 0
  · simp [h1]
  by_cases h2 : M.weight Y e - M.weight B e = 0
  · simp [h2]
  exfalso
  have mem1 : e ∈ M.lineage A ∆ M.lineage O := by
    rcases hM A e with hA | hA <;> rcases hM O e with hO | hO <;>
      simp_all [DriftModel.lineage, Finset.mem_symmDiff]
  have mem2 : e ∈ M.lineage Y ∆ M.lineage B := by
    rcases hM Y e with hY | hY <;> rcases hM B e with hB | hB <;>
      simp_all [DriftModel.lineage, Finset.mem_symmDiff]
  exact Finset.disjoint_left.mp h mem1 mem2

end MathlibExt.Biology.PopulationGenetics.FStatistics
