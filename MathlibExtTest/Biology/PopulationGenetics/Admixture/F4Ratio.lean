/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Admixture.F4Ratio
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum
import MathlibExt.Biology.PopulationGenetics.Admixture.ConditionalNegDef

@[expose] public section

open MeasureTheory
open MathlibExt.Biology.PopulationGenetics.FStatistics
open scoped ENNReal BigOperators symmDiff

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.F4Ratio

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

/-- Integration against `μ4` is averaging over the four outcomes. -/
theorem integral_μ4 (f : Fin 4 → ℝ) : ∫ ω, f ω ∂μ4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp only [μ4, integral_smul_measure, integral_count, Fin.sum_univ_four]
  norm_num
  ring

/-- Two orthogonal drift increments, each with second moment `1/16`. -/
noncomputable def incr4 : Fin 2 → Fin 4 → ℝ :=
  ![![1 / 4, 1 / 4, -1 / 4, -1 / 4], ![1 / 4, -1 / 4, 1 / 4, -1 / 4]]

/-- Drift-model witness for the split-reference example. Populations are
`0 = A`, `1 = O`, `2 = X`, `3 = Y`, `4 = B`, `5 = C`, with
`X = (3/4) Y + (1/4) C` in lineage weights. -/
noncomputable def M : DriftModel μ4 (Fin 2) (Fin 6) where
  root := fun _ => 1 / 2
  incr := incr4
  len := fun _ => 1 / 16
  weight := ![![1, 1], ![0, 0], ![3 / 4, 3 / 4], ![1, 1], ![1, 0], ![0, 0]]
  memLp_root := MemLp.of_discrete
  memLp_incr := fun _ => MemLp.of_discrete
  inner_incr := by
    intro e f h
    fin_cases e <;> fin_cases f <;> simp_all [integral_μ4, incr4] <;> norm_num
  sq_incr := by
    intro e
    fin_cases e <;> simp [integral_μ4, incr4] <;> norm_num

theorem weight_X :
    M.weight 2 = (3 / 4 : ℝ) • M.weight 3 + (1 - 3 / 4 : ℝ) • M.weight 5 := by
  ext e
  fin_cases e <;> simp [M] <;> norm_num

theorem f4_B : f4 μ4 M.freq 0 1 4 5 = 1 / 16 := by
  rw [M.f4_freq]
  simp [M, Fin.sum_univ_two]

theorem f4_Y : f4 μ4 M.freq 0 1 3 5 = 1 / 8 := by
  rw [M.f4_freq]
  simp [M, Fin.sum_univ_two]
  norm_num

theorem f4_B_ne_zero : f4 μ4 M.freq 0 1 4 5 ≠ 0 := by
  rw [f4_B]
  norm_num

/-- The principal bias-factor API on the concrete model. -/
example :
    f4 μ4 M.freq 0 1 2 5 / f4 μ4 M.freq 0 1 4 5 =
      (3 / 4) * (f4 μ4 M.freq 0 1 3 5 / f4 μ4 M.freq 0 1 4 5) :=
  M.f4_ratio_eq_mul_div weight_X f4_B_ne_zero

/-- The principal iff API detects the failed f4 equality on the concrete
model: the ratio is not `α = 3/4`. -/
example : ¬ f4 μ4 M.freq 0 1 2 5 / f4 μ4 M.freq 0 1 4 5 = 3 / 4 := by
  have hiff := M.f4_ratio_eq_iff weight_X f4_B_ne_zero
  intro h
  rcases hiff.mp h with hα | hEq
  · norm_num at hα
  · rw [f4_Y, f4_B] at hEq
    norm_num at hEq

/-- With `α = 3/4`, the misspecified ratio is `3/2`, outside `[0, 1]`. -/
example : f4 μ4 M.freq 0 1 2 5 / f4 μ4 M.freq 0 1 4 5 = 3 / 2 := by
  have h := M.f4_ratio_eq_two_mul_of_split_reference (A := 0) (O := 1) (X := 2)
    (Y := 3) (B := 4) (C := 5) (α := 3 / 4) (ℓ := 1 / 16)
    (by norm_num)
    (by ext e; fin_cases e <;> simp [M])
    rfl rfl rfl rfl rfl weight_X
  rw [h]
  norm_num

/-- Scalar boundary probe through the iff API: at `α = 0`, the ratio is `α`
even when f4 equality fails; this is why the iff has the `α = 0` disjunct. -/
example :
    ((0 : ℝ) * 2) / 1 = 0 ∧ ¬((2 : ℝ) = 1) := by
  have h := (MathlibExt.Biology.PopulationGenetics.Admixture.ratio_eq_iff_of_eq_mul
    (α := (0 : ℝ)) (fX := (0 : ℝ)) (fY := (2 : ℝ)) (fB := (1 : ℝ))
    (by norm_num) (by norm_num)).mpr (Or.inl rfl)
  exact ⟨by simpa using h, by norm_num⟩

/-! ### The sister condition -/

section SisterCriterion

open MathlibExt.Biology.PopulationGenetics.Admixture (exists_driftModel)

variable {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E]

example (M : DriftModel μ E P) (A O Y B C : P) :
    f4 μ M.freq A O Y C - f4 μ M.freq A O B C =
      ∑ e, (M.weight A e - M.weight O e) * (M.weight Y e - M.weight B e) * M.len e :=
  M.f4_sub_f4_eq_sum A O Y B C

example (M : DriftModel μ E P) (A O Y B C : P) :
    f4 μ M.freq A O Y C = f4 μ M.freq A O B C ↔
      ∑ e, (M.weight A e - M.weight O e) * (M.weight Y e - M.weight B e) * M.len e = 0 :=
  M.f4_sister_iff_sum_eq_zero A O Y B C

example (M : DriftModel μ E P) (A O Y B C : P) :
    f4 μ M.freq A O Y C = f4 μ M.freq A O B C ↔ f4 μ M.freq A O Y B = 0 :=
  M.f4_sister_iff_f4_eq_zero A O Y B C

example (M : DriftModel μ E P) (A O Y B C : P)
    (h : ∀ e, (M.weight A e - M.weight O e) * (M.weight Y e - M.weight B e) = 0) :
    f4 μ M.freq A O Y C = f4 μ M.freq A O B C :=
  M.f4_sister_of_disjoint A O Y B C h

example [DecidableEq E] (M : DriftModel μ E P) (hM : M.HasBinaryLoadings) (A O Y B C : P)
    (h : Disjoint (M.lineage A ∆ M.lineage O) (M.lineage Y ∆ M.lineage B)) :
    f4 μ M.freq A O Y C = f4 μ M.freq A O B C :=
  M.f4_sister_of_lineage_disjoint hM A O Y B C h

/-- Weights of the satisfying example: populations `A=0, O=1, Y=2, B=3, C=4`
on three edges; edge `0` is on the `A`–`O` path and is shared equally by `Y`
and `B`, and `Y`, `B` differ only on edges `1, 2` (off that path). Binary. -/
def wSisterCriterion : Fin 5 → Fin 3 → ℝ := ![![1, 0, 0], ![0, 0, 0], ![1, 1, 0], ![1, 0, 1], ![0, 0, 0]]

/-- The failing variant: `B=3` loses edge `0`, i.e. `B` branches off before the
`A`–`O` path edge that `Y` carries. -/
def wOffSisterPath : Fin 5 → Fin 3 → ℝ := ![![1, 0, 0], ![0, 0, 0], ![1, 1, 0], ![0, 0, 1], ![0, 0, 0]]

def lenSister3 : Fin 3 → ℝ := ![1, 2, 3]

theorem sister_example :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ (Fin 3) (Fin 5)), M.weight = wSisterCriterion ∧ M.len = lenSister3 ∧
        f4 μ M.freq 0 1 2 4 = 1 ∧ f4 μ M.freq 0 1 3 4 = 1 ∧ f4 μ M.freq 0 1 2 3 = 0 := by
  obtain ⟨Ω, hΩ, μ, hμ, M, hw, hl⟩ := exists_driftModel wSisterCriterion lenSister3 (by
    intro e
    fin_cases e <;> norm_num [lenSister3])
  refine ⟨Ω, hΩ, μ, hμ, M, hw, hl, ?_, ?_, ?_⟩ <;>
    · rw [M.f4_freq, hw, hl]
      norm_num [Fin.sum_univ_three, wSisterCriterion, lenSister3]

theorem offPath_example :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ (Fin 3) (Fin 5)), M.weight = wOffSisterPath ∧ M.len = lenSister3 ∧
        f4 μ M.freq 0 1 2 4 = 1 ∧ f4 μ M.freq 0 1 3 4 = 0 ∧
          ∑ e, (M.weight 0 e - M.weight 1 e) * (M.weight 2 e - M.weight 3 e) * M.len e = 1 := by
  obtain ⟨Ω, hΩ, μ, hμ, M, hw, hl⟩ := exists_driftModel wOffSisterPath lenSister3 (by
    intro e
    fin_cases e <;> norm_num [lenSister3])
  refine ⟨Ω, hΩ, μ, hμ, M, hw, hl, ?_, ?_, ?_⟩
  · rw [M.f4_freq, hw, hl]
    norm_num [Fin.sum_univ_three, wOffSisterPath, lenSister3]
  · rw [M.f4_freq, hw, hl]
    norm_num [Fin.sum_univ_three, wOffSisterPath, lenSister3]
  · rw [hw, hl]
    norm_num [Fin.sum_univ_three, wOffSisterPath, lenSister3]

/-- Accidental equality: the criterion sum can vanish by cancellation between
two edges of the `A`–`O` path, so disjointness of the supports is sufficient
but not necessary. Populations `A=0, O=1, Y=2, B=3, C=4` on two edges. -/
def wSisterAccidental : Fin 5 → Fin 2 → ℝ := ![![1, 1], ![0, 0], ![1, 0], ![0, 1], ![0, 0]]

theorem accidental_example :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ (Fin 2) (Fin 5)), M.weight = wSisterAccidental ∧ M.len = ![1, 1] ∧
        f4 μ M.freq 0 1 2 4 = f4 μ M.freq 0 1 3 4 ∧
          ¬ (∀ e, (M.weight 0 e - M.weight 1 e) * (M.weight 2 e - M.weight 3 e) = 0) := by
  obtain ⟨Ω, hΩ, μ, hμ, M, hw, hl⟩ := exists_driftModel wSisterAccidental ![1, 1] (by
    intro e
    fin_cases e <;> norm_num)
  refine ⟨Ω, hΩ, μ, hμ, M, hw, hl, ?_, ?_⟩
  · rw [M.f4_freq, M.f4_freq, hw, hl]
    norm_num [Fin.sum_univ_two, wSisterAccidental]
  · intro hcon
    have := hcon 0
    rw [hw] at this
    norm_num [wSisterAccidental] at this

/-- Endpoint probe: with no edges every f4 vanishes and the criterion holds
trivially (empty sum). -/
example {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} (M : DriftModel μ Empty P)
    (A O Y B C : P) : f4 μ M.freq A O Y C = f4 μ M.freq A O B C := by
  rw [M.f4_freq, M.f4_freq]
  simp

end SisterCriterion

end MathlibExtTest.Biology.PopulationGenetics.Admixture.F4Ratio
