/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact source statement below is adapted from `anthropics/fermats-last-theorem`,
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`,
`Theorems/Thm_MeasureTheory_exists_section_integral_mul_eq_sum_div_of_forall_eq_of_forall_exists.lean`.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

import MathlibExt.MeasureTheory.Group.DoubleCosetCutoff

/-! # Source fidelity and boundary tests for finite double-coset cutoffs -/

open MeasureTheory

namespace DoubleCosetCutoffTest

/-- The full original source type, including its weak asymmetric measure assumptions. -/
theorem sourceStatement
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (U : Set G)
    (hUo : IsOpen U) (hUc : IsCompact U) (hμUtop : μ U ≠ ⊤)
    (h1U : (1 : G) ∈ U) (hUmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U)
    (hUinv : ∀ a ∈ U, a⁻¹ ∈ U)
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts τ] [τ.IsOpenPosMeasure]
    (ψ : G → ℂ) (hψ : ∀ t ∈ T, ∀ x : G, ∀ u ∈ U, ψ (t * x * u) = ψ x)
    (S : Finset G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T, ∀ u ∈ U, s' = t * s * u → s' = s)
    (hcov : ∀ x, ψ x ≠ 0 → ∃ s ∈ S, ∃ t ∈ T, ∃ u ∈ U, x = t * s * u) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      (∀ x, ψ x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧
      ∫ x, ψ x * (w x : ℂ) ∂μ =
        ∑ s ∈ S, ψ s * ((μ U).toReal : ℂ) /
          ((τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal : ℂ) := by
  refine ⟨doubleCosetCutoff U T τ S, doubleCosetCutoff_nonneg U T τ S,
    measurable_doubleCosetCutoff U T τ S hUo,
    hasCompactSupport_doubleCosetCutoff U T τ S hUc, ?_, ?_⟩
  · exact fun x hx => integral_doubleCosetCutoff_mul U T τ S
      hUo hUc h1U hUmul hUinv hT hS x (hcov x hx)
  · exact (doubleCosetCutoff_integrable_and_integral U T τ S μ hUo hμUtop ψ
      (fun x u hu => by simpa only [one_mul] using hψ 1 T.one_mem x u hu)).2

/-- Empty representatives give the zero cutoff, independently of all topology. -/
theorem emptyCutoff {G : Type*} [Group G] (U : Set G) (T : Subgroup G)
    [MeasurableSpace T] (τ : Measure T) : doubleCosetCutoff U T τ ∅ = 0 := by
  funext y
  simp [doubleCosetCutoff]

/-- Zero measure cannot give a normalized cutoff: the denominator totalizes. -/
theorem zeroMeasureCutoff {G : Type*} [Group G] (U : Set G) (T : Subgroup G)
    [MeasurableSpace T] (S : Finset G) : doubleCosetCutoff U T 0 S = 0 := by
  funext y
  simp [doubleCosetCutoff]

/-- Scaling the acting measure rescales the explicit cutoff reciprocally.
This includes the totalized zero/infinite scaling boundary. -/
theorem rescaleCutoff {G : Type*} [Group G] (U : Set G) (T : Subgroup G)
    [MeasurableSpace T] (τ : Measure T) (S : Finset G) (c : ENNReal) (y : G) :
    doubleCosetCutoff U T (c • τ) S y = c.toReal⁻¹ * doubleCosetCutoff U T τ S y := by
  classical
  simp only [doubleCosetCutoff, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, mul_inv_rev, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hy : s⁻¹ * y ∈ U <;> simp [hy, mul_comm]

section SymmetricGroup

private abbrev P := Equiv.Perm (Fin 3)
local instance : TopologicalSpace P := ⊥
local instance : DiscreteTopology P := ⟨rfl⟩
local instance : MeasurableSpace P := borel P
local instance : BorelSpace P := ⟨rfl⟩

private abbrev H : Subgroup P := MulAction.stabilizer P (0 : Fin 3)
private abbrev a : P := Equiv.swap 0 1
private abbrev b : P := Equiv.swap 1 2
private abbrev reps : Finset P := {1, a}

/-- The compact-open subgroup in the finite test is not normal. -/
theorem stabilizer_not_normal : ¬ H.Normal := by
  intro h
  have hb : b ∈ H := by decide
  have hconj := h.conj_mem b hb a
  revert hconj
  decide

private theorem count_H : (Measure.count : Measure P) (H : Set P) = 2 := by
  have he : (H : Set P) = ↑({1, b} : Finset P) := by
    ext p
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    change p 0 = 0 ↔ p = 1 ∨ p = b
    revert p
    decide
  rw [he, Measure.count_apply_finset]
  norm_num [show (1 : P) ≠ b by decide]

private theorem count_slice (s : P) :
    (Measure.count : Measure H) {t : H | s⁻¹ * (t : P) * s ∈ H} =
      if s ∈ H then 2 else 1 := by
  rw [Measure.count_apply_finite _ (Set.toFinite _), Set.Finite.toFinset_ofPred]
  have hc : ∀ s : P,
      (Finset.univ.filter (fun t : H => s⁻¹ * (t : P) * s ∈ H)).card =
        if s ∈ H then 2 else 1 := by decide
  rw [hc]
  split_ifs <;> norm_num

/-- A concrete noncommutative, nonnormal-subgroup normalization test. -/
theorem symmetricGroup_normalized (x : P) :
    ∫ t : H, doubleCosetCutoff (H : Set P) H Measure.count reps ((t : P) * x)
      ∂Measure.count = 1 := by
  apply integral_doubleCosetCutoff_mul (H : Set P) H Measure.count reps
    (isOpen_discrete _) (Set.toFinite _).isCompact H.one_mem
    (fun _ ha _ hb => H.mul_mem ha hb) (fun _ ha => H.inv_mem ha) (isClosed_discrete _)
  · change ∀ s ∈ reps, ∀ s' ∈ reps, ∀ t ∈ H, ∀ u ∈ H,
      s' = t * s * u → s' = s
    decide
  · have hcov : ∀ x : P, ∃ s ∈ reps, ∃ t ∈ H, ∃ u ∈ H, x = t * s * u := by decide
    exact hcov x

/-- Every representative outside the nonnormal subgroup gives the same
weighted integral, three, although the two-element support slice changes. -/
theorem symmetricGroup_integral (s : P) (hs : s ∉ H) :
    ∫ y, (doubleCosetCutoff (H : Set P) H Measure.count {1, s} y : ℂ)
      ∂Measure.count = 3 := by
  have he := (doubleCosetCutoff_integrable_and_integral (H : Set P) H Measure.count
    {1, s} Measure.count (isOpen_discrete _) (by rw [count_H]; norm_num)
    (fun _ => (1 : ℂ)) (fun _ _ _ => rfl)).2
  have hne : (1 : P) ≠ s := by
    intro h
    subst s
    exact hs H.one_mem
  have hm (r : P) : (Measure.count : Measure H)
      {t : H | r⁻¹ * (t : P) * r ∈ (H : Set P)} = if r ∈ H then 2 else 1 := count_slice r
  simp only [hm, count_H, one_mul] at he
  have hs0 : s 0 ≠ 0 := hs
  norm_num [hne, hs0] at he ⊢
  exact he

/-- Changing a representative by left multiplication from `H` preserves the
computed integral. Neither representative is in the nonnormal subgroup. -/
theorem changedRepresentative_integral :
    (∫ y, (doubleCosetCutoff (H : Set P) H Measure.count {1, a} y : ℂ)
      ∂Measure.count) =
    ∫ y, (doubleCosetCutoff (H : Set P) H Measure.count {1, b * a} y : ℂ)
      ∂Measure.count := by
  rw [symmetricGroup_integral a (by decide), symmetricGroup_integral (b * a) (by decide)]

/-- Doubling `τ` halves the cutoff and still gives orbit integral one. -/
theorem scaled_normalized (x : P) :
    ∫ t : H, doubleCosetCutoff (H : Set P) H ((2 : ENNReal) • Measure.count) reps ((t : P) * x)
      ∂((2 : ENNReal) • Measure.count) = 1 := by
  rw [integral_smul_measure]
  simp_rw [rescaleCutoff, ENNReal.toReal_ofNat]
  rw [integral_const_mul, symmetricGroup_normalized]
  norm_num

/-- Infinite acting mass totalizes the cutoff to zero, not a normalized section. -/
theorem infiniteMeasure_not_normalized (x : P) :
    (∫ t : H, doubleCosetCutoff (H : Set P) H ((⊤ : ENNReal) • Measure.count) reps
      ((t : P) * x) ∂((⊤ : ENNReal) • Measure.count)) ≠ 1 := by
  simp_rw [rescaleCutoff, ENNReal.toReal_top, inv_zero, zero_mul]
  simp

/-- Zero acting mass likewise cannot normalize a nonempty orbit. -/
theorem zeroMeasure_not_normalized (x : P) :
    (∫ t : H, doubleCosetCutoff (H : Set P) H 0 reps ((t : P) * x) ∂(0 : Measure H)) ≠ 1 := by
  simp

end SymmetricGroup

end DoubleCosetCutoffTest
