/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import PhyslibExt.CondensedMatter.Plasticity.DeviatoricReturnMap

/-!
# Deviatoric return-map checks

## i. Overview

Elaboration, non-vacuity, and endpoint checks for
`PhyslibExt.CondensedMatter.Plasticity.DeviatoricReturnMap`: the public
shape of the metric identity, its symmetric-shear double count, the
zero-correction case at the singleton yield section `{0}`, the
totalized zero-shear-modulus endpoint, the energy characterization
at `{0}`, and maximum-plastic-work checks: zero comparison stress, an
outside-section witness at any pressure, and sign, pressure-section and
anisotropic-scaling controls. These are checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Metric identity
- B. Zero correction and totalization
- C. Energy characterization at a singleton
- D. Maximum plastic work

## iv. References

- `PhyslibExt.CondensedMatter.Plasticity.DeviatoricReturnMap`
-/

open scoped InnerProductSpace Matrix
open scoped Plasticity
open MathlibExt.Analysis.InnerProductSpace.ConvexProjection

/-! ## A. Metric identity -/

/-- Public shape of the Frobenius metric identity. -/
example (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    ⟪A, B⟫_ℝ = ∑ i, ∑ j, A i j * B i j :=
  Plasticity.frobenius_inner_eq_sum_mul A B

/-- The unit symmetric shear tensor has squared Frobenius norm `2`:
the off-diagonal pair is counted twice. -/
example :
    ⟪(!![0, 1, 0; 1, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ),
      !![0, 1, 0; 1, 0, 0; 0, 0, 0]⟫_ℝ = 2 := by
  rw [Plasticity.frobenius_inner_eq_sum_mul]
  norm_num [Fin.sum_univ_three]

/-! ## B. Zero correction and totalization -/

/-- At the singleton yield section `{0}` and zero trial stress, the
return has zero plastic strain increment (the in-`K` component of
`deviatoric_return`, with every premise discharged). -/
example :
    Plasticity.plasticStrainIncrement 1 (0 : Matrix (Fin 3) (Fin 3) ℝ)
        (Elasticity.meanStress (0 : Matrix (Fin 3) (Fin 3) ℝ) • 1 +
          convexProjection ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ))
            (Elasticity.deviatoricStress (0 : Matrix (Fin 3) (Fin 3) ℝ)))
      = 0 := by
  have hKne : ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)).Nonempty :=
    Set.singleton_nonempty 0
  have hKc : IsComplete ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    @IsCompact.isComplete _ Plasticity.frobeniusUniformSpace _
      (@isCompact_singleton _ Plasticity.frobeniusUniformSpace.toTopologicalSpace _)
  have hKv : Convex ℝ ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    convex_singleton 0
  have hKdev : ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) ⊆
      Plasticity.deviatoricStresses := by
    intro σ hσ
    rw [Set.mem_singleton_iff] at hσ
    subst hσ
    exact ⟨Matrix.transpose_zero, by simp⟩
  have h := Plasticity.deviatoric_return (μ := 1)
    (K := ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)))
    (by norm_num) hKne hKc hKv hKdev
    (σTrial := (0 : Matrix (Fin 3) (Fin 3) ℝ)) Matrix.transpose_zero
  have hmem0 : Elasticity.deviatoricStress (0 : Matrix (Fin 3) (Fin 3) ℝ) ∈
      ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
    simp [Elasticity.deviatoricStress, Elasticity.meanStress]
  exact (h.2.2.2.2.2.2.2.2 hmem0).1

/-- At `μ = 0` the totalized plastic strain increment is `0` for every
pair of stresses. -/
example (σTrial σ : Matrix (Fin 3) (Fin 3) ℝ) :
    Plasticity.plasticStrainIncrement 0 σTrial σ = 0 := by
  simp [Plasticity.plasticStrainIncrement]

/-! ## C. Energy characterization at a singleton -/

/-- At the singleton yield section `{0}`, the energy characterization
gives `convexProjection {0} sTrial = 0` for every trial deviator. -/
example (sTrial : Matrix (Fin 3) (Fin 3) ℝ) :
    convexProjection ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) sTrial = 0 := by
  have hKne : ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)).Nonempty :=
    Set.singleton_nonempty 0
  have hKc : IsComplete ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    @IsCompact.isComplete _ Plasticity.frobeniusUniformSpace _
      (@isCompact_singleton _ Plasticity.frobeniusUniformSpace.toTopologicalSpace _)
  have hKv : Convex ℝ ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    convex_singleton 0
  refine (Plasticity.eq_projection_iff_energy_le (μ := 1) (by norm_num)
    hKne hKc hKv sTrial 0).mpr ⟨rfl, ?_⟩
  intro τ hτ
  rw [Set.mem_singleton_iff] at hτ
  subst hτ
  exact le_refl _

/-! ## D. Maximum plastic work -/

open Elasticity Plasticity

/-- Public shape of maximum plastic work. -/
example {μ : ℝ} (hμ : 0 < μ) {K : Set (Matrix (Fin 3) (Fin 3) ℝ)}
    (hKne : K.Nonempty) (hKc : IsComplete K) (hKv : Convex ℝ K)
    (hKdev : K ⊆ Plasticity.deviatoricStresses) (σTrial : Matrix (Fin 3) (Fin 3) ℝ) :
    ∀ τ ∈ K, 0 ≤ ∑ i, ∑ j,
      (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial) - τ) i j *
        Plasticity.plasticStrainIncrement μ σTrial
          (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) i j :=
  Plasticity.deviatoric_return_maximum_plastic_work hμ hKne hKc hKv hKdev σTrial

/-- Nonnegative plastic work against `τ = 0`, under the extra hypothesis
`0 ∈ K` (not a premise of the theorem). -/
example {μ : ℝ} (hμ : 0 < μ) {K : Set (Matrix (Fin 3) (Fin 3) ℝ)}
    (hKne : K.Nonempty) (hKc : IsComplete K) (hKv : Convex ℝ K)
    (hKdev : K ⊆ Plasticity.deviatoricStresses) (h0 : (0 : Matrix (Fin 3) (Fin 3) ℝ) ∈ K)
    (σTrial : Matrix (Fin 3) (Fin 3) ℝ) :
    0 ≤ ∑ i, ∑ j, (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) i j *
      Plasticity.plasticStrainIncrement μ σTrial
        (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) i j := by
  simpa using Plasticity.deviatoric_return_maximum_plastic_work hμ hKne hKc hKv hKdev σTrial 0 h0

/-- Trial deviator already in `K`: zero increment, hence zero work
against every comparison stress. -/
example (μ : ℝ) {K : Set (Matrix (Fin 3) (Fin 3) ℝ)}
    (hKne : K.Nonempty) (hKc : IsComplete K) (hKv : Convex ℝ K)
    (σTrial τ : Matrix (Fin 3) (Fin 3) ℝ) (hin : deviatoricStress σTrial ∈ K) :
    ∑ i, ∑ j, (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial) - τ) i j *
      Plasticity.plasticStrainIncrement μ σTrial
        (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) i j = 0 := by
  have hP := convexProjection_eq_self_of_mem hKne hKc hKv hin
  have hσ : meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial) = σTrial := by
    rw [hP]
    simp [deviatoricStress]
  simp [hσ, Plasticity.plasticStrainIncrement]

/-- Zero section `K = {0}`: zero work for every trial stress and shear modulus. -/
example (μ : ℝ) (σTrial : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ i, ∑ j,
      (meanStress σTrial • 1 + convexProjection ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ))
          (deviatoricStress σTrial) - 0) i j *
        Plasticity.plasticStrainIncrement μ σTrial
          (meanStress σTrial • 1 + convexProjection ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ))
            (deviatoricStress σTrial)) i j = 0 := by
  have hP : convexProjection ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) (deviatoricStress σTrial)
      = 0 :=
    convexProjection_mem (Set.singleton_nonempty 0)
      (@IsCompact.isComplete _ Plasticity.frobeniusUniformSpace _
        (@isCompact_singleton _ Plasticity.frobeniusUniformSpace.toTopologicalSpace _))
      (convex_singleton 0) _
  rw [hP]
  simp only [Plasticity.plasticStrainIncrement, meanStress, Fin.sum_univ_three,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Matrix.trace, Matrix.diag_apply, Matrix.zero_apply]
  simp
  ring

/-- Unit symmetric shear in the 0-1 plane. -/
private def workShearA : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 1, 0, 0; 0, 0, 0]

private lemma workShearA_inner : ⟪workShearA, workShearA⟫_ℝ = 2 := by
  rw [Plasticity.frobenius_inner_eq_sum_mul]
  simp [workShearA, Fin.sum_univ_three]
  norm_num

private lemma workSeg_compact : @IsCompact _ Plasticity.frobeniusUniformSpace.toTopologicalSpace
    (convexHull ℝ ({0, workShearA} : Set (Matrix (Fin 3) (Fin 3) ℝ))) := by
  letI : TopologicalSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    Plasticity.frobeniusUniformSpace.toTopologicalSpace
  exact (Set.toFinite _).isCompact_convexHull ℝ

private lemma workSeg_complete :
    IsComplete (convexHull ℝ ({0, workShearA} : Set (Matrix (Fin 3) (Fin 3) ℝ))) :=
  @IsCompact.isComplete _ Plasticity.frobeniusUniformSpace _ workSeg_compact

private lemma workSeg_subset :
    convexHull ℝ ({0, workShearA} : Set (Matrix (Fin 3) (Fin 3) ℝ)) ⊆
      Plasticity.deviatoricStresses := by
  have hconv : Convex ℝ Plasticity.deviatoricStresses := by
    intro x hx y hy a b _ _ _
    refine ⟨?_, ?_⟩
    · have h1 : xᵀ = x := hx.1
      have h2 : yᵀ = y := hy.1
      change (a • x + b • y)ᵀ = a • x + b • y
      simp [Matrix.transpose_add, Matrix.transpose_smul, h1, h2]
    · simp [Matrix.trace_add, Matrix.trace_smul, hx.2, hy.2]
  refine convexHull_min ?_ hconv
  intro x hx
  rcases hx with rfl | rfl
  · exact ⟨Matrix.transpose_zero, by simp⟩
  · refine ⟨?_, ?_⟩
    · change workShearAᵀ = workShearA
      ext i j; fin_cases i <;> fin_cases j <;> simp [workShearA]
    · simp [workShearA, Matrix.trace, Fin.sum_univ_three]

private lemma workSeg_proj :
    convexProjection (convexHull ℝ ({0, workShearA} : Set (Matrix (Fin 3) (Fin 3) ℝ)))
      ((2 : ℝ) • workShearA) = workShearA := by
  have hne : (convexHull ℝ ({0, workShearA} : Set (Matrix (Fin 3) (Fin 3) ℝ))).Nonempty :=
    ⟨0, subset_convexHull ℝ _ (by simp)⟩
  have hv : Convex ℝ (convexHull ℝ ({0, workShearA} : Set (Matrix (Fin 3) (Fin 3) ℝ))) :=
    convex_convexHull ℝ _
  have hA : workShearA ∈ convexHull ℝ ({0, workShearA} : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  refine convexProjection_eq_of_isNearestPoint hne workSeg_complete hv hA ?_
  refine (norm_eq_iInf_iff_real_inner_le_zero hv hA).mpr ?_
  intro w hw
  rw [convexHull_pair, segment_eq_image] at hw
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hw
  have hx : (2 : ℝ) • workShearA - workShearA = workShearA := by rw [two_smul]; abel
  have hw' : (1 - t) • (0 : Matrix (Fin 3) (Fin 3) ℝ) + t • workShearA - workShearA
      = (t - 1) • workShearA := by rw [smul_zero, zero_add, sub_smul, one_smul]
  rw [hx, hw', inner_smul_right, workShearA_inner]
  nlinarith

/-- Witness: trial stress `2 • workShearA + p • 1` (any pressure `p`), outside
`K = [0, workShearA]`; return `σ = p • 1 + workShearA`,
`Δε_p = workShearA / (2 μ)`, and work against `τ = 0` is `1 / μ`. -/
private lemma workSeg_work (μ p : ℝ) :
    ∑ i, ∑ j,
      (meanStress ((2 : ℝ) • workShearA + p • 1) • 1 +
          convexProjection (convexHull ℝ ({0, workShearA} : Set (Matrix (Fin 3) (Fin 3) ℝ)))
            (deviatoricStress ((2 : ℝ) • workShearA + p • 1)) - 0) i j *
        Plasticity.plasticStrainIncrement μ ((2 : ℝ) • workShearA + p • 1)
          (meanStress ((2 : ℝ) • workShearA + p • 1) • 1 +
            convexProjection (convexHull ℝ ({0, workShearA} : Set (Matrix (Fin 3) (Fin 3) ℝ)))
              (deviatoricStress ((2 : ℝ) • workShearA + p • 1))) i j = μ⁻¹ := by
  have hm : meanStress ((2 : ℝ) • workShearA + p • 1) = p := by
    simp [meanStress, workShearA, Matrix.trace, Fin.sum_univ_three]
    ring
  have hd : deviatoricStress ((2 : ℝ) • workShearA + p • 1) = (2 : ℝ) • workShearA := by
    rw [deviatoricStress, hm]; abel
  rw [hm, hd, workSeg_proj]
  simp only [Plasticity.plasticStrainIncrement, Fin.sum_univ_three, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Matrix.zero_apply,
    workShearA]
  simp
  field_simp
  ring

/-- Strict positivity of the witness work for every `μ > 0` and every pressure `p`. -/
example {μ : ℝ} (hμ : 0 < μ) (p : ℝ) :
    0 < ∑ i, ∑ j,
      (meanStress ((2 : ℝ) • workShearA + p • 1) • 1 +
          convexProjection (convexHull ℝ ({0, workShearA} : Set (Matrix (Fin 3) (Fin 3) ℝ)))
            (deviatoricStress ((2 : ℝ) • workShearA + p • 1)) - 0) i j *
        Plasticity.plasticStrainIncrement μ ((2 : ℝ) • workShearA + p • 1)
          (meanStress ((2 : ℝ) • workShearA + p • 1) • 1 +
            convexProjection (convexHull ℝ ({0, workShearA} : Set (Matrix (Fin 3) (Fin 3) ℝ)))
              (deviatoricStress ((2 : ℝ) • workShearA + p • 1))) i j := by
  rw [workSeg_work]; exact inv_pos.mpr hμ

/-- Control: at `μ = -1` (outside the physical domain) the same witness has negative work. -/
example (p : ℝ) :
    ∑ i, ∑ j,
      (meanStress ((2 : ℝ) • workShearA + p • 1) • 1 +
          convexProjection (convexHull ℝ ({0, workShearA} : Set (Matrix (Fin 3) (Fin 3) ℝ)))
            (deviatoricStress ((2 : ℝ) • workShearA + p • 1)) - 0) i j *
        Plasticity.plasticStrainIncrement (-1) ((2 : ℝ) • workShearA + p • 1)
          (meanStress ((2 : ℝ) • workShearA + p • 1) • 1 +
            convexProjection (convexHull ℝ ({0, workShearA} : Set (Matrix (Fin 3) (Fin 3) ℝ)))
              (deviatoricStress ((2 : ℝ) • workShearA + p • 1))) i j < 0 := by
  rw [workSeg_work]; norm_num

/-- Pressure control: the pressure-dependent section `K = {1}` breaks the inequality. -/
example :
    ∑ i, ∑ j,
      (meanStress (1 : Matrix (Fin 3) (Fin 3) ℝ) • 1 + (1 : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j *
        Plasticity.plasticStrainIncrement (1 / 2) 1
          (meanStress (1 : Matrix (Fin 3) (Fin 3) ℝ) • 1 + 1) i j = -3 := by
  simp [Plasticity.plasticStrainIncrement, meanStress, Matrix.one_apply]

example : convexProjection ({1} : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (deviatoricStress 1) = 1 :=
  convexProjection_mem (Set.singleton_nonempty 1)
    (@IsCompact.isComplete _ Plasticity.frobeniusUniformSpace _
      (@isCompact_singleton _ Plasticity.frobeniusUniformSpace.toTopologicalSpace _))
    (convex_singleton 1) _

example : (1 : Matrix (Fin 3) (Fin 3) ℝ) ∉ Plasticity.deviatoricStresses := by
  rintro ⟨_, h⟩
  simp at h

/-- Unit symmetric shear in the 0-2 plane. -/
private def workShearB : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, 0, 0; 1, 0, 0]

/-- Anisotropic-scaling control: with the Frobenius return `s = workShearA` of
`x = 2 workShearA + workShearB` onto `[workShearA, workShearB]`, isotropic work
against `τ = workShearB` is `0 ≥ 0`, but the anisotropic increment with weight
`3` on the 0-2 shear (instead of the isotropic `1/(2μ)` scalar) gives `-4 < 0`. -/
example :
    ∑ i, ∑ j, (workShearA - workShearB) i j *
        ((2 : ℝ) • workShearA + workShearB - workShearA) i j = 0 ∧
    ∑ i, ∑ j, (workShearA - workShearB) i j *
      ((!![1, 1, 3; 1, 1, 1; 3, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ) i j *
        ((2 : ℝ) • workShearA + workShearB - workShearA) i j) = -4 := by
  constructor <;> simp [workShearA, workShearB, Fin.sum_univ_three] <;> norm_num

/-- The Frobenius projection of `2 workShearA + workShearB` onto
`[workShearA, workShearB]` is `workShearA`. -/
private lemma workSeg2_proj :
    convexProjection (convexHull ℝ ({workShearA, workShearB} : Set (Matrix (Fin 3) (Fin 3) ℝ)))
      ((2 : ℝ) • workShearA + workShearB) = workShearA := by
  have hne : (convexHull ℝ ({workShearA, workShearB} :
        Set (Matrix (Fin 3) (Fin 3) ℝ))).Nonempty :=
    ⟨workShearA, subset_convexHull ℝ _ (by simp)⟩
  have hv := convex_convexHull ℝ ({workShearA, workShearB} : Set (Matrix (Fin 3) (Fin 3) ℝ))
  have hA : workShearA ∈ convexHull ℝ ({workShearA, workShearB} :
        Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have hc : IsComplete (convexHull ℝ ({workShearA, workShearB} :
        Set (Matrix (Fin 3) (Fin 3) ℝ))) := by
    letI : TopologicalSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
      Plasticity.frobeniusUniformSpace.toTopologicalSpace
    exact @IsCompact.isComplete _ Plasticity.frobeniusUniformSpace _
      ((Set.toFinite _).isCompact_convexHull ℝ)
  refine convexProjection_eq_of_isNearestPoint hne hc hv hA ?_
  refine (norm_eq_iInf_iff_real_inner_le_zero hv hA).mpr ?_
  intro w hw
  rw [convexHull_pair, segment_eq_image] at hw
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hw
  rw [Plasticity.frobenius_inner_eq_sum_mul]
  simp [workShearA, workShearB, Fin.sum_univ_three]
  nlinarith
