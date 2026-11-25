/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Elasticity.StressStrain
public import MathlibExt.Analysis.InnerProductSpace.ConvexProjection
public import Mathlib.Analysis.Matrix.Order

/-!
# Deviatoric return map in the Frobenius metric

## i. Overview

Stresses and strains are real `3 × 3` matrices (no Voigt or Mandel
vector), with tension-positive Cauchy stress. The metric is Mathlib's
matrix inner product at the identity weight,
`Matrix.toMatrixNormedAddCommGroup (Fin 3) 1 Matrix.PosDef.one` and
`Matrix.toMatrixInnerProductSpace (Fin 3) 1 Matrix.PosDef.one.posSemidef`, so
`⟪A, B⟫_ℝ = ∑ i, ∑ j, A i j * B i j`: the full double contraction
`A : B`, in which each off-diagonal shear pair of a symmetric tensor is
counted twice. These Frobenius structures are scoped instances in the
`Plasticity` namespace: importing this module alone does not replace the
metric structures on `Matrix (Fin 3) (Fin 3) ℝ`; consumers opt in with
`open scoped Plasticity`. The norm-induced uniform structure then has
high priority (equivalent to the entrywise matrix uniformity in finite
dimension, but not definitionally equal), so `IsComplete K` here is
completeness in the Frobenius metric; no closedness or compactness
claim is made in the entrywise topology.

A trial stress `σTrial` is symmetric; its deviator is
`Elasticity.deviatoricStress σTrial`. The admissible deviatoric
stresses are the symmetric trace-free matrices, and the yield section
`K` is a fixed nonempty complete convex subset of them
(pressure-insensitive: it constrains only the deviator). The returned
deviator is the canonical nearest-point projection
`convexProjection K (Elasticity.deviatoricStress σTrial)`, the returned
stress keeps the trial mean stress, and the isotropic plastic strain
increment is `Δε_p = (2 * μ)⁻¹ • (σTrial - σ)` at shear modulus `μ > 0`
(Lean totalizes `(2 * 0)⁻¹ = 0`; targets needing `μ ≠ 0` assume
`0 < μ`). No hardening and no volumetric plastic strain. Units: stress
in force/area, `μ` in force/area, strain dimensionless.

Out of scope: any new projection or nonexpansiveness theorem (the
canonical `convexProjection` API is reused), hardening, anisotropic
return algorithms (a general elastic tensor needs its compliance
metric), and pressure-dependent yield laws such as Cam-Clay or
Drucker-Prager, whose admissible sets contain stresses of nonzero trace
and so violate the premise `K ⊆ deviatoricStresses`.

## ii. Key results

- `Plasticity.frobenius_inner_eq_sum_mul`: the locked inner product is
  the full double contraction.
- `Plasticity.deviatoric_return`: the return map and its isotropic
  corrector, including admissibility, reconstruction, and zero
  correction inside `K`.
- `Plasticity.deviatoric_return_firmly_nonexpansive`: firm
  nonexpansiveness of the return with the `2 μ` scaling.
- `Plasticity.eq_projection_iff_energy_le`: the return is the
  closest point in the isotropic complementary-energy metric.
- `Plasticity.deviatoric_return_maximum_plastic_work`: maximum plastic
  work of the returned stress against every admissible comparison.

## iii. Table of contents

- A. Frobenius carrier and admissibility
- B. Return map
- C. Stability and energy characterization
- D. Plastic work

## iv. References

- J. C. Simo and T. J. R. Hughes, *Computational Inelasticity*,
  Springer, 1998, ch. 7 (return mapping for perfect plasticity).
- `PhyslibExt.CondensedMatter.Elasticity.StressStrain` for
  `Elasticity.deviatoricStress` and `Elasticity.meanStress`.
- `MathlibExt.Analysis.InnerProductSpace.ConvexProjection` for the
  canonical nearest-point projection.
-/

@[expose] public section

local notation "𝕄" => Matrix (Fin 3) (Fin 3) ℝ

namespace Plasticity

open scoped InnerProductSpace Matrix
open MathlibExt.Analysis.InnerProductSpace.ConvexProjection
open Elasticity

/-! ## A. Frobenius carrier and admissibility -/

/-- Full Frobenius norm on `3 × 3` real matrices, `‖A‖ = √(A * 1 * Aᴴ).trace`. -/
noncomputable scoped instance frobeniusNormedAddCommGroup : NormedAddCommGroup 𝕄 :=
  Matrix.toMatrixNormedAddCommGroup (Fin 3) 1 Matrix.PosDef.one

/-- Full Frobenius inner product on `3 × 3` real matrices, `⟪A, B⟫ = (B * 1 * Aᴴ).trace`. -/
noncomputable scoped instance frobeniusInnerProductSpace : InnerProductSpace ℝ 𝕄 :=
  Matrix.toMatrixInnerProductSpace (Fin 3) 1 Matrix.PosDef.one.posSemidef

/-- Uniform structure of the Frobenius norm, preferred over the entrywise matrix uniformity. -/
noncomputable scoped instance (priority := high) frobeniusUniformSpace : UniformSpace 𝕄 :=
  PseudoMetricSpace.toUniformSpace

/-- The Frobenius inner product space sits over the Frobenius normed group (instance check). -/
example : (NormedAddCommGroup.toSeminormedAddCommGroup : SeminormedAddCommGroup 𝕄) =
    Matrix.toMatrixSeminormedAddCommGroup (Fin 3) 1 Matrix.PosDef.one.posSemidef :=
  rfl

/-- Admissible deviatoric stresses: symmetric trace-free `3 × 3` matrices. -/
def deviatoricStresses : Set 𝕄 := {σ | IsSymmetricStress σ ∧ σ.trace = 0}

/-- Isotropic plastic strain increment `Δε_p = (σTrial - σ) / (2 μ)`, `μ` the shear modulus. -/
noncomputable def plasticStrainIncrement (μ : ℝ) (σTrial σ : 𝕄) : 𝕄 :=
  (2 * μ)⁻¹ • (σTrial - σ)

/-- Metric identity: the locked inner product is the full double contraction
`A : B = ∑ i, ∑ j, A i j * B i j`, so for symmetric tensors each off-diagonal shear pair
contributes twice, as in the stress power `σ : ε`. -/
theorem frobenius_inner_eq_sum_mul (A B : 𝕄) : ⟪A, B⟫_ℝ = ∑ i, ∑ j, A i j * B i j := by
  show (B * 1 * Aᴴ).trace = ∑ i, ∑ j, A i j * B i j
  rw [Matrix.mul_one]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_trivial]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/-! ## B. Return map -/

/-- Deviatoric return map with isotropic corrector. For a symmetric trial stress `σTrial`, a
shear modulus `μ > 0` and a fixed nonempty complete convex yield section `K` of symmetric
trace-free stresses, put `s := convexProjection K (deviatoricStress σTrial)` and
`σ := meanStress σTrial • 1 + s`. Then the trial deviator is symmetric trace-free, `s ∈ K`, the
returned stress `σ` is symmetric with the trial mean stress and deviator `s`, the plastic strain
increment `(σTrial - σ) / (2 μ)` equals `(deviatoricStress σTrial - s) / (2 μ)` and is symmetric
trace-free (no volumetric plastic strain), `σ = σTrial - 2 μ Δε_p`, and a trial deviator already
in `K` gives zero correction. -/
theorem deviatoric_return
    {μ : ℝ} (hμ : 0 < μ) {K : Set 𝕄} (hKne : K.Nonempty) (hKc : IsComplete K)
    (hKv : Convex ℝ K) (hKdev : K ⊆ deviatoricStresses) {σTrial : 𝕄}
    (hσTrial : IsSymmetricStress σTrial) :
    deviatoricStress σTrial ∈ deviatoricStresses ∧
      convexProjection K (deviatoricStress σTrial) ∈ K ∧
      IsSymmetricStress (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) ∧
      meanStress (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) =
        meanStress σTrial ∧
      deviatoricStress (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) =
        convexProjection K (deviatoricStress σTrial) ∧
      plasticStrainIncrement μ σTrial
          (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) =
        plasticStrainIncrement μ (deviatoricStress σTrial)
          (convexProjection K (deviatoricStress σTrial)) ∧
      plasticStrainIncrement μ σTrial
          (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) ∈
        deviatoricStresses ∧
      meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial) = σTrial - (2 * μ) •
        plasticStrainIncrement μ σTrial
          (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) ∧
      (deviatoricStress σTrial ∈ K →
        plasticStrainIncrement μ σTrial
          (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) = 0 ∧
        meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial) = σTrial) := by
  have hσTrialT : σTrialᵀ = σTrial := hσTrial
  have hsK : convexProjection K (deviatoricStress σTrial) ∈ K := convexProjection_mem hKne hKc hKv _
  have hsdev : IsSymmetricStress (convexProjection K (deviatoricStress σTrial))
      ∧ (convexProjection K (deviatoricStress σTrial)).trace = 0 := hKdev hsK
  have hsT : (convexProjection K (deviatoricStress σTrial))ᵀ
      = convexProjection K (deviatoricStress σTrial) := hsdev.1
  have hstr : (convexProjection K (deviatoricStress σTrial)).trace = 0 := hsdev.2
  have hdevT : (deviatoricStress σTrial)ᵀ = deviatoricStress σTrial := by
    simp only [deviatoricStress, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, hσTrialT]
  have hdevtr : (deviatoricStress σTrial).trace = 0 := by
    simp only [deviatoricStress, meanStress, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    ring
  have hσT : (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial))ᵀ
      = meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial) := by
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hsT]
  have hσtr : (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)).trace
      = σTrial.trace := by
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      hstr, smul_eq_mul, add_zero, meanStress]
    ring
  have hσmean : meanStress (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial))
      = meanStress σTrial :=
    congrArg (fun t => t / 3) hσtr
  have hσdev : deviatoricStress
        (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial))
      = convexProjection K (deviatoricStress σTrial) := by
    show meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial) -
        meanStress (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) • 1 = _
    rw [hσmean]
    exact add_sub_cancel_left _ _
  have hΔeq : plasticStrainIncrement μ σTrial
        (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial))
      = plasticStrainIncrement μ (deviatoricStress σTrial)
        (convexProjection K (deviatoricStress σTrial)) := by
    simp only [plasticStrainIncrement, deviatoricStress]
    congr 1
    abel
  have hDsymm : (σTrial - (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)))ᵀ
      = σTrial - (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) := by
    simp only [Matrix.transpose_sub, hσTrialT, hσT]
  have hDtr : (σTrial -
        (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial))).trace
      = 0 := by
    simp only [Matrix.trace_sub, hσtr, sub_self]
  have hΔmem : plasticStrainIncrement μ σTrial
        (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial))
      ∈ deviatoricStresses := by
    simp only [plasticStrainIncrement]
    refine ⟨?_, ?_⟩
    · unfold IsSymmetricStress
      simp only [Matrix.transpose_smul, hDsymm]
    · simp only [Matrix.trace_smul, hDtr, smul_zero]
  have h2μ : (2 : ℝ) * μ ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hμ)
  have hσback : meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)
      = σTrial - (2 * μ) • plasticStrainIncrement μ σTrial
        (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) := by
    simp only [plasticStrainIncrement, smul_inv_smul₀ h2μ, sub_sub_cancel]
  have hσfix : meanStress σTrial • 1 + deviatoricStress σTrial = σTrial := by
    simp only [deviatoricStress, add_sub_cancel]
  refine ⟨⟨hdevT, hdevtr⟩, hsK, hσT, hσmean, hσdev, hΔeq, hΔmem, hσback, ?_⟩
  intro hKmem
  have hPfix : convexProjection K (deviatoricStress σTrial) = deviatoricStress σTrial :=
    convexProjection_eq_self_of_mem hKne hKc hKv hKmem
  refine ⟨?_, ?_⟩
  · simp only [plasticStrainIncrement, hPfix, hσfix, sub_self, smul_zero]
  · rw [hPfix]
    exact hσfix

private theorem norm_sq_eq_sum_sq (A : 𝕄) : ‖A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, frobenius_inner_eq_sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

private theorem sum_sub_sq_eq_norm (X Y : 𝕄) :
    (∑ i, ∑ j, (X i j - Y i j) ^ 2) = ‖X - Y‖ ^ 2 := by
  rw [norm_sq_eq_sum_sq]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [Matrix.sub_apply]

/-! ## C. Stability and energy characterization -/

/-- Firm nonexpansiveness of the deviatoric return with the isotropic `2 μ` scaling: for two
trial stresses, the squared Frobenius distance between the returned deviators plus `(2 μ) ^ 2`
times the squared Frobenius distance between the plastic strain increments is at most the squared
Frobenius distance between the trial deviators. Physically `μ > 0`; the inequality holds for every
real `μ` (for `μ = 0` the totalized increments vanish). -/
theorem deviatoric_return_firmly_nonexpansive
    (μ : ℝ) {K : Set 𝕄} (hKne : K.Nonempty) (hKc : IsComplete K) (hKv : Convex ℝ K)
    (σ₁ σ₂ : 𝕄) :
    ∑ i, ∑ j, (convexProjection K (deviatoricStress σ₁) i j
        - convexProjection K (deviatoricStress σ₂) i j) ^ 2 +
        (2 * μ) ^ 2 * ∑ i, ∑ j,
          (plasticStrainIncrement μ (deviatoricStress σ₁)
              (convexProjection K (deviatoricStress σ₁)) i j -
            plasticStrainIncrement μ (deviatoricStress σ₂)
              (convexProjection K (deviatoricStress σ₂)) i j) ^ 2 ≤
      ∑ i, ∑ j, (deviatoricStress σ₁ i j - deviatoricStress σ₂ i j) ^ 2 := by
  simp only [sum_sub_sq_eq_norm]
  have hΔsub : plasticStrainIncrement μ (deviatoricStress σ₁)
        (convexProjection K (deviatoricStress σ₁)) -
        plasticStrainIncrement μ (deviatoricStress σ₂) (convexProjection K (deviatoricStress σ₂))
      = (2 * μ)⁻¹ • ((deviatoricStress σ₁ - convexProjection K (deviatoricStress σ₁)) -
          (deviatoricStress σ₂ - convexProjection K (deviatoricStress σ₂))) := by
    simp only [plasticStrainIncrement, ← smul_sub]
  by_cases h0 : (2 : ℝ) * μ = 0
  · have hinv : ((2 : ℝ) * μ)⁻¹ = 0 := inv_eq_zero.mpr h0
    have hΔ0 : plasticStrainIncrement μ (deviatoricStress σ₁)
          (convexProjection K (deviatoricStress σ₁)) -
          plasticStrainIncrement μ (deviatoricStress σ₂)
            (convexProjection K (deviatoricStress σ₂)) = 0 := by
      rw [hΔsub, hinv, zero_smul]
    rw [hΔ0, norm_zero]
    norm_num
    calc ‖convexProjection K (deviatoricStress σ₁) - convexProjection K (deviatoricStress σ₂)‖ ^ 2
        ≤ ‖convexProjection K (deviatoricStress σ₁)
            - convexProjection K (deviatoricStress σ₂)‖ ^ 2 +
            ‖(deviatoricStress σ₁ - convexProjection K (deviatoricStress σ₁)) -
              (deviatoricStress σ₂ - convexProjection K (deviatoricStress σ₂))‖ ^ 2 :=
          le_add_of_nonneg_right (sq_nonneg _)
      _ ≤ ‖deviatoricStress σ₁ - deviatoricStress σ₂‖ ^ 2 :=
          convexProjection_firmly_nonexpansive hKne hKc hKv _ _
  · have hscalar : (2 * μ) ^ 2 * ‖((2 : ℝ) * μ)⁻¹‖ ^ 2 = 1 := by
      rw [Real.norm_eq_abs, sq_abs, ← mul_pow, mul_inv_cancel₀ h0, one_pow]
    have hscale : (2 * μ) ^ 2 *
          ‖plasticStrainIncrement μ (deviatoricStress σ₁)
              (convexProjection K (deviatoricStress σ₁)) -
            plasticStrainIncrement μ (deviatoricStress σ₂)
              (convexProjection K (deviatoricStress σ₂))‖ ^ 2
        = ‖(deviatoricStress σ₁ - convexProjection K (deviatoricStress σ₁)) -
            (deviatoricStress σ₂ - convexProjection K (deviatoricStress σ₂))‖ ^ 2 := by
      rw [hΔsub, norm_smul]
      have hmp : (‖((2 : ℝ) * μ)⁻¹‖ *
            ‖(deviatoricStress σ₁ - convexProjection K (deviatoricStress σ₁)) -
              (deviatoricStress σ₂ - convexProjection K (deviatoricStress σ₂))‖) ^ 2
          = ‖((2 : ℝ) * μ)⁻¹‖ ^ 2 *
            ‖(deviatoricStress σ₁ - convexProjection K (deviatoricStress σ₁)) -
              (deviatoricStress σ₂ - convexProjection K (deviatoricStress σ₂))‖ ^ 2 :=
        mul_pow _ _ _
      rw [hmp, ← mul_assoc, hscalar, one_mul]
    rw [hscale]
    exact convexProjection_firmly_nonexpansive hKne hKc hKv _ _

private theorem energy_eq_norm_sq (μ : ℝ) (D : 𝕄) :
    μ * ∑ i, ∑ j, (((2 * μ)⁻¹ • D) i j) ^ 2
      = (μ * ((2 * μ)⁻¹) ^ 2) * ‖D‖ ^ 2 := by
  have hpt : ∀ i j, (((2 * μ)⁻¹ • D) i j) ^ 2
      = ((2 * μ)⁻¹) ^ 2 * (D i j) ^ 2 := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, mul_pow]
  simp only [hpt, ← Finset.mul_sum, norm_sq_eq_sum_sq]
  ring

/-- Closest-point characterization in the isotropic energy metric: for `μ > 0` and a nonempty
complete convex `K`, the projection of `sTrial` is `s` iff `s ∈ K` and `s` minimizes
`μ ‖Δε_p‖² = μ ∑ i, ∑ j, ((sTrial - τ) / (2 μ)) i j ^ 2` over `τ ∈ K`. For a trace-free trial
stress and `K` of trace-free stresses this is the complementary elastic energy
`‖sTrial - τ‖² / (4 μ)` of the plastic stress correction, so the energy-metric return is the
Frobenius projection. The equivalence holds for every trial matrix. -/
theorem eq_projection_iff_energy_le
    {μ : ℝ} (hμ : 0 < μ) {K : Set 𝕄} (hKne : K.Nonempty) (hKc : IsComplete K)
    (hKv : Convex ℝ K) (sTrial s : 𝕄) :
    convexProjection K sTrial = s ↔ s ∈ K ∧ ∀ τ ∈ K,
      μ * ∑ i, ∑ j, plasticStrainIncrement μ sTrial s i j ^ 2 ≤
        μ * ∑ i, ∑ j, plasticStrainIncrement μ sTrial τ i j ^ 2 := by
  have h2μ : (2 : ℝ) * μ ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hμ)
  have hC : 0 < μ * ((2 * μ)⁻¹) ^ 2 :=
    mul_pos hμ (sq_pos_of_ne_zero (inv_ne_zero h2μ))
  have hE : ∀ τ : 𝕄, μ * ∑ i, ∑ j, plasticStrainIncrement μ sTrial τ i j ^ 2
      = (μ * ((2 * μ)⁻¹) ^ 2) * ‖sTrial - τ‖ ^ 2 := by
    intro τ
    simp only [plasticStrainIncrement]
    exact energy_eq_norm_sq μ (sTrial - τ)
  have hbdd : BddBelow (Set.range fun w : K => ‖sTrial - w‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  constructor
  · intro hPs
    subst hPs
    refine ⟨convexProjection_mem hKne hKc hKv _, ?_⟩
    intro τ hτ
    rw [hE, hE]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    rw [convexProjection_norm_eq_iInf hKne hKc hKv]
    exact ciInf_le hbdd ⟨τ, hτ⟩
  · rintro ⟨hsK, hmin⟩
    have _nonempty : Nonempty K := hKne.to_subtype
    refine convexProjection_eq_of_isNearestPoint hKne hKc hKv hsK ?_
    apply le_antisymm
    · apply le_ciInf
      intro w
      have hmw := hmin w w.2
      rw [hE, hE] at hmw
      have hsq : ‖sTrial - s‖ ^ 2 ≤ ‖sTrial - w‖ ^ 2 :=
        le_of_mul_le_mul_left hmw hC
      exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq
    · exact ciInf_le hbdd ⟨s, hsK⟩

/-! ## D. Plastic work -/

private lemma inner_smul_one (c : ℝ) (B : 𝕄) : ⟪c • 1, B⟫_ℝ = c * B.trace := by
  rw [frobenius_inner_eq_sum_mul]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum]
  congr 1

/-- Maximum plastic work for the deviatoric return. For a trial stress `σTrial`, a shear modulus
`μ > 0` and a fixed nonempty complete convex yield section `K` of symmetric trace-free stresses,
let `σ := meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)` be the returned
stress and
`Δε_p := (σTrial - σ) / (2 μ)` the isotropic plastic strain increment. Then every admissible
stress `τ ∈ K` satisfies `(σ - τ) : Δε_p = ∑ i, ∑ j, (σ - τ) i j * Δε_p i j ≥ 0`: for
every admissible comparison stress `τ ∈ K`, the returned stress `σ` (which itself need not
lie in `K`, since it carries the trial mean stress) does at least as much plastic work on
`Δε_p` as `τ`. The hydrostatic
part of `σ` does no plastic work because `Δε_p` is trace-free, which uses `K ⊆ deviatoricStresses`
(pressure insensitivity). No symmetry of `σTrial` is needed. -/
theorem deviatoric_return_maximum_plastic_work
    {μ : ℝ} (hμ : 0 < μ) {K : Set 𝕄} (hKne : K.Nonempty) (hKc : IsComplete K)
    (hKv : Convex ℝ K) (hKdev : K ⊆ deviatoricStresses) (σTrial : 𝕄) :
    ∀ τ ∈ K, 0 ≤ ∑ i, ∑ j,
      (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial) - τ) i j *
        plasticStrainIncrement μ σTrial
          (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial))
          i j := by
  intro τ hτ
  have hmemP : convexProjection K (deviatoricStress σTrial) ∈ K :=
    convexProjection_mem hKne hKc hKv _
  have hp0 : (convexProjection K (deviatoricStress σTrial)).trace = 0 := (hKdev hmemP).2
  have hs0 : (deviatoricStress σTrial).trace = 0 := trace_deviatoric σTrial
  have htr : (deviatoricStress σTrial -
        convexProjection K (deviatoricStress σTrial)).trace = 0 := by
    rw [Matrix.trace_sub, hs0, hp0, sub_zero]
  have hsub : σTrial - (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial))
      = deviatoricStress σTrial - convexProjection K (deviatoricStress σTrial) := by
    unfold deviatoricStress
    abel
  have hΔ : plasticStrainIncrement μ σTrial
        (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial))
      = (2 * μ)⁻¹ • (deviatoricStress σTrial -
        convexProjection K (deviatoricStress σTrial)) := by
    unfold plasticStrainIncrement
    rw [hsub]
  have hsum : (∑ i, ∑ j, (meanStress σTrial • 1 +
        convexProjection K (deviatoricStress σTrial) - τ) i j *
        plasticStrainIncrement μ σTrial
          (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial)) i j)
      = ⟪meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial) - τ,
        plasticStrainIncrement μ σTrial
          (meanStress σTrial • 1 + convexProjection K (deviatoricStress σTrial))⟫_ℝ :=
    (frobenius_inner_eq_sum_mul _ _).symm
  have hX : ⟪convexProjection K (deviatoricStress σTrial),
        deviatoricStress σTrial - convexProjection K (deviatoricStress σTrial)⟫_ℝ
      - ⟪τ, deviatoricStress σTrial - convexProjection K (deviatoricStress σTrial)⟫_ℝ
      = -⟪deviatoricStress σTrial - convexProjection K (deviatoricStress σTrial),
        τ - convexProjection K (deviatoricStress σTrial)⟫_ℝ := by
    have hneg : convexProjection K (deviatoricStress σTrial) - τ
        = -(τ - convexProjection K (deviatoricStress σTrial)) := by abel
    rw [← inner_sub_left, hneg, inner_neg_left, real_inner_comm]
  have hvar' := convexProjection_variational hKne hKc hKv (deviatoricStress σTrial) τ hτ
  have hpos : (0 : ℝ) < (2 * μ)⁻¹ := inv_pos.mpr (by linarith)
  rw [hsum, hΔ, inner_smul_right, inner_sub_left, inner_add_left, inner_smul_one, htr,
    mul_zero, zero_add, hX]
  exact mul_nonneg hpos.le (neg_nonneg.mpr hvar')

end Plasticity
