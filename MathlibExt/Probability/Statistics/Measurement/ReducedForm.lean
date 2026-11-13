/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Covariance
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Linear SEM reduced form and covariance

Prove the reduced form and covariance identity for centered linear
structural equation models.

## References

- StataCorp (2017), Stata SEM Reference Manual Release 15,
  "methods and formulas for sem", "Model and parameterization".
- M. Drton (2016/2018), "Algebraic problems in structural equation
  modeling", arXiv:1612.05994, (2.1)-(2.2).
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ProbabilityTheory

/-- Reduced form equivalence for `v = B *ᵥ v + w` when `I - B` is a unit. -/
public theorem eq_inv_mulVec_iff {p : Type*} [Fintype p] [DecidableEq p]
  (B : Matrix p p ℝ) (v w : p → ℝ) (hdet : IsUnit (1 - B).det) :
  v = B *ᵥ v + w ↔ v = (1 - B)⁻¹ *ᵥ w := by
  have hN : (1 - B)⁻¹ * (1 - B) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hN' : (1 - B) * (1 - B)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  constructor
  · intro hv
    have h1 : (1 - B) *ᵥ v = w := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_eq_of_eq_add' hv
    have h2 : (1 - B)⁻¹ *ᵥ (1 - B) *ᵥ v = v := by
      rw [Matrix.mulVec_mulVec, hN, Matrix.one_mulVec]
    rw [h1] at h2
    exact h2.symm
  · intro hv
    have h3 : (1 - B) *ᵥ v = w := by
      rw [hv, Matrix.mulVec_mulVec, hN', Matrix.one_mulVec]
    have h4 : v - B *ᵥ v = w := by
      rw [← h3, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [← h4]
    abel

/-- Reduced form for structural equations with invertible `I - B`. -/
public theorem reducedForm_of_structural {p q : Type*} [Fintype p]
  [DecidableEq p] [Fintype q] {Ω : Type*} (B : Matrix p p ℝ)
  (Γ : Matrix p q ℝ) (y : Ω → p → ℝ) (x : Ω → q → ℝ)
  (ζ : Ω → p → ℝ) (hdet : IsUnit (1 - B).det)
  (hstruct : ∀ ω, y ω = B *ᵥ y ω + Γ *ᵥ x ω + ζ ω) :
  ∀ ω, y ω = (1 - B)⁻¹ *ᵥ (Γ *ᵥ x ω + ζ ω) := by
  intro ω
  have hω := hstruct ω
  rw [add_assoc] at hω
  exact (eq_inv_mulVec_iff B (y ω) (Γ *ᵥ x ω + ζ ω) hdet).mp hω

private theorem cov_univ_weighted {ι κ : Type*} [Fintype ι] [Fintype κ]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] (c : ι → ℝ) (d : κ → ℝ)
  (X : ι → Ω → ℝ) (Y : κ → Ω → ℝ)
  (hX : ∀ k, MemLp (X k) 2 P) (hY : ∀ l, MemLp (Y l) 2 P) :
  cov[fun ω => ∑ k, c k * X k ω, fun ω => ∑ l, d l * Y l ω; P] =
    ∑ k, ∑ l, c k * d l * cov[X k, Y l; P] := by
  have hX' : ∀ k, MemLp (fun ω => c k * X k ω) 2 P :=
    fun k => (hX k).const_mul (c k)
  have hY' : ∀ l, MemLp (fun ω => d l * Y l ω) 2 P :=
    fun l => (hY l).const_mul (d l)
  rw [ProbabilityTheory.covariance_fun_sum_fun_sum hX' hY']
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have hx : MemLp (X k) 2 P := hX k
  have hy : MemLp (Y l) 2 P := hY l
  have hx' : MemLp (fun ω => c k * X k ω) 2 P := hX' k
  have hy' : MemLp (fun ω => d l * Y l ω) 2 P := hY' l
  simp only [ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_const_mul_right]
  ring

private theorem cov_cross_zero {q : Type*} [Fintype q]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {p : Type*} (Γ : Matrix p q ℝ)
  (x : Ω → q → ℝ) (ζ : Ω → p → ℝ)
  (hx : ∀ k, MemLp (fun ω => x ω k) 2 P)
  (hζ : ∀ k, MemLp (fun ω => ζ ω k) 2 P)
  (hcross : ∀ k l, cov[fun ω => x ω k, fun ω => ζ ω l; P] = 0) :
  ∀ k l, cov[fun ω => ∑ t, Γ k t * x ω t, fun ω => ζ ω l; P] = 0 := by
  intro k l
  rw [ProbabilityTheory.covariance_fun_sum_left
    (fun t => (hx t).const_mul (Γ k t)) (hζ l)]
  apply Finset.sum_eq_zero
  intro t _
  rw [ProbabilityTheory.covariance_const_mul_left, hcross t l, mul_zero]

/-- Var(Y) = (I − B)⁻¹(ΓΦΓ′ + Ψ)((I − B)⁻¹)′
    (StataCorp sem methods and formulas; Drton (2.2));
    only second moments and zero cross covariance are used. -/
public theorem covariance_structural {p q : Type*} [Fintype p]
  [DecidableEq p] [Fintype q] {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] (B : Matrix p p ℝ)
  (Γ : Matrix p q ℝ) (Φ : Matrix q q ℝ) (Ψ : Matrix p p ℝ)
  (y : Ω → p → ℝ) (x : Ω → q → ℝ) (ζ : Ω → p → ℝ)
  (hdet : IsUnit (1 - B).det)
  (hstruct : ∀ ω, y ω = B *ᵥ y ω + Γ *ᵥ x ω + ζ ω)
  (hx : ∀ k, MemLp (fun ω => x ω k) 2 P)
  (hζ : ∀ k, MemLp (fun ω => ζ ω k) 2 P)
  (hΦ : ∀ k l, cov[fun ω => x ω k, fun ω => x ω l; P] = Φ k l)
  (hΨ : ∀ k l, cov[fun ω => ζ ω k, fun ω => ζ ω l; P] = Ψ k l)
  (hcross : ∀ k l, cov[fun ω => x ω k, fun ω => ζ ω l; P] = 0) :
  ∀ i j : p, cov[fun ω => y ω i, fun ω => y ω j; P] =
    ((1 - B)⁻¹ * (Γ * Φ * Γᵀ + Ψ) * ((1 - B)⁻¹)ᵀ : Matrix p p ℝ) i j := by
  intro i j
  have hred : ∀ ω, y ω = (1 - B)⁻¹ *ᵥ (Γ *ᵥ x ω + ζ ω) :=
    reducedForm_of_structural B Γ y x ζ hdet hstruct
  have heq_Γx : ∀ k, (fun ω => (Γ *ᵥ x ω) k) =
    fun ω => ∑ t, Γ k t * x ω t := by
    intro k
    funext ω
    simp [Matrix.mulVec, dotProduct]
  have hmem_Γx : ∀ k, MemLp (fun ω => (Γ *ᵥ x ω) k) 2 P := by
    intro k
    rw [heq_Γx k]
    exact MeasureTheory.memLp_finsetSum Finset.univ
      (fun t _ => (hx t).const_mul (Γ k t))
  have hmem_w : ∀ k, MemLp (fun ω => (Γ *ᵥ x ω) k + ζ ω k) 2 P :=
    fun k => (hmem_Γx k).add (hζ k)
  have hy_i : (fun ω => y ω i) = fun ω => ∑ k,
    (1 - B)⁻¹ i k * ((Γ *ᵥ x ω) k + ζ ω k) := by
    funext ω
    rw [hred ω]
    simp [Matrix.mulVec, dotProduct, Pi.add_apply]
  have hy_j : (fun ω => y ω j) = fun ω => ∑ k,
    (1 - B)⁻¹ j k * ((Γ *ᵥ x ω) k + ζ ω k) := by
    funext ω
    rw [hred ω]
    simp [Matrix.mulVec, dotProduct, Pi.add_apply]
  rw [hy_i, hy_j]
  rw [cov_univ_weighted _ _ _ _ hmem_w hmem_w]
  have hcov : ∀ k l,
    cov[fun ω => (Γ *ᵥ x ω) k + ζ ω k,
      fun ω => (Γ *ᵥ x ω) l + ζ ω l; P] =
      (∑ s, ∑ t, Γ k s * Γ l t * Φ s t) + Ψ k l := by
    intro k l
    have hmem_gk : MemLp (fun ω => (Γ *ᵥ x ω) k) 2 P := hmem_Γx k
    have hmem_gl : MemLp (fun ω => (Γ *ᵥ x ω) l) 2 P := hmem_Γx l
    have hmem_zk : MemLp (fun ω => ζ ω k) 2 P := hζ k
    have hmem_zl : MemLp (fun ω => ζ ω l) 2 P := hζ l
    have hxx : cov[fun ω => (Γ *ᵥ x ω) k,
      fun ω => (Γ *ᵥ x ω) l; P] =
      ∑ s, ∑ t, Γ k s * Γ l t * Φ s t := by
      have e1 : (fun ω => (Γ *ᵥ x ω) k) =
        fun ω => ∑ t, Γ k t * x ω t := heq_Γx k
      have e2 : (fun ω => (Γ *ᵥ x ω) l) =
        fun ω => ∑ t, Γ l t * x ω t := heq_Γx l
      rw [e1, e2]
      rw [cov_univ_weighted _ _ _ _ hx hx]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      rw [hΦ s t]
    have hxz : cov[fun ω => (Γ *ᵥ x ω) k, fun ω => ζ ω l; P] = 0 := by
      have e1 : (fun ω => (Γ *ᵥ x ω) k) =
        fun ω => ∑ t, Γ k t * x ω t := heq_Γx k
      rw [e1]
      exact cov_cross_zero Γ x ζ hx hζ hcross k l
    have hzx : cov[fun ω => ζ ω k, fun ω => (Γ *ᵥ x ω) l; P] = 0 := by
      rw [ProbabilityTheory.covariance_comm]
      have e2 : (fun ω => (Γ *ᵥ x ω) l) =
        fun ω => ∑ t, Γ l t * x ω t := heq_Γx l
      rw [e2]
      exact cov_cross_zero Γ x ζ hx hζ hcross l k
    have hzz : cov[fun ω => ζ ω k, fun ω => ζ ω l; P] = Ψ k l :=
      hΨ k l
    have hadd : cov[(fun ω => (Γ *ᵥ x ω) k) + (fun ω => ζ ω k),
        (fun ω => (Γ *ᵥ x ω) l) + (fun ω => ζ ω l); P]
        = (cov[(fun ω => (Γ *ᵥ x ω) k), (fun ω => (Γ *ᵥ x ω) l); P]
          + cov[(fun ω => (Γ *ᵥ x ω) k), (fun ω => ζ ω l); P])
        + (cov[(fun ω => ζ ω k), (fun ω => (Γ *ᵥ x ω) l); P]
          + cov[(fun ω => ζ ω k), (fun ω => ζ ω l); P]) :=
      calc cov[(fun ω => (Γ *ᵥ x ω) k) + (fun ω => ζ ω k),
              (fun ω => (Γ *ᵥ x ω) l) + (fun ω => ζ ω l); P]
          = cov[(fun ω => (Γ *ᵥ x ω) k),
              (fun ω => (Γ *ᵥ x ω) l) + (fun ω => ζ ω l); P]
            + cov[(fun ω => ζ ω k),
              (fun ω => (Γ *ᵥ x ω) l) + (fun ω => ζ ω l); P] :=
          ProbabilityTheory.covariance_add_left hmem_gk hmem_zk
            (hmem_gl.add hmem_zl)
        _ = (cov[(fun ω => (Γ *ᵥ x ω) k), (fun ω => (Γ *ᵥ x ω) l); P]
            + cov[(fun ω => (Γ *ᵥ x ω) k), (fun ω => ζ ω l); P])
          + (cov[(fun ω => ζ ω k), (fun ω => (Γ *ᵥ x ω) l); P]
            + cov[(fun ω => ζ ω k), (fun ω => ζ ω l); P]) := by
          rw [ProbabilityTheory.covariance_add_right hmem_gk hmem_gl hmem_zl,
            ProbabilityTheory.covariance_add_right hmem_zk hmem_gl hmem_zl]
    calc cov[fun ω => (Γ *ᵥ x ω) k + ζ ω k,
          fun ω => (Γ *ᵥ x ω) l + ζ ω l; P]
        = cov[(fun ω => (Γ *ᵥ x ω) k) + (fun ω => ζ ω k),
            (fun ω => (Γ *ᵥ x ω) l) + (fun ω => ζ ω l); P] := rfl
      _ = (cov[(fun ω => (Γ *ᵥ x ω) k), (fun ω => (Γ *ᵥ x ω) l); P]
          + cov[(fun ω => (Γ *ᵥ x ω) k), (fun ω => ζ ω l); P])
        + (cov[(fun ω => ζ ω k), (fun ω => (Γ *ᵥ x ω) l); P]
          + cov[(fun ω => ζ ω k), (fun ω => ζ ω l); P]) := hadd
      _ = (∑ s, ∑ t, Γ k s * Γ l t * Φ s t) + Ψ k l := by
        rw [hxx, hxz, hzx, hzz]
        ring
  have hC : ∀ k l, (Γ * Φ * Γᵀ + Ψ : Matrix p p ℝ) k l =
    (∑ s, ∑ t, Γ k s * Γ l t * Φ s t) + Ψ k l := by
    intro k l
    simp only [Matrix.add_apply]
    congr 1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hRHS : ((1 - B)⁻¹ * (Γ * Φ * Γᵀ + Ψ) * ((1 - B)⁻¹)ᵀ : Matrix p p ℝ) i j =
    ∑ k, ∑ l, (1 - B)⁻¹ i k * (Γ * Φ * Γᵀ + Ψ) k l * (1 - B)⁻¹ j l := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  simp only [hcov]
  rw [hRHS]
  simp only [hC]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end MathlibExt.Probability.Statistics.Measurement
