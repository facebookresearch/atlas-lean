/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Metrizable.ContinuousMap

@[expose] public section

open scoped ENNReal

section
namespace MathlibExt.Analysis.FunctionalAnalysis.KreinRutmanWanted

-- N1
private theorem kr_pos_opNorm_le_norm_apply_one
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : C(K, ℝ) →L[ℝ] C(K, ℝ))
    (hA : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (A f) x) :
    ‖A‖ ≤ ‖A 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (f := A) (norm_nonneg _) ?_
  intro f
  have habs : ∀ y, |f y| ≤ ‖f‖ := by
    intro y
    have h := ContinuousMap.norm_coe_le_norm f y
    rwa [Real.norm_eq_abs] at h
  have hfn : ∀ y, f y ≤ ‖f‖ := fun y => le_trans (le_abs_self _) (habs y)
  have hfn2 : ∀ y, -‖f‖ ≤ f y := fun y => (abs_le.mp (habs y)).1
  have hpos1 : ∀ y, 0 ≤ (‖f‖ • (1 : C(K, ℝ)) - f) y := by
    intro y
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one]
    linarith [hfn y]
  have hpos2 : ∀ y, 0 ≤ (‖f‖ • (1 : C(K, ℝ)) + f) y := by
    intro y
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one]
    linarith [hfn2 y]
  have hA1 := hA _ hpos1
  have hA2 := hA _ hpos2
  have e1 : ∀ x, (A (‖f‖ • 1 - f)) x = ‖f‖ * (A 1) x - (A f) x := by
    intro x
    simp [map_sub, smul_eq_mul]
  have e2 : ∀ x, (A (‖f‖ • 1 + f)) x = ‖f‖ * (A 1) x + (A f) x := by
    intro x
    simp [map_add, smul_eq_mul]
  have hA1le : ∀ y, |(A 1) y| ≤ ‖A 1‖ := by
    intro y
    have h := ContinuousMap.norm_coe_le_norm (A 1) y
    rwa [Real.norm_eq_abs] at h
  have hpoint : ∀ x, |(A f) x| ≤ ‖A 1‖ * ‖f‖ := by
    intro x
    have g1 : 0 ≤ ‖f‖ * (A 1) x - (A f) x := by rw [← e1 x]; exact hA1 x
    have g2 : 0 ≤ ‖f‖ * (A 1) x + (A f) x := by rw [← e2 x]; exact hA2 x
    have hub := hA1le x
    rw [abs_le]
    constructor
    · have hle : -(‖f‖ * (A 1) x) ≤ (A f) x := by linarith
      calc -(‖A 1‖ * ‖f‖) ≤ -(‖f‖ * (A 1) x) := by
            apply neg_le_neg
            calc ‖f‖ * (A 1) x ≤ ‖f‖ * |(A 1) x| :=
                  mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _)
              _ ≤ ‖f‖ * ‖A 1‖ := mul_le_mul_of_nonneg_left hub (norm_nonneg _)
              _ = ‖A 1‖ * ‖f‖ := mul_comm _ _
        _ ≤ (A f) x := hle
    · have hle : (A f) x ≤ ‖f‖ * (A 1) x := by linarith
      calc (A f) x ≤ ‖f‖ * (A 1) x := hle
        _ ≤ ‖f‖ * |(A 1) x| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _)
        _ ≤ ‖f‖ * ‖A 1‖ := mul_le_mul_of_nonneg_left hub (norm_nonneg _)
        _ = ‖A 1‖ * ‖f‖ := mul_comm _ _
  have hbound : ∀ x, ‖(A f) x‖ ≤ ‖A 1‖ * ‖f‖ := by
    intro x
    rw [Real.norm_eq_abs]
    exact hpoint x
  exact (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hbound

-- N2
private theorem kr_isUnit_one_sub_and_inverse_pos
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : C(K, ℝ) →L[ℝ] C(K, ℝ))
    (hA : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (A f) x)
    (hlt : ‖A‖ < 1) :
    IsUnit (1 - A) ∧ ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (Ring.inverse (1 - A) f) x := by
  constructor
  · exact ⟨_, Units.val_oneSub A hlt⟩
  · have hpow : ∀ n : ℕ, ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ ((A ^ n) f) x := by
      intro n
      induction n with
      | zero =>
        intro f hf x
        simpa using hf x
      | succ n ih =>
        intro f hf x
        have h1 : ∀ y, 0 ≤ ((A ^ n) f) y := ih f hf
        have h2 := hA _ h1 x
        have heq : ((A ^ (n + 1)) f) x = (A ((A ^ n) f)) x := by
          rw [pow_succ']
          rfl
        rw [heq]
        exact h2
    intro f hf x
    have hsum : Summable (fun n : ℕ => A ^ n) := summable_geometric_of_norm_lt_one (x := A) hlt
    have hs := hsum.hasSum
    have hval : (∑' n : ℕ, A ^ n) = Ring.inverse (1 - A) := geom_series_eq_inverse A hlt
    let g : (C(K, ℝ) →L[ℝ] C(K, ℝ)) →+ ℝ :=
      { toFun := fun B => (B f) x
        map_zero' := by simp
        map_add' := by intro B C; simp }
    have hcont : Continuous (fun B : C(K, ℝ) →L[ℝ] C(K, ℝ) => (B f) x) :=
      (continuous_eval_const x).comp (continuous_eval_const f)
    have hcont' : Continuous (⇑g) := hcont
    have h2 : HasSum (⇑g ∘ (fun n : ℕ => A ^ n)) (g (∑' n : ℕ, A ^ n)) :=
      HasSum.map hs g hcont'
    rw [hval] at h2
    have h3 : HasSum (fun n : ℕ => ((A ^ n) f) x) ((Ring.inverse (1 - A) f) x) := h2
    exact HasSum.nonneg (fun n => hpow n f hf x) h3

-- N3
private theorem kr_resolvent_sub_eq
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (S : A) (ν : ℝ) (hν : ν ∈ resolventSet ℝ S) (t : ℝ)
    (ht : ‖t • resolvent S ν‖ < 1) :
    ν - t ∈ resolventSet ℝ S ∧
    resolvent S (ν - t) = Ring.inverse (1 - t • resolvent S ν) * resolvent S ν := by
  have hu : IsUnit (algebraMap ℝ A ν - S) :=
    (spectrum.mem_resolventSet_iff).mp hν
  have hR : resolvent S ν = Ring.inverse (algebraMap ℝ A ν - S) := rfl
  have h1 : (algebraMap ℝ A ν - S) * Ring.inverse (algebraMap ℝ A ν - S) = 1 :=
    Ring.mul_inverse_cancel _ hu
  have h2 : Ring.inverse (algebraMap ℝ A ν - S) * (algebraMap ℝ A ν - S) = 1 :=
    Ring.inverse_mul_cancel _ hu
  have hcomm : Commute (algebraMap ℝ A ν - S) (resolvent S ν) := by
    change (algebraMap ℝ A ν - S) * resolvent S ν = resolvent S ν * (algebraMap ℝ A ν - S)
    rw [hR, h1, h2]
  have hsmul : (algebraMap ℝ A ν - S) * (t • resolvent S ν)
      = (t • resolvent S ν) * (algebraMap ℝ A ν - S) := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hcomm.eq]
  have hCsmul : Commute (algebraMap ℝ A ν - S) (t • resolvent S ν) := hsmul
  have hcomm2 : Commute (algebraMap ℝ A ν - S) (1 - t • resolvent S ν) :=
    (Commute.one_right _).sub_right hCsmul
  have hunit12 : IsUnit (1 - t • resolvent S ν) :=
    ⟨_, Units.val_oneSub _ ht⟩
  have hkey : (algebraMap ℝ A ν - S) * (1 - t • resolvent S ν)
      = algebraMap ℝ A (ν - t) - S := by
    have e1 : (algebraMap ℝ A ν - S) * (t • resolvent S ν)
        = t • ((algebraMap ℝ A ν - S) * resolvent S ν) := Algebra.mul_smul_comm _ _ _
    have e2 : (algebraMap ℝ A ν - S) * resolvent S ν = 1 := by
      rw [hR]; exact h1
    have e3 : t • (1 : A) = algebraMap ℝ A t := (Algebra.algebraMap_eq_smul_one t).symm
    calc (algebraMap ℝ A ν - S) * (1 - t • resolvent S ν)
        = (algebraMap ℝ A ν - S) - (algebraMap ℝ A ν - S) * (t • resolvent S ν) := by
          rw [mul_sub, mul_one]
      _ = (algebraMap ℝ A ν - S) - t • ((algebraMap ℝ A ν - S) * resolvent S ν) := by rw [e1]
      _ = (algebraMap ℝ A ν - S) - t • (1 : A) := by rw [e2]
      _ = (algebraMap ℝ A ν - S) - algebraMap ℝ A t := by rw [e3]
      _ = algebraMap ℝ A (ν - t) - S := by rw [map_sub]; abel
  have hunit : IsUnit (algebraMap ℝ A (ν - t) - S) := by
    rw [← hkey]
    exact hu.mul hunit12
  constructor
  · exact (spectrum.mem_resolventSet_iff).mpr hunit
  · have hform : Ring.inverse (algebraMap ℝ A (ν - t) - S)
        = Ring.inverse (1 - t • resolvent S ν) * Ring.inverse (algebraMap ℝ A ν - S) := by
      rw [← hkey]
      exact Ring.mul_inverse_rev' hcomm2
    have r1 : resolvent S (ν - t) = Ring.inverse (algebraMap ℝ A (ν - t) - S) := rfl
    rw [r1, hform, ← hR]

-- N12
private theorem kr_pos_eigenvector_of_sq
    {K : Type*} [TopologicalSpace K]
    (T : C(K, ℝ) →L[ℝ] C(K, ℝ))
    (hT : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (T f) x)
    (r : ℝ) (hr : 0 < r)
    (g : C(K, ℝ)) (hg0 : g ≠ 0) (hg : ∀ x, 0 ≤ g x)
    (hgg : (T ^ 2) g = (r ^ 2) • g) :
    ∃ f : C(K, ℝ), f ≠ 0 ∧ (∀ x, 0 ≤ f x) ∧ T f = r • f := by
  have hT2 : (T ^ 2) g = T (T g) := by rw [pow_two]; rfl
  have hTg : ∀ x, 0 ≤ (T g) x := hT g hg
  refine ⟨T g + r • g, ?_, ?_, ?_⟩
  · intro hcon
    apply hg0
    apply ContinuousMap.ext
    intro x
    have hx : (T g + r • g) x = 0 := by rw [hcon]; rfl
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul] at hx
    have h1 : 0 ≤ (T g) x := hTg x
    have h2 : 0 ≤ r * g x := mul_nonneg hr.le (hg x)
    have e1 : (T g) x = 0 := by
      have := (add_eq_zero_iff_of_nonneg h1 h2).mp hx
      exact this.1
    have e2 : r * g x = 0 := by
      have := (add_eq_zero_iff_of_nonneg h1 h2).mp hx
      exact this.2
    have : g x = 0 := by
      rcases mul_eq_zero.mp e2 with h | h
      · linarith
      · exact h
    exact this
  · intro x
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
    exact add_nonneg (hTg x) (mul_nonneg hr.le (hg x))
  · have hTf : T (T g + r • g) = T (T g) + r • T g := by rw [map_add, map_smul]
    have hTT : T (T g) = (r ^ 2) • g := by rw [← hT2, hgg]
    rw [hTf, hTT]
    have hrr : (r ^ 2) • g = r • (r • g) := by rw [pow_two, smul_smul]
    rw [hrr]
    rw [smul_add]
    exact add_comm _ _

-- N6
private theorem kr_one_le_norm_resolvent_mul
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (S : A) (ρ μ : ℝ)
    (hρ : ρ ∈ spectrum ℝ S) (hμ : μ ∈ resolventSet ℝ S) :
    1 ≤ ‖resolvent S μ‖ * |μ - ρ| := by
  by_contra hcon
  push Not at hcon
  have hlt : ‖(μ - ρ) • resolvent S μ‖ < 1 := by
    calc ‖(μ - ρ) • resolvent S μ‖ ≤ ‖(μ - ρ : ℝ)‖ * ‖resolvent S μ‖ := norm_smul_le _ _
      _ = ‖resolvent S μ‖ * |μ - ρ| := by rw [Real.norm_eq_abs, mul_comm]
      _ < 1 := hcon
  have hmem := (kr_resolvent_sub_eq S μ hμ (μ - ρ) hlt).1
  rw [sub_sub_cancel] at hmem
  have hnot : ¬ IsUnit (algebraMap ℝ A ρ - S) := (spectrum.mem_iff).mp hρ
  exact hnot ((spectrum.mem_resolventSet_iff).mp hmem)

-- N4
private theorem kr_resolvent_pos_of_norm_lt
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (S : C(K, ℝ) →L[ℝ] C(K, ℝ))
    (hS : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (S f) x)
    (μ : ℝ) (hμ : ‖S‖ < μ) :
    μ ∈ resolventSet ℝ S ∧
    ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (resolvent S μ f) x := by
  have hμpos : 0 < μ := lt_of_le_of_lt (norm_nonneg S) hμ
  have hμne : μ ≠ 0 := ne_of_gt hμpos
  have hμnorm : ‖S‖ < ‖μ‖ := by rwa [Real.norm_eq_abs, abs_of_pos hμpos]
  have hmem : μ ∈ resolventSet ℝ S :=
    spectrum.mem_resolventSet_of_norm_lt (a := S) (k := μ) hμnorm
  refine ⟨hmem, ?_⟩
  have hsmul_pos : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ ((μ⁻¹ • S) f) x := by
    intro f hf x
    have h := hS f hf x
    have e : ((μ⁻¹ • S) f) x = μ⁻¹ • ((S f) x) := rfl
    rw [e, smul_eq_mul]
    exact mul_nonneg (le_of_lt (inv_pos.mpr hμpos)) h
  have hsmul_norm : ‖μ⁻¹ • S‖ < 1 := by
    calc ‖μ⁻¹ • S‖ ≤ ‖(μ⁻¹ : ℝ)‖ * ‖S‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ = μ⁻¹ * ‖S‖ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμpos)]
      _ < μ⁻¹ * μ := mul_lt_mul_of_pos_left hμ (inv_pos.mpr hμpos)
      _ = 1 := inv_mul_cancel₀ hμne
  have hB := (kr_isUnit_one_sub_and_inverse_pos (μ⁻¹ • S) hsmul_pos hsmul_norm).2
  have hprod : algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ * (μ⁻¹ • S) = S := by
    calc algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ * (μ⁻¹ • S)
        = μ • (1 * (μ⁻¹ • S)) := by rw [Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc]
      _ = μ • (μ⁻¹ • S) := by rw [one_mul]
      _ = (μ * μ⁻¹) • S := smul_smul μ μ⁻¹ S
      _ = (1 : ℝ) • S := by rw [mul_inv_cancel₀ hμne]
      _ = S := one_smul ℝ S
  have hfac : algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ - S
      = algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ * (1 - μ⁻¹ • S) := by
    rw [mul_sub, mul_one, hprod]
  have hcomm : Commute (algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ) (1 - μ⁻¹ • S) :=
    Algebra.commute_algebraMap_left μ _
  have h1 : algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ * algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ⁻¹ =
      1 := by
    rw [← map_mul, mul_inv_cancel₀ hμne, map_one]
  have h2 : algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ⁻¹ * algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ =
      1 := by
    rw [← map_mul, inv_mul_cancel₀ hμne, map_one]
  have hinv : Ring.inverse (algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ)
      = algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ⁻¹ := by
    have e : Ring.inverse ((⟨algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ, algebraMap ℝ
        (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ⁻¹, h1, h2⟩ :
        (C(K, ℝ) →L[ℝ] C(K, ℝ))ˣ) : C(K, ℝ) →L[ℝ] C(K, ℝ))
        = algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ⁻¹ := by
      rw [Ring.inverse_unit, Units.inv_mk]
    exact e
  have hform : resolvent S μ
      = Ring.inverse (1 - μ⁻¹ • S) * algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ⁻¹ := by
    have r1 : resolvent S μ = Ring.inverse (algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ - S) := rfl
    rw [r1, hfac, Ring.mul_inverse_rev' hcomm, hinv]
  intro f hf x
  rw [hform]
  have hCf : ∀ y, 0 ≤ ((algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ⁻¹) f) y := by
    intro y
    have e : ((algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ⁻¹) f) y = μ⁻¹ • (f y) := rfl
    rw [e, smul_eq_mul]
    exact mul_nonneg (le_of_lt (inv_pos.mpr hμpos)) (hf y)
  have hBC : ((Ring.inverse (1 - μ⁻¹ • S) * algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ⁻¹) f) x
      = (Ring.inverse (1 - μ⁻¹ • S) ((algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ⁻¹) f)) x := rfl
  rw [hBC]
  exact hB _ hCf x

-- N5
private theorem kr_resolvent_pos_sub
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (S : C(K, ℝ) →L[ℝ] C(K, ℝ))
    (ν : ℝ) (hν : ν ∈ resolventSet ℝ S)
    (hRpos : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (resolvent S ν f) x)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t * ‖resolvent S ν‖ < 1) :
    ν - t ∈ resolventSet ℝ S ∧
    ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (resolvent S (ν - t) f) x := by
  have hnorm : ‖t • resolvent S ν‖ < 1 := by
    calc ‖t • resolvent S ν‖ ≤ ‖(t : ℝ)‖ * ‖resolvent S ν‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ = t * ‖resolvent S ν‖ := by rw [Real.norm_eq_abs, abs_of_nonneg ht0]
      _ < 1 := ht
  have hN3 := kr_resolvent_sub_eq S ν hν t hnorm
  have hmem : ν - t ∈ resolventSet ℝ S := hN3.1
  have hform : resolvent S (ν - t)
      = Ring.inverse (1 - t • resolvent S ν) * resolvent S ν := hN3.2
  have htRpos : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ ((t • resolvent S ν) f) x := by
    intro f hf x
    have e : ((t • resolvent S ν) f) x = t • ((resolvent S ν f) x) := rfl
    rw [e, smul_eq_mul]
    exact mul_nonneg ht0 (hRpos f hf x)
  have hB := (kr_isUnit_one_sub_and_inverse_pos (t • resolvent S ν) htRpos hnorm).2
  refine ⟨hmem, ?_⟩
  intro f hf x
  rw [hform]
  have hBC : ((Ring.inverse (1 - t • resolvent S ν) * resolvent S ν) f) x
      = (Ring.inverse (1 - t • resolvent S ν) (resolvent S ν f)) x := rfl
  rw [hBC]
  exact hB _ (hRpos f hf) x

-- N11
private theorem kr_sq_spectralRadius_mem_spectrum_sq
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a : A) (hpos : (0 : ℝ≥0∞) < spectralRadius ℝ a)
    (hfin : spectralRadius ℝ a ≠ ⊤) :
    (spectralRadius ℝ a).toReal ^ 2 ∈ spectrum ℝ (a ^ 2) ∧
    ∀ μ : ℝ, (spectralRadius ℝ a).toReal ^ 2 < μ → μ ∈ resolventSet ℝ (a ^ 2) := by
  have hr_nonneg : 0 ≤ (spectralRadius ℝ a).toReal := ENNReal.toReal_nonneg
  have hr_pos : 0 < (spectralRadius ℝ a).toReal := ENNReal.toReal_pos hpos.ne' hfin
  have hne : (spectrum ℝ a).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hzero : spectralRadius ℝ a = 0 := by
      rw [spectralRadius_eq_of_unital, hcon]
      simp
    rw [hzero] at hpos
    exact (lt_irrefl (0 : ℝ≥0∞) hpos).elim
  have hor := Real.spectralRadius_mem_spectrum_or (a := a) hne
  have hmem : (spectralRadius ℝ a).toReal ^ 2 ∈ spectrum ℝ (a ^ 2) := by
    rcases hor with h | h
    · exact spectrum.pow_mem_pow a 2 h
    · have h2 := spectrum.pow_mem_pow a 2 h
      rwa [neg_sq] at h2
  refine ⟨hmem, ?_⟩
  intro μ hμ
  have hμnn : 0 ≤ (spectralRadius ℝ a).toReal ^ 2 := sq_nonneg _
  have hμpos2 : 0 < μ := lt_of_le_of_lt hμnn hμ
  have hrs : (spectralRadius ℝ a).toReal < Real.sqrt μ :=
    (Real.lt_sqrt (x := (spectralRadius ℝ a).toReal) (y := μ) hr_nonneg).mpr hμ
  have hs_pos : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμpos2
  have hrad : spectralRadius ℝ a = ENNReal.ofReal (spectralRadius ℝ a).toReal :=
    (ENNReal.ofReal_toReal hfin).symm
  have hs_coe : ((‖Real.sqrt μ‖₊ : NNReal) : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt μ) := by
    rw [Real.nnnorm_of_nonneg (Real.sqrt_nonneg μ), ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_mk]
  have hsr : spectralRadius ℝ a < ‖Real.sqrt μ‖₊ := by
    rw [hrad, hs_coe]
    exact (ENNReal.ofReal_lt_ofReal_iff hs_pos).mpr hrs
  have hsr2 : spectralRadius ℝ a < ‖-Real.sqrt μ‖₊ := by
    rw [nnnorm_neg]; exact hsr
  have hs_res : Real.sqrt μ ∈ resolventSet ℝ a :=
    spectrum.mem_resolventSet_of_spectralRadius_lt (a := a) (k := Real.sqrt μ) hsr
  have hns_res : -Real.sqrt μ ∈ resolventSet ℝ a :=
    spectrum.mem_resolventSet_of_spectralRadius_lt (a := a) (k := -Real.sqrt μ) hsr2
  have hsq : (Real.sqrt μ) ^ 2 = μ := Real.sq_sqrt (le_of_lt hμpos2)
  have e2 : -(algebraMap ℝ A (-Real.sqrt μ) - a) = algebraMap ℝ A (Real.sqrt μ) + a := by
    rw [map_neg]; abel
  have e3 : (algebraMap ℝ A (Real.sqrt μ) - a) * (algebraMap ℝ A (Real.sqrt μ) + a)
      = algebraMap ℝ A (Real.sqrt μ) * algebraMap ℝ A (Real.sqrt μ) - a * a := by
    have hc : algebraMap ℝ A (Real.sqrt μ) * a = a * algebraMap ℝ A (Real.sqrt μ) :=
      Algebra.commutes _ _
    rw [sub_mul, mul_add, mul_add, hc]
    abel
  have e4 : algebraMap ℝ A (Real.sqrt μ) * algebraMap ℝ A (Real.sqrt μ)
      = algebraMap ℝ A μ := by
    rw [← map_mul, ← pow_two, hsq]
  have hfac : algebraMap ℝ A μ - a ^ 2
      = (algebraMap ℝ A (Real.sqrt μ) - a) * (-(algebraMap ℝ A (-Real.sqrt μ) - a)) := by
    rw [e2, e3, e4, pow_two]
  have hu1 : IsUnit (algebraMap ℝ A (Real.sqrt μ) - a) :=
    (spectrum.mem_resolventSet_iff).mp hs_res
  have hu2 : IsUnit (-(algebraMap ℝ A (-Real.sqrt μ) - a)) :=
    ((spectrum.mem_resolventSet_iff).mp hns_res).neg
  have hunit : IsUnit (algebraMap ℝ A μ - a ^ 2) := by
    rw [hfac]
    exact hu1.mul hu2
  exact (spectrum.mem_resolventSet_iff).mpr hunit

-- N7
private theorem kr_resolvent_pos_of_gt
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (S : C(K, ℝ) →L[ℝ] C(K, ℝ))
    (hS : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (S f) x)
    (ρ : ℝ)
    (hres : ∀ μ : ℝ, ρ < μ → μ ∈ resolventSet ℝ S) :
    ∀ μ : ℝ, ρ < μ → ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (resolvent S μ f) x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨μ₀, hμ₀ρ, hμ₀⟩ := hcon
  have hμ₀neg : ¬ ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (resolvent S μ₀ f) x := by
    intro hall
    obtain ⟨f, hf, x, hx⟩ := hμ₀
    exact (not_le.mpr hx) (hall f hf x)
  set B : Set ℝ := {μ | ρ < μ ∧ ¬ ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (resolvent S μ f) x} with
      hBdef
  have hBne : B.Nonempty := ⟨μ₀, hμ₀ρ, hμ₀neg⟩
  have hBdd : BddAbove B := by
    refine ⟨‖S‖, ?_⟩
    intro b hb
    by_contra hlt
    push Not at hlt
    exact hb.2 (kr_resolvent_pos_of_norm_lt S hS b hlt).2
  have hBne2 : B.Nonempty := hBne
  obtain ⟨b₀, hb₀⟩ := hBne2
  have hrs : ρ < sSup B := lt_of_lt_of_le hb₀.1 (le_csSup hBdd hb₀)
  have hs_res : sSup B ∈ resolventSet ℝ S := hres _ hrs
  have hgt : ∀ μ : ℝ, sSup B < μ →
      (∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (resolvent S μ f) x) := by
    intro μ hμ
    by_contra hnc
    have hμB : μ ∈ B := ⟨lt_trans hrs hμ, hnc⟩
    have hle : μ ≤ sSup B := le_csSup hBdd hμB
    exact (lt_irrefl _ (lt_of_lt_of_le hμ hle)).elim
  have hs_pos : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (resolvent S (sSup B) f) x := by
    intro f hf x
    have h1 : ContinuousAt
        (fun μ => algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ - S) (sSup B) :=
      (continuous_algebraMap ℝ _).continuousAt.sub continuousAt_const
    obtain ⟨u, hu⟩ := (spectrum.mem_resolventSet_iff).mp hs_res
    let uNR : @Units (C(K, ℝ) →L[ℝ] C(K, ℝ))
        (@Semiring.toMonoid _ (@Ring.toSemiring _ (@NormedRing.toRing _ inferInstance))) := u
    have huNR : ↑uNR = algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) (sSup B) - S := hu
    have h2 : ContinuousAt Ring.inverse
        (algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) (sSup B) - S) := by
      rw [← huNR]
      exact NormedRing.inverse_continuousAt uNR
    have hcomp : ContinuousAt
        (Ring.inverse ∘ (fun μ => algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ - S)) (sSup B) :=
      ContinuousAt.comp (g := Ring.inverse)
        (f := (fun μ => algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) μ - S)) (x := sSup B) h2 h1
    have hcontΦ : ContinuousAt (fun μ => resolvent S μ) (sSup B) := hcomp
    have hev : Continuous (fun W : C(K, ℝ) →L[ℝ] C(K, ℝ) => (W f) x) :=
      (continuous_eval_const x).comp (continuous_eval_const f)
    have htend : Filter.Tendsto (fun μ => (resolvent S μ f) x) (nhds (sSup B))
        (nhds ((resolvent S (sSup B) f) x)) :=
      (hev.tendsto _).comp (ContinuousAt.tendsto hcontΦ)
    have := nhdsWithin_Ioi_neBot (a := sSup B) (b := sSup B) (le_refl _)
    exact ge_of_tendsto (tendsto_nhdsWithin_of_tendsto_nhds htend)
      (Filter.eventually_of_mem self_mem_nhdsWithin
        (fun μ (hμ : μ ∈ Set.Ioi (sSup B)) => hgt μ hμ f hf x))
  have hRs_nn := norm_nonneg (resolvent S (sSup B))
  have hden : (0 : ℝ) < 2 * (‖resolvent S (sSup B)‖ + 1) :=
    mul_pos two_pos (by linarith)
  set δ := 1 / (2 * (‖resolvent S (sSup B)‖ + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact one_div_pos.mpr hden
  have hstep : δ * ‖resolvent S (sSup B)‖ < 1 := by
    rw [hδdef, div_mul_eq_mul_div, one_mul, div_lt_one hden]
    linarith
  have hN5 : ∀ t : ℝ, 0 ≤ t → t ≤ δ →
      (∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (resolvent S (sSup B - t) f) x) := by
    intro t ht0 htδ
    have h1 : t * ‖resolvent S (sSup B)‖ < 1 := by
      calc t * ‖resolvent S (sSup B)‖ ≤ δ * ‖resolvent S (sSup B)‖ :=
            mul_le_mul_of_nonneg_right htδ hRs_nn
        _ < 1 := hstep
    exact (kr_resolvent_pos_sub S (sSup B) hs_res hs_pos t ht0 h1).2
  have hlt : ∀ b ∈ B, b < sSup B - δ := by
    intro b hb
    by_contra hnc
    push Not at hnc
    have hbs : b ≤ sSup B := le_csSup hBdd hb
    have ht0 : 0 ≤ sSup B - b := sub_nonneg.mpr hbs
    have htδ : sSup B - b ≤ δ := by linarith
    have hpos_b := hN5 (sSup B - b) ht0 htδ
    have hbeq : sSup B - (sSup B - b) = b := sub_sub_cancel _ _
    rw [hbeq] at hpos_b
    exact hb.2 hpos_b
  have hle : sSup B ≤ sSup B - δ :=
    csSup_le hBne (fun b hb => le_of_lt (hlt b hb))
  have hss : sSup B < sSup B := by linarith
  exact (lt_irrefl _ hss).elim

-- N8
private theorem kr_exists_approx_pos_eigenvector
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (S : C(K, ℝ) →L[ℝ] C(K, ℝ))
    (hS : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (S f) x)
    (ρ : ℝ) (hρ : ρ ∈ spectrum ℝ S)
    (hres : ∀ μ : ℝ, ρ < μ → μ ∈ resolventSet ℝ S)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ v : C(K, ℝ), (∀ x, 0 ≤ v x) ∧ ‖v‖ = 1 ∧ ‖S v - ρ • v‖ ≤ 2 * δ := by
  have hμρ : ρ < ρ + δ := lt_add_of_pos_right _ hδ
  have hμmem : ρ + δ ∈ resolventSet ℝ S := hres _ hμρ
  have hRpos := kr_resolvent_pos_of_gt S hS ρ hres (ρ + δ) hμρ
  set R := resolvent S (ρ + δ) with hRdef
  set u := R 1 with hudef
  have hu_pos_pt : ∀ x, 0 ≤ u x := by
    have h1 : ∀ x, 0 ≤ (1 : C(K, ℝ)) x := fun x => by simp
    exact hRpos 1 h1
  have h1le : 1 ≤ ‖R‖ * δ := by
    have h := kr_one_le_norm_resolvent_mul S ρ (ρ + δ) hρ hμmem
    have heq : ρ + δ - ρ = δ := by ring
    rwa [heq, abs_of_pos hδ] at h
  have hRle : ‖R‖ ≤ ‖u‖ := kr_pos_opNorm_le_norm_apply_one R hRpos
  have hu_ge : 1 ≤ ‖u‖ * δ :=
    le_trans h1le (mul_le_mul_of_nonneg_right hRle hδ.le)
  have hu_pos : 0 < ‖u‖ := by
    by_contra hc
    push Not at hc
    have hzz : ‖u‖ = 0 := le_antisymm hc (norm_nonneg _)
    rw [hzz, zero_mul] at hu_ge
    linarith
  have hu_inv : ‖u‖⁻¹ ≤ δ := by
    rw [inv_le_iff_one_le_mul₀ hu_pos]
    calc (1 : ℝ) ≤ ‖u‖ * δ := hu_ge
      _ = δ * ‖u‖ := mul_comm _ _
  have hunit : IsUnit (algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) (ρ + δ) - S) :=
    (spectrum.mem_resolventSet_iff).mp hμmem
  have hmul : (algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) (ρ + δ) - S) * R = 1 :=
    Ring.mul_inverse_cancel _ hunit
  have key : (ρ + δ) • u - S u = (1 : C(K, ℝ)) := by
    have happ := congrArg (fun B : C(K, ℝ) →L[ℝ] C(K, ℝ) => B (1 : C(K, ℝ))) hmul
    have e1 : ((algebraMap ℝ (C(K, ℝ) →L[ℝ] C(K, ℝ)) (ρ + δ) - S) * R) (1 : C(K, ℝ))
        = (ρ + δ) • u - S u := rfl
    have e2 : ((1 : C(K, ℝ) →L[ℝ] C(K, ℝ)) (1 : C(K, ℝ))) = (1 : C(K, ℝ)) := rfl
    rwa [e1, e2] at happ
  have hv_norm : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (inv_pos.mpr hu_pos)),
      inv_mul_cancel₀ (ne_of_gt hu_pos)]
  have hdiff : S u - ρ • u = δ • u - 1 := by
    have e : (ρ + δ) • u = ρ • u + δ • u := add_smul _ _ _
    have hSu : S u = (ρ + δ) • u - 1 := by
      calc S u = (ρ + δ) • u - ((ρ + δ) • u - S u) := by abel
        _ = (ρ + δ) • u - 1 := by rw [key]
    rw [hSu, e]
    abel
  refine ⟨‖u‖⁻¹ • u, ?_, hv_norm, ?_⟩
  · intro x
    have e : ((‖u‖⁻¹ • u : C(K, ℝ))) x = ‖u‖⁻¹ * u x := rfl
    rw [e]
    exact mul_nonneg (le_of_lt (inv_pos.mpr hu_pos)) (hu_pos_pt x)
  · have hSv : S (‖u‖⁻¹ • u) = ‖u‖⁻¹ • S u := map_smul _ _ _
    have hρv : ρ • (‖u‖⁻¹ • u) = ‖u‖⁻¹ • (ρ • u) := smul_comm _ _ _
    have hmain : S (‖u‖⁻¹ • u) - ρ • (‖u‖⁻¹ • u)
        = δ • (‖u‖⁻¹ • u) - ‖u‖⁻¹ • (1 : C(K, ℝ)) := by
      rw [hSv, hρv, ← smul_sub, hdiff, smul_sub]
      congr 1
      exact smul_comm _ _ _
    calc ‖S (‖u‖⁻¹ • u) - ρ • (‖u‖⁻¹ • u)‖
        = ‖δ • (‖u‖⁻¹ • u) - ‖u‖⁻¹ • (1 : C(K, ℝ))‖ := by rw [hmain]
      _ ≤ ‖δ • (‖u‖⁻¹ • u)‖ + ‖‖u‖⁻¹ • (1 : C(K, ℝ))‖ := norm_sub_le _ _
      _ = δ * 1 + ‖u‖⁻¹ * 1 := by
          have e1 : ‖δ • (‖u‖⁻¹ • u)‖ = δ * 1 := by
            rw [norm_smul δ _, Real.norm_eq_abs, abs_of_nonneg hδ.le, hv_norm]
          have e2 : ‖‖u‖⁻¹ • (1 : C(K, ℝ))‖ = ‖u‖⁻¹ * 1 := by
            rw [norm_smul (‖u‖⁻¹) _, Real.norm_eq_abs,
              abs_of_nonneg (le_of_lt (inv_pos.mpr hu_pos)), norm_one]
          rw [e1, e2]
      _ = δ + ‖u‖⁻¹ := by ring
      _ ≤ δ + δ := by linarith [hu_inv]
      _ = 2 * δ := by ring

-- N9
private theorem kr_exists_eigenvector_of_approx
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (S : C(K, ℝ) →L[ℝ] C(K, ℝ)) (hS : IsCompactOperator S)
    (ρ : ℝ) (hρ : ρ ≠ 0)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ v : C(K, ℝ), (∀ x, 0 ≤ v x) ∧ ‖v‖ = 1 ∧ ‖S v - ρ • v‖ ≤ ε) :
    ∃ v : C(K, ℝ), v ≠ 0 ∧ (∀ x, 0 ≤ v x) ∧ S v = ρ • v := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
    intro n
    apply one_div_pos.mpr
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  choose vn hvn using fun n : ℕ => happrox _ (hpos n)
  have he0 : Filter.Tendsto (fun n : ℕ => ‖S (vn n) - ρ • vn n‖) Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => (hvn n).2.2)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hmem : ∀ n : ℕ, S (vn n) ∈ closure (S '' Metric.closedBall 0 1) := by
    intro n
    apply subset_closure
    refine ⟨vn n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [(hvn n).2.1]
  have hcompact := hS.isCompact_closure_image_closedBall 1
  obtain ⟨w, _, φ, hφmono, hφlim⟩ := hcompact.tendsto_subseq hmem
  have he_norm_sub : Filter.Tendsto (fun k : ℕ => ‖S (vn (φ k)) - ρ • vn (φ k)‖)
      Filter.atTop (nhds 0) :=
    he0.comp (hφmono.tendsto_atTop)
  have he_sub : Filter.Tendsto (fun k : ℕ => S (vn (φ k)) - ρ • vn (φ k)) Filter.atTop
      (nhds 0) := by
    rwa [tendsto_zero_iff_norm_tendsto_zero]
  have hvn_eq : ∀ k : ℕ, vn (φ k) = ρ⁻¹ • (S (vn (φ k)) - (S (vn (φ k)) - ρ • vn (φ k))) := by
    intro k
    rw [sub_sub_cancel]
    exact (inv_smul_smul₀ hρ _).symm
  have hSsub0 : Filter.Tendsto (fun k : ℕ => S (vn (φ k)) - (S (vn (φ k)) - ρ • vn (φ k)))
      Filter.atTop (nhds (w - 0)) :=
    Filter.Tendsto.sub hφlim he_sub
  have hvn_lim : Filter.Tendsto (fun k : ℕ => vn (φ k)) Filter.atTop (nhds (ρ⁻¹ • w)) := by
    have h := hSsub0.const_smul (ρ⁻¹ : ℝ)
    simp only [sub_zero] at h
    have heq : (fun k : ℕ => ρ⁻¹ • (S (vn (φ k)) - (S (vn (φ k)) - ρ • vn (φ k))))
        = (fun k : ℕ => vn (φ k)) := funext fun k => (hvn_eq k).symm
    rwa [heq] at h
  have hnorm1 : ‖ρ⁻¹ • w‖ = 1 := by
    have h1 : Filter.Tendsto (fun k : ℕ => ‖vn (φ k)‖) Filter.atTop (nhds ‖ρ⁻¹ • w‖) :=
      hvn_lim.norm
    have h2 : Filter.Tendsto (fun k : ℕ => ‖vn (φ k)‖) Filter.atTop (nhds 1) := by
      have : (fun k : ℕ => ‖vn (φ k)‖) = fun _ => (1 : ℝ) := by
        funext k
        rw [(hvn (φ k)).2.1]
      rw [this]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  refine ⟨ρ⁻¹ • w, ?_, ?_, ?_⟩
  · intro hz
    rw [hz, norm_zero] at hnorm1
    exact zero_ne_one hnorm1
  · intro x
    have hx : Filter.Tendsto (fun k : ℕ => (vn (φ k)) x) Filter.atTop (nhds ((ρ⁻¹ • w) x)) :=
      ((continuous_eval_const x).tendsto _).comp hvn_lim
    exact ge_of_tendsto hx (Filter.Eventually.of_forall (fun k => (hvn (φ k)).1 x))
  · have hSw : Filter.Tendsto (fun k : ℕ => S (vn (φ k))) Filter.atTop (nhds (S (ρ⁻¹ • w))) :=
      (S.continuous.tendsto _).comp hvn_lim
    have hSw_eq : S (ρ⁻¹ • w) = w := tendsto_nhds_unique hSw hφlim
    have hρw : Filter.Tendsto (fun k : ℕ => ρ • vn (φ k)) Filter.atTop (nhds (ρ • (ρ⁻¹ • w))) :=
      hvn_lim.const_smul ρ
    have heq2 : (fun k : ℕ => ρ • vn (φ k))
        = (fun k : ℕ => S (vn (φ k)) - (S (vn (φ k)) - ρ • vn (φ k))) := by
      funext k
      rw [sub_sub_cancel]
    have hρw2 : Filter.Tendsto (fun k : ℕ => ρ • vn (φ k)) Filter.atTop (nhds (w - 0)) := by
      rw [heq2]
      exact hSsub0
    have hρw_eq : ρ • (ρ⁻¹ • w) = w - 0 := tendsto_nhds_unique hρw hρw2
    rw [hSw_eq, hρw_eq, sub_zero]

-- N10
private theorem kr_exists_pos_eigenvector_of_mem_spectrum
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (S : C(K, ℝ) →L[ℝ] C(K, ℝ)) (hS_compact : IsCompactOperator S)
    (hS : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (S f) x)
    (ρ : ℝ) (hρpos : 0 < ρ) (hρ : ρ ∈ spectrum ℝ S)
    (hres : ∀ μ : ℝ, ρ < μ → μ ∈ resolventSet ℝ S) :
    ∃ v : C(K, ℝ), v ≠ 0 ∧ (∀ x, 0 ≤ v x) ∧ S v = ρ • v := by
  have happ : ∀ ε : ℝ, 0 < ε → ∃ v : C(K, ℝ),
      (∀ x, 0 ≤ v x) ∧ ‖v‖ = 1 ∧ ‖S v - ρ • v‖ ≤ ε := by
    intro ε hε
    obtain ⟨v, hv0, hv1, hv2⟩ :=
      kr_exists_approx_pos_eigenvector S hS ρ hρ hres (ε / 2) (half_pos hε)
    refine ⟨v, hv0, hv1, ?_⟩
    have heq : 2 * (ε / 2) = ε := by ring
    rwa [heq] at hv2
  exact kr_exists_eigenvector_of_approx S hS_compact ρ (ne_of_gt hρpos) happ

/--
For compact Hausdorff `K`, if `T : C(K, ℝ) →L[ℝ] C(K, ℝ)` is compact, positive (`f ≥ 0 → T f ≥ 0`
pointwise), and has `0 < spectralRadius ℝ T`, then there exists nonzero `f ≥ 0` with `T f =
(spectralRadius ℝ T).toReal • f`. Source: M. G. Krein and M. A. Rutman,
Linear operators leaving invariant a cone in a Banach space,
Uspekhi Mat. Nauk 3 (1948), 1–95, positive compact operator principal eigenvalue; Deimling,
Nonlinear Functional Analysis; Lean states `C(K, ℝ)` compact positive case with spectralRadius
eigenvector and nonnegativity.

Proves `Wanted` entry `krein_rutman`.
-/
theorem krein_rutman
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (T : C(K, ℝ) →L[ℝ] C(K, ℝ))
    (hT_compact : IsCompactOperator T)
    (hT_pos : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (T f) x)
    (hr : (0 : ℝ≥0∞) < spectralRadius ℝ T) :
    ∃ f : C(K, ℝ), f ≠ 0 ∧ (∀ x, 0 ≤ f x) ∧ T f = (spectralRadius ℝ T).toReal • f := by
  rcases isEmpty_or_nonempty K with hempty | hempty
  · have h0 : spectralRadius ℝ T = 0 :=
      spectrum.SpectralRadius.of_subsingleton T
    rw [h0] at hr
    exact (lt_irrefl (0 : ℝ≥0∞) hr).elim
  · have : Nonempty K := hempty
    have hbdd : ∀ k ∈ spectrum ℝ T, ‖k‖₊ ≤ ‖T‖₊ := by
      intro k hk
      by_contra hc
      push Not at hc
      have hlt : ‖T‖ < ‖k‖ := by
        rw [← coe_nnnorm T, ← coe_nnnorm k]
        exact NNReal.coe_lt_coe.mpr hc
      have hmem : k ∈ resolventSet ℝ T :=
        spectrum.mem_resolventSet_of_norm_lt (a := T) (k := k) hlt
      exact ((spectrum.mem_iff).mp hk) ((spectrum.mem_resolventSet_iff).mp hmem)
    have hle : spectralRadius ℝ T ≤ ((‖T‖₊ : NNReal) : ℝ≥0∞) := by
      rw [spectralRadius_eq_of_unital]
      apply iSup_le
      intro k
      apply iSup_le
      intro hk
      exact ENNReal.coe_le_coe.mpr (hbdd k hk)
    have hfin : spectralRadius ℝ T ≠ ⊤ :=
      (lt_of_le_of_lt hle ENNReal.coe_lt_top).ne
    have hr_pos : 0 < (spectralRadius ℝ T).toReal := ENNReal.toReal_pos hr.ne' hfin
    have hN11 := kr_sq_spectralRadius_mem_spectrum_sq T hr hfin
    have hT2_compact : IsCompactOperator ((T ^ 2 : C(K, ℝ) →L[ℝ] C(K, ℝ))) := by
      rw [pow_two]
      exact hT_compact.comp_clm T
    have hT2_pos : ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ ((T ^ 2) f) x := by
      intro f hf x
      have e : (T ^ 2) f = T (T f) := by rw [pow_two]; rfl
      rw [e]
      exact hT_pos _ (hT_pos _ hf) x
    obtain ⟨g, hg0, hgpos, hgg⟩ := kr_exists_pos_eigenvector_of_mem_spectrum
      (T ^ 2) hT2_compact hT2_pos ((spectralRadius ℝ T).toReal ^ 2)
      (pow_pos hr_pos 2) hN11.1 hN11.2
    exact kr_pos_eigenvector_of_sq T hT_pos _ hr_pos g hg0 hgpos hgg

end MathlibExt.Analysis.FunctionalAnalysis.KreinRutmanWanted
end
