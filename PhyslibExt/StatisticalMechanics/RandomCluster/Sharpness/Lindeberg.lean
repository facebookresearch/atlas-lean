/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.BooleanFunctions.Coding
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.MonotonicOSSS

/-!
# Means, covariances and the Poincaré inequality for FKG measures

Expectation, covariance, variance and conditional expectation for a probability weight on `{0,
1}^E`, the Lindeberg-type martingale increments, and the Poincaré inequality `Var f ≤ ∑ Cov(f, ω_e)`
for FKG measures.

## i. Overview

The conditional expectation `cExp μ F g` given the coordinates in `F` and the increment `delta` of
revealing one more coordinate give a martingale decomposition of the variance. For a measure
satisfying the FKG lattice condition and a monotone `0 ≤ f ≤ 1`, each increment is bounded by a
covariance, giving `monotonic_poincare`. The random-cluster version is `fk_monotonic_poincare` (`q ≥
1`). Both are unconditional.

## ii. Key results

- `monotonic_poincare`: `Var f ≤ ∑ Cov(f, ω_e)` under the FKG lattice condition (unconditional).
- `fk_monotonic_poincare`: the random-cluster case (unconditional).

## iii. Table of contents

- A. Means, covariances and conditional expectations
- B. Poincaré inequality

## iv. References

* R. O'Donnell, M. Saks, O. Schramm, R. Servedio, *Every decision tree has an influential variable*,
  FOCS 2005.
* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and Potts
  models via decision trees*, Ann. of Math. 189 (2019).
-/

@[expose] public section

open scoped BigOperators
open Finset


namespace StatMech

namespace OSSS

namespace Lindeberg

open OSSS.Monotonic OSSS.Coding

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## A. Means, covariances and conditional expectations -/

/-- The expectation `∑ ω, g ω * μ ω` of `g` under the weight `μ`. -/
noncomputable def mean (μ : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω, g ω * μ ω

/-- The covariance of `f` and `g` under `μ`. -/
noncomputable def cov (μ : ConfigSpace E → ℝ) (f g : ConfigSpace E → ℝ) : ℝ :=
  mean μ (fun ω => f ω * g ω) - mean μ f * mean μ g

/-- The variance of `g` under `μ`. -/
noncomputable def var (μ : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) : ℝ := cov μ g g

/-- The coordinate observable of `e`: `1` if `e` is open, `0` otherwise. -/
noncomputable def coord (e : E) : ConfigSpace E → ℝ := fun ω => if ω e then (1 : ℝ) else 0

lemma mean_add (μ : ConfigSpace E → ℝ) (g h : ConfigSpace E → ℝ) :
    mean μ (fun ω => g ω + h ω) = mean μ g + mean μ h := by
  unfold mean; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun ω _ => by ring)

lemma mean_sub (μ : ConfigSpace E → ℝ) (g h : ConfigSpace E → ℝ) :
    mean μ (fun ω => g ω - h ω) = mean μ g - mean μ h := by
  unfold mean; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun ω _ => by ring)

lemma mean_const_mul (μ : ConfigSpace E → ℝ) (c : ℝ) (g : ConfigSpace E → ℝ) :
    mean μ (fun ω => c * g ω) = c * mean μ g := by
  unfold mean; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)

lemma mean_const (μ : ConfigSpace E → ℝ) (hμ : ∑ ω, μ ω = 1) (c : ℝ) :
    mean μ (fun _ => c) = c := by
  unfold mean
  simp only []
  rw [← Finset.mul_sum, hμ, mul_one]

lemma var_eq_double_sum (μ : ConfigSpace E → ℝ) (hμ : ∑ ω, μ ω = 1) (f : ConfigSpace E → ℝ) :
    var μ f = (1 / 2) * ∑ x, ∑ y, μ x * μ y * (f x - f y) ^ 2 := by
  unfold var cov mean
  have hsplit : ∑ x, ∑ y, μ x * μ y * (f x - f y) ^ 2
      = ∑ x, ∑ y, ((f x * f x) * μ x * μ y)
        + ∑ x, ∑ y, ((f y * f y) * μ x * μ y)
        - 2 * ∑ x, ∑ y, ((f x * μ x) * (f y * μ y)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro x _
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro y _; ring
  rw [hsplit]
  have h1 : ∑ x, ∑ y, ((f x * f x) * μ x * μ y) = ∑ x, (f x * f x) * μ x := by
    apply Finset.sum_congr rfl; intro x _; rw [← Finset.mul_sum, hμ, mul_one]
  have h2 : ∑ x, ∑ y, ((f y * f y) * μ x * μ y) = ∑ y, (f y * f y) * μ y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    rw [show (fun x => (f y * f y) * μ x * μ y) = (fun x => ((f y * f y) * μ y) * μ x) from by
          funext x; ring, ← Finset.mul_sum, hμ, mul_one]
  have h3 : ∑ x, ∑ y, ((f x * μ x) * (f y * μ y)) = (∑ x, f x * μ x) * (∑ y, f y * μ y) := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro x _; rw [Finset.mul_sum]
  rw [h1, h2, h3]; ring

/-- The conditional expectation of `g` given the coordinates in `F`, evaluated at `ω`. -/
noncomputable def cExp (μ : ConfigSpace E → ℝ) (F : Finset E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) : ℝ :=
  ∑ ω', g ω' * condMass μ F ω ω'

/-- The function `h` depends only on the coordinates in `F`. -/
def Fmeas (F : Finset E) (h : ConfigSpace E → ℝ) : Prop :=
  ∀ η η', (∀ f ∈ F, η f = η' f) → h η = h η'

lemma cExp_Fmeas (μ : ConfigSpace E → ℝ) (F : Finset E) (g : ConfigSpace E → ℝ) :
    Fmeas F (cExp μ F g) := by
  intro η η' h
  unfold cExp condMass
  rw [condNorm_congr μ F η η' h]
  apply Finset.sum_congr rfl; intro ω' _
  congr 2
  exact if_congr (agree_congr_of_eq_on F η η' ω' h) rfl rfl

lemma cExp_pullout {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    (g h : ConfigSpace E → ℝ) (hh : Fmeas F h) :
    (∑ ω, (cExp μ F g ω * h ω) * μ ω) = ∑ ω, (g ω * h ω) * μ ω := by
  unfold cExp condMass
  have step : ∀ ω, ((∑ ω', g ω' * ((if Agree F ω ω' then μ ω' else 0) / condNorm μ F ω)) * h ω) * μ
      ω
      = ∑ ω', (if Agree F ω ω' then (g ω' * h ω') * μ ω' else 0) * (μ ω / condNorm μ F ω) := by
    intro ω
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro ω' _
    by_cases hag : Agree F ω ω'
    · rw [ite_eq_left hag, ite_eq_left hag]
      have : h ω = h ω' := hh ω ω' (fun fe hfe => (hag fe hfe).symm)
      rw [this]; ring
    · rw [ite_eq_right hag, ite_eq_right hag]; ring
  simp_rw [step]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro ω' _
  have hZeq : ∀ ω, Agree F ω ω' → condNorm μ F ω = condNorm μ F ω' := by
    intro ω hag; apply condNorm_congr; intro fe hfe; exact (hag fe hfe).symm
  have hrw : (∑ ω, (if Agree F ω ω' then (g ω' * h ω') * μ ω' else 0) * (μ ω / condNorm μ F ω))
      = ((g ω' * h ω') * μ ω' / condNorm μ F ω') * ∑ ω, (if Agree F ω ω' then μ ω else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro ω _
    by_cases hag : Agree F ω ω'
    · rw [ite_eq_left hag, ite_eq_left hag, hZeq ω hag]; ring
    · rw [ite_eq_right hag, ite_eq_right hag]; ring
  rw [hrw]
  have hcn : (∑ ω, (if Agree F ω ω' then μ ω else 0)) = condNorm μ F ω' := by
    unfold condNorm; apply Finset.sum_congr rfl; intro ω _
    exact if_congr ⟨fun hh fe hfe => (hh fe hfe).symm, fun hh fe hfe => (hh fe hfe).symm⟩ rfl rfl
  rw [hcn]
  have hZ := condNorm_pos hpos F ω'
  field_simp

lemma mean_cExp {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    (g : ConfigSpace E → ℝ) :
    mean μ (cExp μ F g) = mean μ g := by
  unfold mean
  have h1 := cExp_pullout hpos F g (fun _ => 1) (fun _ _ _ => rfl)
  simpa using h1

lemma cExp_mono {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hFKG : FKGLatticeCondition μ)
    (F : Finset E) {g : ConfigSpace E → ℝ} (hg : Monotone g) (hg0 : 0 ≤ g) :
    Monotone (cExp μ F g) := by
  intro ω ω' hle
  have hμ : 0 ≤ μ := fun x => (hpos x).le
  have hle' : ∀ f ∈ F, ω f ≤ ω' f := fun f _ => hle f
  have hZω := condNorm_pos hpos F ω
  have hZω' := condNorm_pos hpos F ω'
  exact holley _ _ _ hg0
    (condMass_nonneg hμ F ω hZω) (condMass_nonneg hμ F ω' hZω') hg
    (by rw [condMass_sum F ω hZω.ne', condMass_sum F ω' hZω'.ne'])
    (cross_condMass hμ hFKG F ω ω' hle' hZω hZω')

lemma mean_mul_ge {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) {A B : ConfigSpace E → ℝ}
    (hA : Monotone A) (hB : Monotone B) :
    mean μ A * mean μ B ≤ mean μ (fun ω => A ω * B ω) := by
  have h := fkg_inequality (π := μ) (fun ω => (hpos ω).le) hμ1 hFKG hA hB
  have e1 : (∑ ω, μ ω * A ω) = mean μ A := by
    unfold mean; exact Finset.sum_congr rfl (fun ω _ => by ring)
  have e2 : (∑ ω, μ ω * B ω) = mean μ B := by
    unfold mean; exact Finset.sum_congr rfl (fun ω _ => by ring)
  have e3 : (∑ ω, μ ω * (A ω * B ω)) = mean μ (fun ω => A ω * B ω) := by
    unfold mean; exact Finset.sum_congr rfl (fun ω _ => by ring)
  rw [e1, e2, e3] at h
  exact h

/-- The unnormalized conditional sum of `g` over configurations agreeing with `ω` on `F`. -/
noncomputable def cSum (μ : ConfigSpace E → ℝ) (F : Finset E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) : ℝ :=
  ∑ ω', (if Agree F ω ω' then g ω' * μ ω' else 0)

lemma cExp_eq_cSum_div (μ : ConfigSpace E → ℝ) (F : Finset E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) :
    cExp μ F g ω = cSum μ F g ω / condNorm μ F ω := by
  unfold cExp cSum condMass
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun ω' _ => ?_)
  by_cases h : Agree F ω ω'
  · simp [h]; ring
  · simp [h]

lemma condNorm_eq_cSum_one (μ : ConfigSpace E → ℝ) (F : Finset E) (ω : ConfigSpace E) :
    condNorm μ F ω = cSum μ F (fun _ => 1) ω := by
  unfold condNorm cSum
  refine Finset.sum_congr rfl (fun ω' _ => ?_)
  by_cases h : Agree F ω ω'
  · simp [h]
  · simp [h]

lemma cSum_split (μ : ConfigSpace E → ℝ) (F : Finset E) (e : E) (he : e ∉ F)
    (g : ConfigSpace E → ℝ) (ω : ConfigSpace E) :
    cSum μ F g ω = cSum μ (insert e F) g (setOpen e ω) + cSum μ (insert e F) g (setClosed e ω) := by
  unfold cSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ω' _ => ?_)
  have hne : ∀ x ∈ F, x ≠ e := fun x hxF => by rintro rfl; exact he hxF
  by_cases hF : Agree F ω ω'
  · by_cases hb : ω' e = true
    · have hopen : Agree (insert e F) (setOpen e ω) ω' := by
        intro x hx; rcases Finset.mem_insert.mp hx with rfl | hxF
        · rw [setOpen_self]; exact hb
        · rw [setOpen_of_ne (hne x hxF)]; exact hF x hxF
      have hclosed : ¬ Agree (insert e F) (setClosed e ω) ω' := by
        intro hag; have := hag e (Finset.mem_insert_self e F); rw [setClosed_self] at this
        rw [hb] at this; exact absurd this (by simp)
      rw [ite_eq_left hF, ite_eq_left hopen, ite_eq_right hclosed, add_zero]
    · have hb' : ω' e = false := by
        cases hh : ω' e with
        | false => rfl
        | true => exact absurd hh hb
      have hclosed : Agree (insert e F) (setClosed e ω) ω' := by
        intro x hx; rcases Finset.mem_insert.mp hx with rfl | hxF
        · rw [setClosed_self]; exact hb'
        · rw [setClosed_of_ne (hne x hxF)]; exact hF x hxF
      have hopen : ¬ Agree (insert e F) (setOpen e ω) ω' := by
        intro hag; have := hag e (Finset.mem_insert_self e F); rw [setOpen_self] at this
        rw [hb'] at this; exact absurd this (by simp)
      rw [ite_eq_left hF, ite_eq_right hopen, ite_eq_left hclosed, zero_add]
  · have h1 : ¬ Agree (insert e F) (setOpen e ω) ω' := by
      intro hag; apply hF; intro x hxF
      have := hag x (Finset.mem_insert_of_mem hxF)
      rwa [setOpen_of_ne (hne x hxF)] at this
    have h2 : ¬ Agree (insert e F) (setClosed e ω) ω' := by
      intro hag; apply hF; intro x hxF
      have := hag x (Finset.mem_insert_of_mem hxF)
      rwa [setClosed_of_ne (hne x hxF)] at this
    rw [ite_eq_right hF, ite_eq_right h1, ite_eq_right h2, add_zero]

lemma cSum_coord_open (μ : ConfigSpace E → ℝ) (F : Finset E) (e : E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) :
    cSum μ (insert e F) (fun ω'' => g ω'' * coord e ω'') (setOpen e ω)
      = cSum μ (insert e F) g (setOpen e ω) := by
  unfold cSum
  refine Finset.sum_congr rfl (fun ω' _ => ?_)
  simp only []
  by_cases hag : Agree (insert e F) (setOpen e ω) ω'
  · have he : ω' e = true := by
      have := hag e (Finset.mem_insert_self e F); rwa [setOpen_self] at this
    rw [ite_eq_left hag, ite_eq_left hag]; unfold coord; simp [he]
  · rw [ite_eq_right hag, ite_eq_right hag]

lemma cSum_coord_closed (μ : ConfigSpace E → ℝ) (F : Finset E) (e : E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) :
    cSum μ (insert e F) (fun ω'' => g ω'' * coord e ω'') (setClosed e ω) = 0 := by
  unfold cSum
  refine Finset.sum_eq_zero (fun ω' _ => ?_)
  simp only []
  by_cases hag : Agree (insert e F) (setClosed e ω) ω'
  · have he : ω' e = false := by
      have := hag e (Finset.mem_insert_self e F); rwa [setClosed_self] at this
    rw [ite_eq_left hag]; unfold coord; simp [he]
  · rw [ite_eq_right hag]

lemma cExp_decomp {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (e : E)
    (he : e ∉ F) (f : ConfigSpace E → ℝ) (ω : ConfigSpace E) :
    cExp μ F f ω = cExp μ F (coord e) ω * cExp μ (insert e F) f (setOpen e ω)
      + (1 - cExp μ F (coord e) ω) * cExp μ (insert e F) f (setClosed e ω) := by
  have hZopos : 0 < condNorm μ (insert e F) (setOpen e ω) := condNorm_pos hpos _ _
  have hZcpos : 0 < condNorm μ (insert e F) (setClosed e ω) := condNorm_pos hpos _ _
  have hZFpos : 0 < condNorm μ F ω := condNorm_pos hpos _ _
  set Zo := condNorm μ (insert e F) (setOpen e ω) with hZo
  set Zc := condNorm μ (insert e F) (setClosed e ω) with hZc
  set ZF := condNorm μ F ω with hZF
  have hZFsum : ZF = Zo + Zc := by
    rw [hZF, condNorm_eq_cSum_one, cSum_split μ F e he, ← condNorm_eq_cSum_one, ←
        condNorm_eq_cSum_one]
  have hN : cExp μ F (coord e) ω = Zo / ZF := by
    rw [cExp_eq_cSum_div, cSum_split μ F e he _ ω]
    have ho : cSum μ (insert e F) (coord e) (setOpen e ω) = Zo := by
      have := cSum_coord_open μ F e (fun _ => 1) ω
      simp only [one_mul] at this
      rw [hZo, condNorm_eq_cSum_one, ← this]
    have hc : cSum μ (insert e F) (coord e) (setClosed e ω) = 0 := by
      have := cSum_coord_closed μ F e (fun _ => 1) ω
      simp only [one_mul] at this; exact this
    rw [ho, hc, add_zero]
  have ha : cSum μ (insert e F) f (setOpen e ω) = cExp μ (insert e F) f (setOpen e ω) * Zo := by
    rw [cExp_eq_cSum_div, div_mul_cancel₀]; exact hZopos.ne'
  have hb : cSum μ (insert e F) f (setClosed e ω) = cExp μ (insert e F) f (setClosed e ω) * Zc := by
    rw [cExp_eq_cSum_div, div_mul_cancel₀]; exact hZcpos.ne'
  rw [cExp_eq_cSum_div, cSum_split μ F e he f ω, ha, hb, hN, ← hZF, hZFsum]
  field_simp
  ring

omit [DecidableEq E] [Fintype E] in
lemma coord_mono (e : E) : Monotone (coord (E := E) e) := by
  intro x y hxy; unfold coord
  by_cases h : x e = true
  · have hy : y e = true := by have := hxy e; rw [h] at this; exact le_antisymm le_top this
    simp [h, hy]
  · simp only [h]
    by_cases h2 : y e = true <;> simp [h2]

omit [DecidableEq E] [Fintype E] in
lemma coord_nonneg (e : E) : (0 : ConfigSpace E → ℝ) ≤ coord e := by
  intro ω; unfold coord; split <;> norm_num

lemma cExp_nonneg {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    {g : ConfigSpace E → ℝ} (hg0 : 0 ≤ g) (ω : ConfigSpace E) : 0 ≤ cExp μ F g ω := by
  unfold cExp
  apply Finset.sum_nonneg; intro ω' _
  exact mul_nonneg (hg0 ω')
    (condMass_nonneg (fun x => (hpos x).le) F ω (condNorm_pos hpos F ω) ω')

lemma cExp_le_one {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    {g : ConfigSpace E → ℝ} (hg1 : ∀ ω, g ω ≤ 1) (ω : ConfigSpace E) : cExp μ F g ω ≤ 1 := by
  unfold cExp
  have hsum : ∑ ω', condMass μ F ω ω' = 1 := condMass_sum F ω (condNorm_pos hpos F ω).ne'
  calc ∑ ω', g ω' * condMass μ F ω ω'
      ≤ ∑ ω', 1 * condMass μ F ω ω' := by
        apply Finset.sum_le_sum; intro ω' _
        exact mul_le_mul_of_nonneg_right (hg1 ω')
          (condMass_nonneg (fun x => (hpos x).le) F ω (condNorm_pos hpos F ω) ω')
    _ = 1 := by simp [hsum]

/-- The increment of the conditional expectation of `f` when coordinate `e` is added to `F`. -/
noncomputable def delta (μ : ConfigSpace E → ℝ) (F : Finset E) (e : E) (f : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) : ℝ :=
  cExp μ (insert e F) f (setOpen e ω) - cExp μ (insert e F) f (setClosed e ω)

lemma delta_nonneg {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hFKG : FKGLatticeCondition μ)
    (F : Finset E) (e : E) {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    (ω : ConfigSpace E) : 0 ≤ delta μ F e f ω := by
  unfold delta
  have := (cExp_mono hpos hFKG (insert e F) hf hf0) (setClosed_le_setOpen e ω)
  linarith

lemma delta_le_one {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (e : E)
    {f : ConfigSpace E → ℝ} (hf1 : ∀ ω, f ω ≤ 1) (hf0 : 0 ≤ f) (ω : ConfigSpace E) :
    delta μ F e f ω ≤ 1 := by
  unfold delta
  have h1 := cExp_le_one hpos (insert e F) hf1 (setOpen e ω)
  have h2 := cExp_nonneg hpos (insert e F) hf0 (setClosed e ω)
  linarith

lemma delta_Fmeas (μ : ConfigSpace E → ℝ) (F : Finset E) (e : E) (he : e ∉ F)
    (f : ConfigSpace E → ℝ) : Fmeas F (delta μ F e f) := by
  intro η η' h
  unfold delta
  have hne : ∀ x ∈ F, x ≠ e := fun x hxF => by rintro rfl; exact he hxF
  congr 1
  · apply cExp_Fmeas μ (insert e F) f
    intro x hx; rcases Finset.mem_insert.mp hx with rfl | hxF
    · rw [setOpen_self, setOpen_self]
    · rw [setOpen_of_ne (hne x hxF), setOpen_of_ne (hne x hxF)]; exact h x hxF
  · apply cExp_Fmeas μ (insert e F) f
    intro x hx; rcases Finset.mem_insert.mp hx with rfl | hxF
    · rw [setClosed_self, setClosed_self]
    · rw [setClosed_of_ne (hne x hxF), setClosed_of_ne (hne x hxF)]; exact h x hxF

lemma cExp_branch (μ : ConfigSpace E → ℝ) (F : Finset E) (e : E)
    (f : ConfigSpace E → ℝ) (ω : ConfigSpace E) :
    cExp μ (insert e F) f ω
      = if ω e then cExp μ (insert e F) f (setOpen e ω) else cExp μ (insert e F) f (setClosed e ω)
          := by
  by_cases hb : ω e = true
  · rw [ite_eq_left hb]
    apply cExp_Fmeas μ (insert e F) f ω (setOpen e ω)
    intro x _; by_cases hxe : x = e
    · subst hxe; rw [setOpen_self]; exact hb
    · rw [setOpen_of_ne hxe]
  · have hb' : ω e = false := by
      cases hh : ω e with
      | false => rfl
      | true => exact absurd hh hb
    rw [ite_eq_right hb]
    apply cExp_Fmeas μ (insert e F) f ω (setClosed e ω)
    intro x _; by_cases hxe : x = e
    · subst hxe; rw [setClosed_self]; exact hb'
    · rw [setClosed_of_ne hxe]

lemma step_factor {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (e : E)
    (he : e ∉ F) (f : ConfigSpace E → ℝ) (ω : ConfigSpace E) :
    cExp μ (insert e F) f ω - cExp μ F f ω
      = delta μ F e f ω * (coord e ω - cExp μ F (coord e) ω) := by
  rw [cExp_decomp hpos F e he f ω, cExp_branch μ F e f ω]
  have hcoord : coord e ω = if ω e then (1 : ℝ) else 0 := rfl
  unfold delta
  by_cases hbit : ω e = true
  · rw [ite_eq_left hbit, hcoord, ite_eq_left hbit]; ring
  · have hbit' : ω e = false := by
      cases hh : ω e with
      | false => rfl
      | true => exact absurd hh hbit
    rw [ite_eq_right hbit, hcoord, ite_eq_right hbit]; ring

lemma step_le_cov {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) (F : Finset E) (e : E) (he : e ∉ F)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    mean μ (fun ω => (cExp μ (insert e F) f ω - cExp μ F f ω) ^ 2) ≤ cov μ f (coord e) := by
  set D := fun ω => cExp μ (insert e F) f ω - cExp μ F f ω with hD
  set δ := delta μ F e f with hδ
  set N := cExp μ F (coord e) with hNdef
  have hDfac : ∀ ω, D ω = δ ω * (coord e ω - N ω) := by
    intro ω; rw [hD]; simp only []; rw [step_factor hpos F e he f ω]
  have hstepA : mean μ (fun ω => (D ω) ^ 2) ≤ mean μ (fun ω => D ω * coord e ω) := by
    have hzero : (∑ ω, (δ ω * N ω * (coord e ω - N ω)) * μ ω) = 0 := by
      have hFm : Fmeas F (fun ω => δ ω * N ω) := by
        intro η η' h
        have h1 := delta_Fmeas μ F e he f η η' h
        have h2 := cExp_Fmeas μ F (coord e) η η' h
        change δ η * N η = δ η' * N η'
        rw [hδ, hNdef, h1, h2]
      have hpull := cExp_pullout hpos F (coord e) (fun ω => δ ω * N ω) hFm
      have hpull' : (∑ ω, ((N ω) * (δ ω * N ω)) * μ ω) = ∑ ω, (coord e ω * (δ ω * N ω)) * μ ω :=
        hpull
      have hexp : (∑ ω, (δ ω * N ω * (coord e ω - N ω)) * μ ω)
          = (∑ ω, (coord e ω * (δ ω * N ω)) * μ ω) - (∑ ω, ((N ω) * (δ ω * N ω)) * μ ω) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun ω _ => by ring)
      rw [hexp, hpull']; ring
    have hdiff : mean μ (fun ω => D ω * coord e ω) - mean μ (fun ω => (D ω) ^ 2)
        = ∑ ω, (δ ω * (1 - δ ω) * (coord e ω - N ω) ^ 2) * μ ω := by
      unfold mean
      rw [← Finset.sum_sub_distrib]
      have expand : ∀ ω, (D ω * coord e ω) * μ ω - ((D ω) ^ 2) * μ ω
          = (δ ω * (1 - δ ω) * (coord e ω - N ω) ^ 2) * μ ω
            + (δ ω * N ω * (coord e ω - N ω)) * μ ω := by
        intro ω; rw [hDfac ω]; ring
      simp_rw [expand]
      rw [Finset.sum_add_distrib, hzero, add_zero]
    have hge : 0 ≤ ∑ ω, (δ ω * (1 - δ ω) * (coord e ω - N ω) ^ 2) * μ ω := by
      apply Finset.sum_nonneg; intro ω _
      refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) (hpos ω).le
      · exact delta_nonneg hpos hFKG F e hf hf0 ω
      · have := delta_le_one hpos F e hf1 hf0 ω; rw [hδ]; linarith
      · positivity
    linarith [hdiff, hge]
  have hstepB : mean μ (fun ω => D ω * coord e ω) ≤ cov μ f (coord e) := by
    have hcoordFmeas : Fmeas (insert e F) (coord e) := by
      intro η η' h; unfold coord; rw [h e (Finset.mem_insert_self e F)]
    have h1 : mean μ (fun ω => cExp μ (insert e F) f ω * coord e ω)
        = mean μ (fun ω => f ω * coord e ω) := by
      unfold mean; exact cExp_pullout hpos (insert e F) f (coord e) hcoordFmeas
    have hcExpFf_Fmeas : Fmeas F (cExp μ F f) := cExp_Fmeas μ F f
    have h2 : mean μ (fun ω => cExp μ F f ω * coord e ω)
        = mean μ (fun ω => cExp μ F f ω * N ω) := by
      have hp := cExp_pullout hpos F (coord e) (cExp μ F f) hcExpFf_Fmeas
      unfold mean
      rw [show (fun ω => cExp μ F f ω * coord e ω) = (fun ω => coord e ω * cExp μ F f ω) from by
            funext ω; ring]
      rw [show (∑ ω, (fun ω => coord e ω * cExp μ F f ω) ω * μ ω)
            = ∑ ω, (coord e ω * cExp μ F f ω) * μ ω from rfl, ← hp]
      exact Finset.sum_congr rfl (fun ω _ => by rw [hNdef]; ring)
    have hDexp : mean μ (fun ω => D ω * coord e ω)
        = mean μ (fun ω => f ω * coord e ω) - mean μ (fun ω => cExp μ F f ω * N ω) := by
      have hsub : mean μ (fun ω => D ω * coord e ω)
          = mean μ (fun ω => cExp μ (insert e F) f ω * coord e ω)
            - mean μ (fun ω => cExp μ F f ω * coord e ω) := by
        unfold mean
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun ω _ => by rw [hD]; simp only []; ring)
      rw [hsub, h1, h2]
    rw [hDexp]
    have hmono1 : Monotone (cExp μ F f) := cExp_mono hpos hFKG F hf hf0
    have hmono2 : Monotone N := by
      rw [hNdef]; exact cExp_mono hpos hFKG F (coord_mono e) (coord_nonneg e)
    have hfkg := mean_mul_ge hpos hμ1 hFKG hmono1 hmono2
    rw [mean_cExp hpos F f, hNdef, mean_cExp hpos F (coord e), ← hNdef] at hfkg
    unfold cov
    linarith [hfkg]
  exact hstepA.trans hstepB

omit [DecidableEq E] [Fintype E] in
lemma Fmeas_mono {F F' : Finset E} (hsub : F ⊆ F') {h : ConfigSpace E → ℝ} (hh : Fmeas F h) :
    Fmeas F' h := fun η η' heq => hh η η' (fun x hx => heq x (hsub hx))

lemma cExp_univ {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (f : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) : cExp μ Finset.univ f ω = f ω := by
  unfold cExp condMass
  rw [Finset.sum_eq_single ω]
  · rw [condNorm_univ, ite_eq_left (agree_self _ _)]; field_simp [(hpos ω).ne']
  · intro ω' _ hne
    rw [ite_eq_right, zero_div, mul_zero]
    intro hag; exact hne (funext fun x => (hag x (Finset.mem_univ x)))
  · intro h; exact absurd (Finset.mem_univ ω) h

lemma cExp_empty {μ : ConfigSpace E → ℝ} (hμ1 : ∑ ω, μ ω = 1) (f : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) : cExp μ ∅ f ω = mean μ f := by
  unfold cExp condMass mean
  rw [condNorm_empty, hμ1]
  apply Finset.sum_congr rfl; intro ω' _
  rw [ite_eq_left]
  · field_simp
  · intro x hx; exact absurd hx (Finset.notMem_empty x)

lemma projection {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) {F F' : Finset E} (hsub : F ⊆ F')
    (f : ConfigSpace E → ℝ) :
    mean μ (fun ω => cExp μ F' f ω * cExp μ F f ω)
      = mean μ (fun ω => cExp μ F f ω * cExp μ F f ω) := by
  have hFmeas : Fmeas F' (cExp μ F f) := Fmeas_mono hsub (cExp_Fmeas μ F f)
  have h1 : mean μ (fun ω => cExp μ F' f ω * cExp μ F f ω) = mean μ (fun ω => f ω * cExp μ F f ω)
      := by
    unfold mean; exact cExp_pullout hpos F' f (cExp μ F f) hFmeas
  have h2 : mean μ (fun ω => cExp μ F f ω * cExp μ F f ω) = mean μ (fun ω => f ω * cExp μ F f ω) :=
      by
    unfold mean; exact cExp_pullout hpos F f (cExp μ F f) (cExp_Fmeas μ F f)
  rw [h1, h2]

lemma pythagoras {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) {F F' : Finset E} (hsub : F ⊆ F')
    (f : ConfigSpace E → ℝ) :
    mean μ (fun ω => (cExp μ F' f ω - cExp μ F f ω) ^ 2)
      = mean μ (fun ω => cExp μ F' f ω * cExp μ F' f ω)
        - mean μ (fun ω => cExp μ F f ω * cExp μ F f ω) := by
  have hexpand : mean μ (fun ω => (cExp μ F' f ω - cExp μ F f ω) ^ 2)
      = mean μ (fun ω => cExp μ F' f ω * cExp μ F' f ω)
        - 2 * mean μ (fun ω => cExp μ F' f ω * cExp μ F f ω)
        + mean μ (fun ω => cExp μ F f ω * cExp μ F f ω) := by
    unfold mean
    rw [show (∑ ω, ((cExp μ F' f ω - cExp μ F f ω) ^ 2) * μ ω)
          = ∑ ω, ((cExp μ F' f ω * cExp μ F' f ω) * μ ω
              - 2 * ((cExp μ F' f ω * cExp μ F f ω) * μ ω)
              + (cExp μ F f ω * cExp μ F f ω) * μ ω) from by
          apply Finset.sum_congr rfl; intro ω _; ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexpand, projection hpos hsub f]; ring

lemma var_telescope {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    var μ f = ∑ t ∈ Finset.range n,
      mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) (t + 1)) f ω
                          - cExp μ (prefixSet (σ : Fin n → E) t) f ω) ^ 2) := by
  set g : ℕ → ℝ := fun t =>
    mean μ (fun ω => cExp μ (prefixSet (σ : Fin n → E) t) f ω
                      * cExp μ (prefixSet (σ : Fin n → E) t) f ω) with hg
  have hterm : ∀ t ∈ Finset.range n,
      mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) (t + 1)) f ω
                          - cExp μ (prefixSet (σ : Fin n → E) t) f ω) ^ 2) = g (t + 1) - g t := by
    intro t ht
    rw [Finset.mem_range] at ht
    have hsub : prefixSet (σ : Fin n → E) t ⊆ prefixSet (σ : Fin n → E) (t + 1) := by
      rw [prefixSet_succ_lt (σ : Fin n → E) t ht]; exact Finset.subset_insert _ _
    rw [pythagoras hpos hsub f]
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub g n]
  have hgn : g n = mean μ (fun ω => f ω * f ω) := by
    change mean μ (fun ω => cExp μ (prefixSet (σ : Fin n → E) n) f ω
                          * cExp μ (prefixSet (σ : Fin n → E) n) f ω) = _
    rw [prefixSet_card σ]
    unfold mean; apply Finset.sum_congr rfl; intro ω _
    simp only [cExp_univ hpos f ω]
  have hg0 : g 0 = mean μ f * mean μ f := by
    change mean μ (fun ω => cExp μ (prefixSet (σ : Fin n → E) 0) f ω
                          * cExp μ (prefixSet (σ : Fin n → E) 0) f ω) = _
    rw [prefixSet_zero]
    unfold mean
    have hc : (fun ω => cExp μ ∅ f ω * cExp μ ∅ f ω) = (fun _ => mean μ f * mean μ f) := by
      funext ω; rw [cExp_empty hμ1 f ω]
    rw [hc]
    simp only []
    rw [← Finset.mul_sum, hμ1, mul_one]
    rfl
  rw [hgn, hg0]
  unfold var cov; ring

/-! ## B. Poincaré inequality -/

/-- `Var f ≤ ∑ Cov(f, ω_e)` under the FKG lattice condition (unconditional). -/
theorem monotonic_poincare {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    var μ f ≤ ∑ e, cov μ f (coord e) := by
  classical
  set n := Fintype.card E with hn
  set σ : Fin n ≃ E := (Fintype.equivFin E).symm with hσ
  rw [var_telescope hpos hμ1 σ f]
  have hreindex : ∑ t ∈ Finset.range n,
      mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) (t + 1)) f ω
                          - cExp μ (prefixSet (σ : Fin n → E) t) f ω) ^ 2)
      = ∑ i : Fin n,
          mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) ((i : ℕ) + 1)) f ω
                            - cExp μ (prefixSet (σ : Fin n → E) (i : ℕ)) f ω) ^ 2) := by
    rw [Finset.sum_range fun t =>
      mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) (t + 1)) f ω
                          - cExp μ (prefixSet (σ : Fin n → E) t) f ω) ^ 2)]
  rw [hreindex]
  have hbound : ∀ i : Fin n,
      mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) ((i : ℕ) + 1)) f ω
                          - cExp μ (prefixSet (σ : Fin n → E) (i : ℕ)) f ω) ^ 2)
        ≤ cov μ f (coord ((σ : Fin n → E) i)) := by
    intro i
    rw [prefixSet_succ_lt (σ : Fin n → E) (i : ℕ) i.2]
    have hi : (⟨(i : ℕ), i.2⟩ : Fin n) = i := rfl
    rw [hi]
    have hnotmem : (σ : Fin n → E) i ∉ prefixSet (σ : Fin n → E) (i : ℕ) := by
      rw [mem_prefixSet_iff]
      rintro ⟨s, hs, hseq⟩
      have := σ.injective hseq
      rw [this] at hs; exact (lt_irrefl (i : ℕ)) hs
    exact step_le_cov hpos hμ1 hFKG _ _ hnotmem hf hf0 hf1
  calc ∑ i : Fin n,
        mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) ((i : ℕ) + 1)) f ω
                            - cExp μ (prefixSet (σ : Fin n → E) (i : ℕ)) f ω) ^ 2)
      ≤ ∑ i : Fin n, cov μ f (coord ((σ : Fin n → E) i)) := Finset.sum_le_sum (fun i _ => hbound i)
    _ = ∑ e, cov μ f (coord e) := Equiv.sum_comp σ (fun e => cov μ f (coord e))

open OSSS.MonotonicMeasure in
lemma cov_eq_genCov (μ : ConfigSpace E → ℝ) (f g : ConfigSpace E → ℝ) :
    cov μ f g = genCov μ f g := rfl

open OSSS.MonotonicMeasure in
lemma var_eq_genVar (μ : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) :
    var μ g = genVar μ g := rfl

open OSSS.MonotonicMeasure in
omit [DecidableEq E] [Fintype E] in
lemma coord_eq_genCoord (e : E) : (coord e : ConfigSpace E → ℝ) =
    StatMech.OSSS.CovLowerBound.coordI e := rfl

open OSSS.MonotonicMeasure in
lemma monotonicOSSSBound_poincare {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    MonotonicOSSSBound μ Finset.univ f 1 1 1 := by
  unfold MonotonicOSSSBound
  rw [← var_eq_genVar]
  have hmain := monotonic_poincare hpos hμ1 hFKG hf hf0 hf1
  rw [Nat.cast_one, one_mul, one_mul, one_mul]
  refine hmain.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro e _
  rw [← cov_eq_genCov, ← coord_eq_genCoord]
  unfold cov mean
  rw [show (fun ω => f ω * coord e ω) = (fun ω => coord e ω * f ω) from by funext ω; ring]
  ring

open MonotonicFK OSSS.MonotonicMeasure in
lemma fk_monotonic_poincare {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) {f : ConfigSpace (Sym2 V) → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    var (fkMass G p q) f ≤ ∑ e, cov (fkMass G p q) f (coord e) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact monotonic_poincare
    (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_sum_eq_one G hp hp1 hq0)
    (FK.fkProb_FKGLatticeCondition G hp hp1 hq) hf hf0 hf1

open MonotonicFK OSSS.MonotonicMeasure in
lemma fk_monotonicOSSSBound_poincare {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) {f : ConfigSpace (Sym2 V) → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    MonotonicOSSSBound (fkMass G p q) Finset.univ f 1 1 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact monotonicOSSSBound_poincare
    (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_sum_eq_one G hp hp1 hq0)
    (FK.fkProb_FKGLatticeCondition G hp hp1 hq) hf hf0 hf1

end Lindeberg

end OSSS

end StatMech
