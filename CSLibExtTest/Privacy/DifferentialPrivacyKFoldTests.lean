/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DifferentialPrivacyKFold
public import Cslib.Foundations.Relation.RelatesInSteps
public import Cslib.Probability.PMF

/-!
# k-fold and group privacy tests

Boundary checks for adaptive composition (`k = 0, 1, 2`), constant mechanisms,
two-step chains, and error-shape identities for the sum-form group privacy.
Behavioral checks evaluate `kfoldCompose` on tiny Dirac and uniform
mechanisms, pinning transcript carriers and masses.
-/

@[expose] public section

namespace CSLibExtTest.Privacy.DifferentialPrivacyKFoldTests

open CSLibExt.Privacy.DifferentialPrivacy
open scoped ENNReal

universe u

/-- Sum over zero stages vanishes. -/
theorem test_sum_zero (ε : ℕ → ℝ) :
    Finset.sum (Finset.range 0) ε = 0 := by
  simp

/-- Sum over one stage is the head budget. -/
theorem test_sum_one (ε : ℕ → ℝ) :
    Finset.sum (Finset.range 1) ε = ε 0 := by
  simp

/-- Sum over two stages splits as expected. -/
theorem test_sum_two (ε : ℕ → ℝ) :
    Finset.sum (Finset.range 2) ε = ε 0 + ε 1 := by
  simp [Finset.sum_range_succ]

/-- Zero stages: the transcript is the unit Dirac. -/
theorem test_kfold_zero_dirac {D : Type*} (d : D) :
    kfoldCompose (A := fun _ => Bool) (fun _ _ _ => PMF.pure true) 0 d
      = PMF.pure (PUnit.unit : PUnit) :=
  rfl

/-- Zero stages carry full mass on the unit transcript. -/
theorem test_kfold_zero_mass {D : Type*} (d : D) :
    kfoldCompose (A := fun _ => Bool) (fun _ _ _ => PMF.pure true) 0 d
      (PUnit.unit : PUnit) = 1 := by
  rw [test_kfold_zero_dirac]
  show (PMF.pure (PUnit.unit : PUnit)) (PUnit.unit : PUnit) = 1
  simp

/-- One Dirac stage: the transcript is the paired Dirac. -/
theorem test_kfold_one_dirac {D : Type*} (d : D) :
    kfoldCompose (A := fun _ => Bool) (fun _ _ _ => PMF.pure true) 1 d
      = PMF.pure ((PUnit.unit, true) : PUnit × Bool) := by
  show kfoldCompose _ (0 + 1) _ = _
  rw [kfoldCompose_succ, kfoldCompose_zero]
  show ((PMF.pure (PUnit.unit : PUnit)).bind fun t =>
      (PMF.pure true).bind fun a => PMF.pure (t, a)) = _
  simp

/-- One Dirac stage puts full mass on the paired point. -/
theorem test_kfold_one_mass_true {D : Type*} (d : D) :
    kfoldCompose (A := fun _ => Bool) (fun _ _ _ => PMF.pure true) 1 d
      ((PUnit.unit, true) : PUnit × Bool) = 1 := by
  rw [test_kfold_one_dirac]
  show (PMF.pure ((PUnit.unit, true) : PUnit × Bool))
    ((PUnit.unit, true) : PUnit × Bool) = 1
  simp

/-- One Dirac stage puts no mass off the paired point. -/
theorem test_kfold_one_mass_false {D : Type*} (d : D) :
    kfoldCompose (A := fun _ => Bool) (fun _ _ _ => PMF.pure true) 1 d
      ((PUnit.unit, false) : PUnit × Bool) = 0 := by
  rw [test_kfold_one_dirac]
  show (PMF.pure ((PUnit.unit, true) : PUnit × Bool))
    ((PUnit.unit, false) : PUnit × Bool) = 0
  simp

/-- Two Dirac stages: the transcript is the nested paired Dirac. -/
theorem test_kfold_two_dirac {D : Type*} (d : D) :
    kfoldCompose (A := fun _ => Bool) (fun _ _ _ => PMF.pure true) 2 d
      = PMF.pure (((PUnit.unit, true), true) : (PUnit × Bool) × Bool) := by
  show kfoldCompose _ (1 + 1) _ = _
  rw [kfoldCompose_succ]
  show (((kfoldCompose (A := fun _ => Bool) (fun _ _ _ => PMF.pure true) 1 d).bind
    fun t => (PMF.pure true).bind fun a => PMF.pure (t, a))) = _
  rw [test_kfold_one_dirac]
  show (((PMF.pure ((PUnit.unit, true) : PUnit × Bool)).bind
    fun t => (PMF.pure true).bind fun a => PMF.pure (t, a))) = _
  simp

/-- Two Dirac stages put full mass on the nested paired point. -/
theorem test_kfold_two_mass {D : Type*} (d : D) :
    kfoldCompose (A := fun _ => Bool) (fun _ _ _ => PMF.pure true) 2 d
      (((PUnit.unit, true), true) : (PUnit × Bool) × Bool) = 1 := by
  rw [test_kfold_two_dirac]
  show (PMF.pure (((PUnit.unit, true), true) : (PUnit × Bool) × Bool))
    (((PUnit.unit, true), true) : (PUnit × Bool) × Bool) = 1
  simp

/-- One uniform stage: even split on `true`. -/
theorem test_kfold_one_coin_true {D : Type*} (d : D) :
    kfoldCompose (A := fun _ => Bool)
        (fun _ _ _ => Cslib.Probability.PMF.uniformOfFintype Bool) 1 d
        ((PUnit.unit, true) : PUnit × Bool) = (2 : ℝ≥0∞)⁻¹ := by
  show kfoldCompose _ (0 + 1) _ _ = _
  rw [kfoldCompose_succ, kfoldCompose_zero]
  show ((((PMF.pure (PUnit.unit : PUnit)).bind fun t =>
    (Cslib.Probability.PMF.uniformOfFintype Bool).bind fun a =>
      PMF.pure (t, a))) ((PUnit.unit, true) : PUnit × Bool)) = _
  rw [Cslib.Probability.PMF.bind_pair_apply]
  simp

/-- One uniform stage: even split on `false`. -/
theorem test_kfold_one_coin_false {D : Type*} (d : D) :
    kfoldCompose (A := fun _ => Bool)
        (fun _ _ _ => Cslib.Probability.PMF.uniformOfFintype Bool) 1 d
        ((PUnit.unit, false) : PUnit × Bool) = (2 : ℝ≥0∞)⁻¹ := by
  show kfoldCompose _ (0 + 1) _ _ = _
  rw [kfoldCompose_succ, kfoldCompose_zero]
  show ((((PMF.pure (PUnit.unit : PUnit)).bind fun t =>
    (Cslib.Probability.PMF.uniformOfFintype Bool).bind fun a =>
      PMF.pure (t, a))) ((PUnit.unit, false) : PUnit × Bool)) = _
  rw [Cslib.Probability.PMF.bind_pair_apply]
  simp

/-- k-fold with `k = 2` matches the staged pair theorem budgets. -/
theorem test_kfold_two_vs_pair {D : Type*} {A : ℕ → Type u} {adj : D → D → Prop}
    {K : (n : ℕ) → Transcript A n → D → PMF (A n)} {ε δ : ℕ → ℝ}
    (hε0 : 0 ≤ ε 0) (hε1 : 0 ≤ ε 1) (hδ0 : 0 ≤ δ 0) (hδ1 : 0 ≤ δ 1)
    (hK0 : ∀ t, IsApproxDP (fun d => K 0 t d) adj (ε 0) (δ 0))
    (hK1 : ∀ t, IsApproxDP (fun d => K 1 t d) adj (ε 1) (δ 1)) :
    IsApproxDP (kfoldCompose K 2) adj (ε 0 + ε 1) (δ 0 + δ 1) := by
  have hε : ∀ i, i < 2 → 0 ≤ ε i := by
    intro i hi
    interval_cases i
    · exact hε0
    · exact hε1
  have hδ : ∀ i, i < 2 → 0 ≤ δ i := by
    intro i hi
    interval_cases i
    · exact hδ0
    · exact hδ1
  have hK : ∀ i, i < 2 → ∀ t, IsApproxDP (fun d => K i t d) adj (ε i) (δ i) := by
    intro i hi t
    interval_cases i
    · exact hK0 t
    · exact hK1 t
  have h := isApproxDP_kfold 2 hε hδ hK
  simpa [Finset.sum_range_succ] using h

/-- Constant kernels compose to `(0, 0)`-DP. -/
theorem test_kfold_const_zero {D : Type*} {A : ℕ → Type u} {adj : D → D → Prop}
    {p : (i : ℕ) → PMF (A i)} (k : ℕ) :
    IsApproxDP (kfoldCompose (fun i _ _ => p i) k) adj 0 0 := by
  have hM : ∀ i, i < k → IsApproxDP (fun _ : D => p i) adj 0 0 := by
    intro i _
    rw [isApproxDP_zero_iff]
    exact isDP_const _ _
  have h := isApproxDP_kfold_const (M := fun i _ => p i)
    (ε := fun _ => 0) (δ := fun _ => 0) k
    (fun _ _ => le_refl 0) (fun _ _ => le_refl 0) hM
  simpa using h

/-- Any two `Fin 1` databases are adjacent. -/
theorem test_replaceOne_fin1 {X : Type*} (d d' : Fin 1 → X) :
    ReplaceOne d d' := by
  intro i _ j _
  have hi : i = 0 := Fin.eq_zero i
  have hj : j = 0 := Fin.eq_zero j
  rw [hi, hj]

/-- A two-step chain over `Fin 1`. -/
theorem test_chain_two {X : Type*} (d d' d'' : Fin 1 → X) :
    ReplaceOneChain 2 d d'' :=
  Relation.RelatesInSteps.tail _ _ _ _
    (Relation.RelatesInSteps.tail _ _ _ _ (Relation.RelatesInSteps.refl d)
      (test_replaceOne_fin1 d d'))
    (test_replaceOne_fin1 d' d'')

/-- Group error at `k = 0` is zero. -/
theorem test_err_zero (δ ε : ℝ) :
    δ * Finset.sum (Finset.range 0)
      (fun j => Real.exp ((j : ℝ) * ε)) = 0 := by
  simp

/-- Group error at `k = 1` is exactly `δ`. -/
theorem test_err_one (δ ε : ℝ) :
    δ * Finset.sum (Finset.range 1)
      (fun j => Real.exp ((j : ℝ) * ε)) = δ := by
  simp

/-- Group error at `k = 2` is `δ * (1 + exp ε)`. -/
theorem test_err_two (δ ε : ℝ) :
    δ * Finset.sum (Finset.range 2)
      (fun j => Real.exp ((j : ℝ) * ε)) = δ * (1 + Real.exp ε) := by
  have hsum : Finset.sum (Finset.range 2)
      (fun j => Real.exp ((j : ℝ) * ε)) = 1 + Real.exp ε := by
    simp [Finset.sum_range_succ]
  rw [hsum]

/-- Two-step bound with `ε = 0`, `δ = 0`: factor one, no error term. -/
theorem test_two_step_pure {X Output : Type*}
    {M : (Fin 1 → X) → PMF Output}
    (hM : IsApproxDP M ReplaceOne 0 0)
    {d d'' : Fin 1 → X} (d' : Fin 1 → X) (s : Set Output) :
    (M d).toOuterMeasure s ≤
      1 * (M d'').toOuterMeasure s + 0 := by
  have hchain := test_chain_two d d' d''
  have h := isApproxDP_groupPrivacy (ε := 0) (δ := 0) hM hchain s
  have hexp : Real.exp (((2 : ℕ) : ℝ) * 0) = 1 := by
    simp
  have herr : (0 : ℝ) * Finset.sum (Finset.range 2)
      (fun j => Real.exp ((j : ℝ) * 0)) = 0 := by
    simp
  simpa [hexp, herr] using h

/-- Two-step bound with `ε = 0` and symbolic `δ`: error is exactly `2 * δ`. -/
theorem test_two_step_nonzero_delta {X Output : Type*}
    {M : (Fin 1 → X) → PMF Output} {δ : ℝ}
    (hM : IsApproxDP M ReplaceOne 0 δ)
    (_hδ : 0 ≤ δ)
    {d d'' : Fin 1 → X} (d' : Fin 1 → X) (s : Set Output) :
    (M d).toOuterMeasure s ≤
      1 * (M d'').toOuterMeasure s + ENNReal.ofReal (2 * δ) := by
  have hchain := test_chain_two d d' d''
  have h := isApproxDP_groupPrivacy (ε := 0) (δ := δ) hM hchain s
  have hexp : Real.exp (((2 : ℕ) : ℝ) * 0) = 1 := by
    simp
  have herr : δ * Finset.sum (Finset.range 2)
      (fun j => Real.exp ((j : ℝ) * 0)) = 2 * δ := by
    rw [test_err_two, Real.exp_zero]
    ring
  rw [hexp, herr, ENNReal.ofReal_one] at h
  exact h

#print axioms isApproxDP_kfold
#print axioms isDP_kfold
#print axioms isDP_groupPrivacy
#print axioms isApproxDP_groupPrivacy

end CSLibExtTest.Privacy.DifferentialPrivacyKFoldTests
