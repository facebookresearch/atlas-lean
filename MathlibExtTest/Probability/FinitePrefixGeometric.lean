/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FinitePrefixGeometric

import Mathlib.Tactic

open scoped ENNReal

open Filter Topology

@[expose] public section

namespace MathlibExt.Probability.FinitePrefix

/-! Ordinary tokens are `Bool`. Test kernels are axiom-clean: their normalization
proofs are complete. -/

/-- Test kernel: constant EOS probability `2/8 = 1/4`; each ordinary token
has probability `3/8`, so ordinary mass `3/4` per step. -/
private noncomputable def quarterKernel (_ : List Bool) : PMF (Option Bool) :=
  PMF.ofFintype (fun x => if x = Option.none then (2 / 8 : ℝ≥0∞) else 3 / 8)
    (by
      simp only [Fintype.sum_option, Fintype.sum_bool, ite_true, reduceCtorEq, ite_false]
      rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
      norm_num
      exact ENNReal.div_self (by norm_num) (by norm_num))

/-- Test kernel: immediate EOS at every prefix. -/
private noncomputable def immediateKernel (_ : List Bool) : PMF (Option Bool) :=
  PMF.pure Option.none

/-- Test kernel: EOS probability `0` at every prefix. -/
private noncomputable def neverKernel (_ : List Bool) : PMF (Option Bool) :=
  PMF.pure (Option.some true)

/-- Test kernel: EOS probability `(1/2) ^ (length w + 2)` at prefix `w`,
remaining mass on `some true`; positive everywhere but with no uniform positive
lower bound. -/
private noncomputable def decayKernel (w : List Bool) : PMF (Option Bool) :=
  PMF.ofFintype
    (fun x => if x = Option.none then (1 / 2 : ℝ≥0∞) ^ (w.length + 2)
      else if x = Option.some true then 1 - (1 / 2 : ℝ≥0∞) ^ (w.length + 2) else 0)
    (by
      simp only [Fintype.sum_option, Fintype.sum_bool, ite_true, reduceCtorEq, ite_false,
        Option.some.injEq, Bool.false_eq_true, add_zero]
      exact add_tsub_cancel_of_le (pow_le_one₀ (by norm_num) (by norm_num)))

/-- (constant EOS 1/4): the hypothesis holds with `ε = 1/4`, the tail
bound is attained with equality at every `n`, and total terminated mass is one. -/
private theorem quarter_uniformEOS_termination :
    (∀ w : List Bool, (1 / 4 : ℝ≥0∞) ≤ eosProb quarterKernel w)
      ∧ (∀ n : ℕ, survivalMass quarterKernel n = (1 - 1 / 4 : ℝ≥0∞) ^ n)
      ∧ survivalMass quarterKernel 2 = (9 / 16 : ℝ≥0∞)
      ∧ totalTerminatedMass quarterKernel = 1 := by
  have hQnone : ∀ (w : List Bool), eosProb quarterKernel w = 2 / 8 := by
    intro w
    unfold eosProb quarterKernel
    rw [PMF.ofFintype_apply, ite_eq_left rfl]
  have hQsome : ∀ (w : List Bool) (a : Bool),
      quarterKernel w (Option.some a) = 3 / 8 := by
    intro w a
    unfold quarterKernel
    rw [PMF.ofFintype_apply, ite_eq_right (by simp)]
  have h28 : (2 / 8 : ℝ≥0∞) = 1 / 4 := by
    rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  have h1st : ∀ w : List Bool, (1 / 4 : ℝ≥0∞) ≤ eosProb quarterKernel w := by
    intro w
    rw [hQnone w, h28]
  have h14 : (1 - 1 / 4 : ℝ≥0∞) = 3 / 4 := by
    have h14top : (1 / 4 : ℝ≥0∞) ≠ ∞ := by simp
    have hadd : (1 : ℝ≥0∞) = 1 / 4 + 3 / 4 := by
      rw [ENNReal.div_add_div_same]
      norm_num
      exact (ENNReal.div_self (by norm_num) (by norm_num)).symm
    exact ENNReal.sub_eq_of_eq_add_rev h14top hadd
  have h38 : (3 / 8 : ℝ≥0∞) + 3 / 8 = 1 - 1 / 4 := by
    have h33 : (3 / 8 : ℝ≥0∞) + 3 / 8 = 6 / 8 := by
      rw [ENNReal.div_add_div_same]
      norm_num
    rw [h33, h14]
    rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  have hsurv : ∀ (n : ℕ),
      survivalMass quarterKernel n = (1 - 1 / 4 : ℝ≥0∞) ^ n := by
    intro n
    induction n with
    | zero =>
        have h0 : survivalMass quarterKernel 0 = 1 := rfl
        rw [h0, pow_zero]
    | succ n ih =>
        rw [survivalMass_succ]
        have hterm : ∀ (a : Bool),
            quarterKernel [] (Option.some a)
                * survivalMass (fun p => quarterKernel (a :: p)) n
                = 3 / 8 * (1 - 1 / 4 : ℝ≥0∞) ^ n := by
          intro a
          have ih_a : survivalMass (fun p => quarterKernel (a :: p)) n
              = (1 - 1 / 4 : ℝ≥0∞) ^ n := ih
          rw [hQsome [] a, ih_a]
        simp only [hterm]
        rw [Fintype.sum_bool, ← add_mul, h38, pow_succ']
  have hsq : survivalMass quarterKernel 2 = (9 / 16 : ℝ≥0∞) := by
    rw [hsurv 2, h14]
    have h1 : ((3 / 4 : ℝ≥0∞)) ^ 2 ≠ ∞ :=
      ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp) (by norm_num))
    have h2 : (9 / 16 : ℝ≥0∞) ≠ ∞ :=
      ENNReal.div_ne_top (by simp) (by norm_num)
    rw [← ENNReal.toReal_eq_toReal_iff' h1 h2]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_div]
    norm_num
  have htot : totalTerminatedMass quarterKernel = 1 :=
    totalTerminatedMass_eq_one_of_uniformEOS quarterKernel (1 / 4)
      (by norm_num) h1st
  exact ⟨h1st, hsurv, hsq, htot⟩

/-- (immediate EOS): the hypothesis holds with `ε = 1`, all mass is on
the empty terminated string, and survival past step one is zero. -/
private theorem immediate_uniformEOS_termination :
    (∀ w : List Bool, (1 : ℝ≥0∞) ≤ eosProb immediateKernel w)
      ∧ stopMass immediateKernel 0 = 1
      ∧ (∀ n : ℕ, survivalMass immediateKernel (n + 1) = 0)
      ∧ totalTerminatedMass immediateKernel = 1 := by
  have hInone : ∀ (w : List Bool), eosProb immediateKernel w = 1 := by
    intro w
    unfold eosProb immediateKernel
    exact PMF.pure_apply_self _
  have hIsome : ∀ (w : List Bool) (a : Bool),
      immediateKernel w (Option.some a) = 0 := by
    intro w a
    unfold immediateKernel
    exact PMF.pure_apply_of_ne _ _ (by simp)
  have h1st : ∀ w : List Bool, (1 : ℝ≥0∞) ≤ eosProb immediateKernel w := by
    intro w
    rw [hInone w]
  have hstop0 : stopMass immediateKernel 0 = 1 := by
    have hz : stopMass immediateKernel 0 = eosProb immediateKernel [] := rfl
    rw [hz, hInone []]
  have hsurv : ∀ (n : ℕ), survivalMass immediateKernel (n + 1) = 0 := by
    intro n
    rw [survivalMass_succ]
    simp only [hIsome, zero_mul, Finset.sum_const_zero]
  have htot : totalTerminatedMass immediateKernel = 1 :=
    totalTerminatedMass_eq_one_of_uniformEOS immediateKernel 1 zero_lt_one
      h1st
  exact ⟨h1st, hstop0, hsurv, htot⟩

/-- (positive lower bound dropped): with EOS probability `0` the
`ε = 0` hypothesis holds, nothing ever terminates, and total terminated mass
is `0`. -/
private theorem never_no_termination :
    (∀ w : List Bool, (0 : ℝ≥0∞) ≤ eosProb neverKernel w)
      ∧ (∀ n : ℕ, survivalMass neverKernel n = 1)
      ∧ totalTerminatedMass neverKernel = 0 := by
  have hNnone : ∀ (w : List Bool), eosProb neverKernel w = 0 := by
    intro w
    unfold eosProb neverKernel
    exact PMF.pure_apply_of_ne _ _ (by simp)
  have hNtrue : ∀ (w : List Bool), neverKernel w (Option.some true) = 1 := by
    intro w
    unfold neverKernel
    exact PMF.pure_apply_self _
  have hNfalse : ∀ (w : List Bool), neverKernel w (Option.some false) = 0 := by
    intro w
    unfold neverKernel
    exact PMF.pure_apply_of_ne _ _ (by simp)
  have h1st : ∀ w : List Bool, (0 : ℝ≥0∞) ≤ eosProb neverKernel w := by
    intro w
    rw [hNnone w]
  have hsurv : ∀ (n : ℕ), survivalMass neverKernel n = 1 := by
    intro n
    induction n with
    | zero => exact rfl
    | succ n ih =>
        rw [survivalMass_succ]
        have hterm : ∀ (a : Bool),
            neverKernel [] (Option.some a)
                * survivalMass (fun p => neverKernel (a :: p)) n
                = neverKernel [] (Option.some a) * 1 := by
          intro a
          have ih_a : survivalMass (fun p => neverKernel (a :: p)) n = 1 := ih
          rw [ih_a]
        simp only [hterm, mul_one]
        rw [Fintype.sum_bool, hNtrue, hNfalse]
        exact add_zero _
  have hstop : ∀ (n : ℕ), stopMass neverKernel n = 0 := by
    intro n
    induction n with
    | zero =>
        have hz : stopMass neverKernel 0 = eosProb neverKernel [] := rfl
        rw [hz, hNnone []]
    | succ n ih =>
        have hss : stopMass neverKernel (n + 1)
            = Finset.sum Finset.univ
                (fun a => neverKernel [] (Option.some a)
                  * stopMass (fun p => neverKernel (a :: p)) n) := rfl
        rw [hss]
        have hterm0 : ∀ (a : Bool),
            neverKernel [] (Option.some a)
                * stopMass (fun p => neverKernel (a :: p)) n = 0 := by
          intro a
          have ih_a : stopMass (fun p => neverKernel (a :: p)) n = 0 := ih
          rw [ih_a, mul_zero]
        simp only [hterm0, Finset.sum_const_zero]
  have htot : totalTerminatedMass neverKernel = 0 := by
    show (∑' n : ℕ, stopMass neverKernel n) = 0
    simp only [hstop]
    exact tsum_zero
  exact ⟨h1st, hsurv, htot⟩

/-- Test: the conclusion fails once `0 < ε` is dropped. -/
private theorem uniformEOS_termination_needs_pos :
    ¬ ∀ (q : List Bool → PMF (Option Bool)) (ε : ℝ≥0∞),
        (∀ w : List Bool, ε ≤ eosProb q w) → totalTerminatedMass q = 1 := by
  intro H
  have hn := never_no_termination
  obtain ⟨h0, -, hT⟩ := hn
  have h1 := H neverKernel 0 h0
  rw [hT] at h1
  exact zero_ne_one h1

/-- Shifted decay kernel: EOS `(1 / 2) ^ (length w + m)` at prefix `w`,
remaining mass on `some true`. `decayKernel` is the `m = 2` case. -/
private noncomputable def decayShift (m : ℕ) (w : List Bool) : PMF (Option Bool) :=
  PMF.ofFintype
    (fun x => if x = Option.none then (1 / 2 : ℝ≥0∞) ^ (w.length + m)
      else if x = Option.some true then 1 - (1 / 2 : ℝ≥0∞) ^ (w.length + m) else 0)
    (by
      simp only [Fintype.sum_option, Fintype.sum_bool, ite_true, reduceCtorEq, ite_false,
        Option.some.injEq, Bool.false_eq_true, add_zero]
      exact add_tsub_cancel_of_le (pow_le_one₀ (by norm_num) (by norm_num)))

/-- Stepping a shifted decay kernel under a token increments the shift. -/
private theorem decayShift_step (a : Bool) (m : ℕ) :
    (fun p => decayShift m (a :: p)) = decayShift (m + 1) := by
  funext p
  unfold decayShift
  have hlen : (a :: p).length + m = p.length + (m + 1) := by
    rw [List.length_cons]
    omega
  simp only [hlen]

/-- Termination mass of a shifted decay kernel is bounded by the EOS mass at
its depth: only the all-`true` path carries mass. -/
private theorem stopMass_decayShift_le (m n : ℕ) :
    stopMass (decayShift m) n ≤ (1 / 2 : ℝ≥0∞) ^ (n + m) := by
  induction n generalizing m with
  | zero =>
      have hz : stopMass (decayShift m) 0 = eosProb (decayShift m) [] := rfl
      have he : eosProb (decayShift m) []
          = (1 / 2 : ℝ≥0∞) ^ (([] : List Bool).length + m) := by
        unfold eosProb decayShift
        rw [PMF.ofFintype_apply, ite_eq_left rfl]
      rw [hz, he]
      exact le_rfl
  | succ n ih =>
      have hss : stopMass (decayShift m) (n + 1)
          = Finset.sum Finset.univ
              (fun a => decayShift m [] (Option.some a)
                * stopMass (fun p => decayShift m (a :: p)) n) := rfl
      have hF : decayShift m [] (Option.some false) = 0 := by
        unfold decayShift
        rw [PMF.ofFintype_apply,
          ite_eq_right (by simp : Option.some false ≠ Option.none),
          ite_eq_right (by simp : Option.some false ≠ Option.some true)]
      have hT : decayShift m [] (Option.some true)
          = 1 - (1 / 2 : ℝ≥0∞) ^ (([] : List Bool).length + m) := by
        unfold decayShift
        rw [PMF.ofFintype_apply,
          ite_eq_right (by simp : Option.some true ≠ Option.none),
          ite_eq_left rfl]
      rw [hss, Fintype.sum_bool, hT, hF, zero_mul, add_zero,
        decayShift_step true m]
      calc (1 - (1 / 2 : ℝ≥0∞) ^ (([] : List Bool).length + m))
              * stopMass (decayShift (m + 1)) n
          ≤ 1 * stopMass (decayShift (m + 1)) n :=
            mul_le_mul_left tsub_le_self _
        _ = stopMass (decayShift (m + 1)) n := one_mul _
        _ ≤ (1 / 2 : ℝ≥0∞) ^ (n + (m + 1)) := ih (m + 1)
        _ = (1 / 2 : ℝ≥0∞) ^ ((n + 1) + m) := by
            congr 1
            omega

/-- (pointwise-positive but non-uniform EOS): every prefix has positive
EOS probability, yet total terminated mass is at most `1/2`, so uniformity of the
lower bound cannot be weakened to pointwise positivity. -/
private theorem decay_pointwise_pos_not_enough :
    (∀ w : List Bool, 0 < eosProb decayKernel w)
      ∧ totalTerminatedMass decayKernel ≤ (1 / 2 : ℝ≥0∞) := by
  have hDnone : ∀ (w : List Bool),
      eosProb decayKernel w = (1 / 2 : ℝ≥0∞) ^ (w.length + 2) := by
    intro w
    unfold eosProb decayKernel
    rw [PMF.ofFintype_apply, ite_eq_left rfl]
  have hpos : ∀ w : List Bool, 0 < eosProb decayKernel w := by
    intro w
    rw [hDnone w]
    exact ENNReal.pow_pos (by norm_num) _
  have hDK : decayKernel = decayShift 2 := rfl
  have hstopD : ∀ (n : ℕ),
      stopMass decayKernel n ≤ (1 / 2 : ℝ≥0∞) ^ (n + 2) := by
    intro n
    rw [hDK]
    exact stopMass_decayShift_le 2 n
  have h12 : (1 - 1 / 2 : ℝ≥0∞) = 1 / 2 := by
    have htop : (1 / 2 : ℝ≥0∞) ≠ ∞ := by simp
    have hadd : (1 : ℝ≥0∞) = 1 / 2 + 1 / 2 := by
      rw [ENNReal.div_add_div_same]
      norm_num
      exact (ENNReal.div_self (by norm_num) (by norm_num)).symm
    exact ENNReal.sub_eq_of_eq_add_rev htop hadd
  have htsum : totalTerminatedMass decayKernel ≤ (1 / 2 : ℝ≥0∞) := by
    show (∑' n : ℕ, stopMass decayKernel n) ≤ 1 / 2
    calc (∑' n : ℕ, stopMass decayKernel n)
        ≤ ∑' n : ℕ, (1 / 2 : ℝ≥0∞) ^ (n + 2) :=
          ENNReal.tsum_le_tsum hstopD
      _ = (1 / 2 : ℝ≥0∞) * ∑' n : ℕ, (1 / 2 : ℝ≥0∞) ^ (n + 1) := by
          have hpow : ∀ (n : ℕ),
              (1 / 2 : ℝ≥0∞) ^ (n + 2) = (1 / 2) * (1 / 2) ^ (n + 1) := by
            intro n
            have hn2 : n + 2 = (n + 1) + 1 := by omega
            rw [hn2, pow_succ']
          simp only [hpow, ENNReal.tsum_mul_left]
      _ = (1 / 2 : ℝ≥0∞) := by
          rw [ENNReal.tsum_geometric_add_one, h12]
          have hpos2 : (0 : ℝ≥0∞) < 1 / 2 := by norm_num
          have hcancel : (1 / 2 : ℝ≥0∞) * (1 / 2)⁻¹ = 1 :=
            ENNReal.mul_inv_cancel (ne_of_gt hpos2) (by simp)
          rw [hcancel, mul_one]
  exact ⟨hpos, htsum⟩

end MathlibExt.Probability.FinitePrefix
