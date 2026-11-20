/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Code.Inequalities.OSSS
import Code.OSSS.Poincare
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators
open Finset

namespace StatMech
namespace Probability

open StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]





theorem kkl_infl_nonneg {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (g : ConfigSpace E → ℝ)
    (e : E) : 0 ≤ OSSS.infl ν g e := by
  unfold OSSS.infl OSSS.expect
  apply Finset.sum_nonneg
  intro ω _
  have hw : 0 ≤ OSSS.weight ν ω :=
    Finset.prod_nonneg (fun e _ => hν.nonneg e (ω e))
  positivity


noncomputable def totalInfl (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  ∑ e, OSSS.infl ν g e

theorem kkl_totalInfl_nonneg {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (g : ConfigSpace E → ℝ) : 0 ≤ totalInfl ν g :=
  Finset.sum_nonneg (fun e _ => kkl_infl_nonneg hν g e)


noncomputable def maxInfl [Nonempty E] (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (OSSS.infl ν g)


theorem kkl_infl_le_maxInfl [Nonempty E] (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ)
    (e : E) : OSSS.infl ν g e ≤ maxInfl ν g :=
  Finset.le_sup' _ (Finset.mem_univ e)


theorem kkl_exists_maxInfl [Nonempty E] (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) :
    ∃ e, OSSS.infl ν g e = maxInfl ν g := by
  unfold maxInfl
  obtain ⟨e, _, he⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := E)) (OSSS.infl ν g)
  exact ⟨e, he.symm⟩


theorem kkl_maxInfl_nonneg [Nonempty E] {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (g : ConfigSpace E → ℝ) : 0 ≤ maxInfl ν g := by
  obtain ⟨e, he⟩ := kkl_exists_maxInfl ν g
  rw [← he]; exact kkl_infl_nonneg hν g e





theorem kkl_maxInfl_ge_avg [Nonempty E] (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) :
    totalInfl ν g ≤ (Fintype.card E : ℝ) * maxInfl ν g := by
  unfold totalInfl
  calc ∑ e, OSSS.infl ν g e
      ≤ ∑ _e : E, maxInfl ν g := by
        apply Finset.sum_le_sum; intro e _; exact kkl_infl_le_maxInfl ν g e
    _ = (Fintype.card E : ℝ) * maxInfl ν g := by
        rw [Finset.sum_const, Finset.card_univ]; ring





theorem kkl_var_nonneg {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (g : ConfigSpace E → ℝ) :
    0 ≤ OSSS.var ν g := by
  have hkey : OSSS.var ν g = OSSS.expect ν (fun ω => (g ω - OSSS.expect ν g) ^ 2) := by
    unfold OSSS.var OSSS.cov OSSS.expect
    have hsum1 : (∑ ω, OSSS.weight ν ω) = 1 := by
      have := OSSS.expect_one hν
      unfold OSSS.expect at this; simpa using this
    rw [Finset.sum_mul]
    have : ∀ ω, OSSS.weight ν ω * (g ω - (∑ ω', OSSS.weight ν ω' * g ω')) ^ 2
        = OSSS.weight ν ω * (g ω * g ω)
          - OSSS.weight ν ω * (2 * (∑ ω', OSSS.weight ν ω' * g ω')) * g ω
          + OSSS.weight ν ω * (∑ ω', OSSS.weight ν ω' * g ω') ^ 2 := by
      intro ω; ring
    simp only [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have e2 : (∑ ω, OSSS.weight ν ω * (2 * (∑ ω', OSSS.weight ν ω' * g ω')) * g ω)
        = 2 * (∑ ω', OSSS.weight ν ω' * g ω') * (∑ ω, OSSS.weight ν ω * g ω) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro ω _; ring
    have e3 : (∑ ω, OSSS.weight ν ω * (∑ ω', OSSS.weight ν ω' * g ω') ^ 2)
        = (∑ ω', OSSS.weight ν ω' * g ω') ^ 2 := by
      rw [← Finset.sum_mul, hsum1, one_mul]
    rw [e2, e3]
    have hgg : ∀ ω, OSSS.weight ν ω * (g ω * g ω) = OSSS.weight ν ω * g ω ^ 2 := by
      intro ω; ring
    simp only [hgg]
    rw [← Finset.sum_mul]
    set S := ∑ ω, OSSS.weight ν ω * g ω with hS
    set Q := ∑ ω, OSSS.weight ν ω * g ω ^ 2 with hQ
    ring
  rw [hkey]
  unfold OSSS.expect
  apply Finset.sum_nonneg
  intro ω _
  have hw : 0 ≤ OSSS.weight ν ω :=
    Finset.prod_nonneg (fun e _ => hν.nonneg e (ω e))
  positivity



theorem kkl_var_indicator_eq (ν : E → Bool → ℝ) (φ : ConfigSpace E → Bool) :
    OSSS.var ν (fun ω => if φ ω then (1 : ℝ) else 0)
      = OSSS.expect ν (fun ω => if φ ω then (1 : ℝ) else 0)
        * (1 - OSSS.expect ν (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  unfold OSSS.var OSSS.cov
  have hsq : (fun ω => f ω * f ω) = f := by
    funext ω; simp only [hf]; by_cases h : φ ω <;> simp [h]
  rw [hsq]; ring



theorem kkl_var_le_quarter (ν : E → Bool → ℝ) (φ : ConfigSpace E → Bool) :
    OSSS.var ν (fun ω => if φ ω then (1 : ℝ) else 0) ≤ 1 / 4 := by
  rw [kkl_var_indicator_eq]
  set m := OSSS.expect ν (fun ω => if φ ω then (1 : ℝ) else 0)
  nlinarith [sq_nonneg (m - 1 / 2)]






theorem kkl_var_le_total_influence {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (φ : ConfigSpace E → Bool) :
    OSSS.var ν (fun ω => if φ ω then (1 : ℝ) else 0)
      ≤ totalInfl ν (fun ω => if φ ω then (1 : ℝ) else 0) :=
  OSSS.Poincare.poincare hν φ


























def KKLHypercontractive (p c : ℝ) : Prop :=
  ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool),
    c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)













theorem kkl_inequality_total {p c : ℝ} (H : KKLHypercontractive p c)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  H φ















theorem kkl_inequality_max {p c : ℝ} (H : KKLHypercontractive p c)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ (Fintype.card E : ℝ)
          * maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  le_trans (kkl_inequality_total H φ)
    (kkl_maxInfl_ge_avg (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))










theorem kkl_hypercontractive_zero (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    KKLHypercontractive p 0 := by
  intro E _ _ _ φ
  simp only [zero_mul]
  exact kkl_totalInfl_nonneg (bernoulliWeight_isProbWeight hp0 hp1) _




theorem kkl_inequality_total_bernoulli {p c : ℝ} (H : KKLHypercontractive p c)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  kkl_inequality_total H φ


theorem kkl_inequality_max_bernoulli {p c : ℝ} (H : KKLHypercontractive p c)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ (Fintype.card E : ℝ)
          * maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  kkl_inequality_max H φ

end Probability
end StatMech
