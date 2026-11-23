/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.OSSS
public import CSLibExt.Complexity.BooleanFunctions.Poincare
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The KKL inequality: statement and elementary bounds

This file defines total and maximal influence for product measures on `{0, 1}^E` and states
the Kahn–Kalai–Linial inequality in the logarithmic form
`c · Var(1_A) · log (1 / maxₑ Infₑ(1_A)) ≤ ∑ₑ Infₑ(1_A)`
as the predicate `StatMech.Probability.KKLHypercontractive p c` on the Bernoulli(`p`)
product measure, quantified over all finite nonempty index types and all Boolean functions.
Since `∑ₑ Infₑ ≤ |E| · maxₑ Infₑ`, the predicate gives the classical conclusion that some
variable has influence of order `Var(1_A) · log |E| / |E|`.

The predicate is proved for `p = 1/2` with `c = 2` in
`StatMech.Probability.fsr_pbiased_endpoint`; the constant `c = 0` is trivial
(`kkl_hypercontractive_zero`).

## Main definitions

* `StatMech.Probability.totalInfl`: the total influence `∑ₑ Infₑ(g)`.
* `StatMech.Probability.maxInfl`: the maximal influence `maxₑ Infₑ(g)`.
* `StatMech.Probability.KKLHypercontractive`: the KKL inequality with constant `c` for the
  Bernoulli(`p`) product measure.

## Main results

* `StatMech.Probability.kkl_inequality_total`, `StatMech.Probability.kkl_inequality_max`: the
  KKL inequality in total- and maximal-influence form, given `KKLHypercontractive p c`.
* `StatMech.Probability.kkl_var_le_quarter`: `Var(1_A) ≤ 1/4`.

## References

* J. Kahn, G. Kalai, N. Linial, *The influence of variables on Boolean functions*, FOCS 1988.
* D. Falik, A. Samorodnitsky, *Edge-isoperimetric inequalities and influences*, Combin. Probab.
  Comput. 16 (2007).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace StatMech
namespace Probability

open StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The total influence `∑ₑ Infₑ(g)` of `g` under the product weight `ν`. -/
noncomputable def totalInfl (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  ∑ e, OSSS.infl ν g e

theorem kkl_totalInfl_nonneg {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (g : ConfigSpace E → ℝ) : 0 ≤ totalInfl ν g :=
  Finset.sum_nonneg (fun e _ => OSSS.infl_nonneg hν g e)

/-- The maximal influence `maxₑ Infₑ(g)` of `g` under the product weight `ν`. -/
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
  rw [← he]; exact OSSS.infl_nonneg hν g e

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

/-- The KKL inequality with constant `c` for the Bernoulli(`p`) product measure: for every finite
  nonempty index type `E` and every Boolean function `φ` on `{0, 1}^E`, `c · Var(φ) · log (1 /
  maxₑ Infₑ(φ)) ≤ ∑ₑ Infₑ(φ)`, with `Infₑ(φ)` the probability that `e` is pivotal.

  Despite its name, this is the conclusion of the KKL theorem, not a hypercontractivity estimate.
  It holds trivially for `c = 0` (`kkl_hypercontractive_zero`) and is proved for `p = 1/2`, `c =
  2` in `fsr_pbiased_endpoint`. When `maxₑ Infₑ(φ) = 0`, `log (1 / 0) = 0` in Lean and the
  inequality is trivial. -/
def KKLHypercontractive (p c : ℝ) : Prop :=
  ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool),
    c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)

/-- **Kahn–Kalai–Linial inequality**, total-influence form (J. Kahn, G. Kalai, N. Linial, *The
  influence of variables on Boolean functions*, FOCS 1988): under `KKLHypercontractive p c`, `c ·
  Var(φ) · log (1 / maxₑ Infₑ(φ)) ≤ ∑ₑ Infₑ(φ)`. -/
theorem kkl_inequality_total {p c : ℝ} (H : KKLHypercontractive p c)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  H φ

/-- **Kahn–Kalai–Linial inequality**, maximal-influence form (J. Kahn, G. Kalai, N. Linial, *The
  influence of variables on Boolean functions*, FOCS 1988): under `KKLHypercontractive p c`, `c ·
  Var(φ) · log (1 / δ) ≤ |E| · δ` with `δ = maxₑ Infₑ(φ)`, so `δ` is at least of order `Var(φ) ·
  log |E| / |E|`. -/
theorem kkl_inequality_max {p c : ℝ} (H : KKLHypercontractive p c)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ (Fintype.card E : ℝ)
          * maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  le_trans (kkl_inequality_total H φ)
    (kkl_maxInfl_ge_avg (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))

/-- `KKLHypercontractive p 0` holds trivially, since total influence is nonnegative. -/
theorem kkl_hypercontractive_zero (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    KKLHypercontractive p 0 := by
  intro E _ _ _ φ
  simp only [zero_mul]
  exact kkl_totalInfl_nonneg (bernoulliWeight_isProbWeight hp0 hp1) _

end Probability
end StatMech
