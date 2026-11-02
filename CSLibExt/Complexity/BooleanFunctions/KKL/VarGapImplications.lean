/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLLevel2VarGap

@[expose] public section

/-!
# The variance-gap core and its consequences

Vanishing of total influence and variance when the max influence vanishes;
the Poincaré inequality as the `δ = 0` instance; the gap vanishing at `p = 1/2`.
Status: the var-power core `vgc_VarPowerCore` is refuted for every `q > 1/2`
(`vgp_varPowerCore_refutable`), and it is kept only as the statement of that refutation;
no chain derives the var-gap core, level-≥2, remaining-goal, master or rho-optimise
estimates from it.

## Main definitions

* `vgc_VarPowerCore`: the uniform var-power estimate over a window `(1/2, q)`; false
  for every `q > 1/2`.

## Main results

* `vgc_totalInfl_zero_of_maxInfl_zero`, `vgc_var_zero_of_maxInfl_zero`: vanishing
  influence/variance when max influence vanishes.
-/


open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem vgc_totalInfl_zero_of_maxInfl_zero [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool)
    (hδ0 : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0) :
    totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0 := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  unfold totalInfl
  apply Finset.sum_eq_zero
  intro e _
  have hle : OSSS.infl (OSSS.bernoulliWeight p) f e
      ≤ maxInfl (OSSS.bernoulliWeight p) f := kkl_infl_le_maxInfl _ f e
  have hge : 0 ≤ OSSS.infl (OSSS.bernoulliWeight p) f e :=
    OSSS.infl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f e
  rw [hδ0] at hle
  linarith

theorem vgc_var_zero_of_maxInfl_zero [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool)
    (hδ0 : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) = 0 := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set μ := OSSS.expect (OSSS.bernoulliWeight p) f with hμ
  have hpoin := mil_poincare hp0 hp1 φ
  rw [← hμ] at hpoin
  have hT0 := vgc_totalInfl_zero_of_maxInfl_zero hp0 hp1 φ hδ0
  rw [hT0, mul_zero] at hpoin
  have hvarF := ptn_var_eq_fourierWeight hp0 hp1 f
  have hvar_eq : OSSS.var (OSSS.bernoulliWeight p) f = μ * (1 - μ) := by
    rw [mil_var_eq φ, ← hμ]; ring
  have hvar_nn : 0 ≤ μ * (1 - μ) := by
    rw [← hvar_eq, hvarF]
    exact Finset.sum_nonneg (fun S _ => sq_nonneg _)
  linarith

/-- The uniform var-power estimate over a window `(1/2, q)`. False for every
`q > 1/2` (`vgp_varPowerCore_refutable`). -/
def vgc_VarPowerCore (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      ∀ u : ℝ, 0 < u → u < 1 →
        0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) →
          OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
            ≤ (u / (4 + 2 * u))
              * ((ptn_sigma p) ^ 2
                * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                    ^ (u / (2 - u))
                  * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))

theorem vgc_varPowerCore_c0 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {u : ℝ} (hu0 : 0 < u) (_hu1 : u < 1) :
    OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)
      * (1 - OSSS.expect (OSSS.bernoulliWeight p)
          (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
      ≤ (u / (4 + 2 * u))
        * ((ptn_sigma p) ^ 2
          * ((maxInfl (OSSS.bernoulliWeight p)
              (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
              ^ (u / (2 - u))
            * totalInfl (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))) := by
  set f0 : ConfigSpace E → Bool := fun _ => false with hf0
  have hf0zero : (fun ω => if f0 ω then (1 : ℝ) else 0) = (fun _ : ConfigSpace E => (0 : ℝ)) := by
    funext ω; rw [hf0]; simp
  have hμ0 : OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if f0 ω then (1 : ℝ) else 0) = 0 := by
    rw [hf0zero]; unfold OSSS.expect; simp
  rw [hμ0]
  simp only [sub_zero, zero_mul]
  have hδnn : 0 ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if f0 ω then (1 : ℝ) else 0) :=
    kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _
  have hTnn : 0 ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if f0 ω then (1 : ℝ) else 0) :=
    kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _
  have h4u : (0 : ℝ) ≤ u / (4 + 2 * u) := by positivity
  positivity

theorem vgc_poincare_is_delta0_instance {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ (ptn_sigma p) ^ 2
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  mil_poincare hp0 hp1 φ

theorem vgc_gap_vanishes_at_p_half {u : ℝ} (d : ℕ) :
    (1 - u) ^ (d - 1) - (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = 0 :=
  bkt2c_gap_vanishes_at_p_half d

end StatMech.Probability
