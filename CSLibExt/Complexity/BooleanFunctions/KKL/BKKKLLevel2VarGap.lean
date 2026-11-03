/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLMeanInfl

@[expose] public section

/-!
# Level-two mass bounded by variance, and the var-gap core

The undegree and level-≥2 masses are at most the variance (`bkt2p_undegree_le_var`,
`bkt2p_levelGe2_le_var`). `bkt2p_VarGapCore` is a uniform var-gap estimate over
`(1/2, q)`. Status: the core is refuted for every `q > 1/2` (`vgp_varGapCore_refutable`),
and it is kept only as the statement of that refutation; no chain derives the level-≥2,
remaining-goal, master or rho-optimise estimates from it. The file
also records the Poincaré inequality (`mil_poincare`) and the gap vanishing at `p = 1/2`.

## Main definitions

* `bkt2p_VarGapCore`: the uniform var-gap estimate over a window `(1/2, q)`; false for
  every `q > 1/2`.

## Main results

* `bkt2p_levelGe2_le_var`, `bkt2p_levelGe2_le_var_and_mil`: level-≥2 mass versus
  variance and mean influence.
-/

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bkt2p_undegree_le_var {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u' : ℝ} (hu'0 : 0 ≤ u') (hu'1 : u' < 1) (k : ℕ) :
    ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (1 - u') ^ S.card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set μ := OSSS.expect (OSSS.bernoulliWeight p) f with hμ
  have h1u'0 : (0 : ℝ) ≤ 1 - u' := by linarith
  have h1u'1 : (1 : ℝ) - u' ≤ 1 := by linarith
  have hvarF : μ * (1 - μ) = ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2 := by
    rw [← ptn_var_eq_fourierWeight hp0 hp1 f, mil_var_eq φ, ← hμ]; ring
  rw [hvarF]
  calc ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (1 - u') ^ S.card * (ptn_coeff p f S) ^ 2
      ≤ ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (ptn_coeff p f S) ^ 2 := by
        apply Finset.sum_le_sum
        intro S _
        have hpow : (1 - u') ^ S.card ≤ 1 := pow_le_one₀ h1u'0 h1u'1
        nlinarith [hpow, sq_nonneg (ptn_coeff p f S), pow_nonneg h1u'0 S.card]
    _ ≤ ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro S hS
          rw [Finset.mem_filter] at hS
          rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ S⟩
          intro he; rw [he, Finset.card_empty] at hS; omega
        · intro S _ _; positivity

theorem bkt2p_levelGe2_le_var {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u u' : ℝ} (hu1 : u < 1) (hu'0 : 0 ≤ u') (hlt : u' < u) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (4 / (u - u'))
        * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
            * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))) := by
  have hu'1 : u' < 1 := by linarith
  have hdpos : 0 < u - u' := by linarith
  have hlever := bkt2f_degreeWeight_le_undegree (p := p) hu1 hlt φ k
  have hvar := bkt2p_undegree_le_var hp0 hp1 φ hu'0 hu'1 k
  calc 4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (S.card : ℝ) * (1 - u) ^ (S.card - 1)
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ 4 * ((1 / (u - u')) * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (1 - u') ^ S.card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) :=
        mul_le_mul_of_nonneg_left hlever (by norm_num)
    _ ≤ 4 * ((1 / (u - u'))
          * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left hvar
        positivity
    _ = (4 / (u - u'))
          * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))) := by
        ring

/-- The uniform var-gap estimate over a window `(1/2, q)`. False for every
`q > 1/2` (`vgp_varGapCore_refutable`). -/
def bkt2p_VarGapCore (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      ∀ u : ℝ, 0 < u → u < 1 →
        ∃ u' : ℝ, 0 < u' ∧ u' < u ∧ ∃ k : ℕ, 1 ≤ k ∧
          (4 / (u - u'))
            * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
                * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))
            ≤ (4 * (ptn_sigma p) ^ 2)
                * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                    ^ (u / (2 - u))
                  - (1 - u) ^ k)
                * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
                  (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2

theorem bkt2p_levelGe2_le_var_and_mil {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u u' : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hu'0 : 0 ≤ u') (hlt : u' < u) (k : ℕ) :
    (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (4 / (u - u'))
        * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
            * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))))
    ∧ (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ 4 * (k : ℝ)
        * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
            * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))) :=
  ⟨bkt2p_levelGe2_le_var hp0 hp1 φ hu1 hu'0 hlt k,
    mil_levelGe2_le_var hp0 hp1 φ hu0 hu1 k⟩

end StatMech.Probability
