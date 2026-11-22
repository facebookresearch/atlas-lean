/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.GameTheory.FairDivision.Indivisible
public import MathlibExt.GameTheory.FairDivision.MaxNashWelfare
public import MathlibExt.GameTheory.FairDivision.MaxNashWelfareEF1

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace MathlibExtTest.GameTheory.FairDivision.MaxNashWelfareEF1

@[expose] public section

open MathlibExt.GameTheory.FairDivision.Indivisible

/-- Test valuations: agent `0` values goods `(4, 3, 0)`, agent `1` values
`(0, 3, 4)`. -/
def tv : Fin 2 → Fin 3 → ℝ := fun i g =>
  if i = 0 then (if g = 0 then 4 else if g = 1 then 3 else 0)
  else (if g = 0 then 0 else if g = 1 then 3 else 4)

/-- Test allocation: goods `0`, `1` to agent `0`, good `2` to agent `1`. -/
def tA : Fin 3 → Fin 2 := fun g => if g = 2 then 1 else 0

/-- Test values for `tv` and `tA`: bundle values `7` and `4`, welfare `28`. -/
theorem t1_values :
    value tv tA 0 = 7 ∧ value tv tA 1 = 4 ∧ positiveWelfare tv tA = 28 := by
  have hb0 : bundle tA 0 = {0, 1} := by decide
  have hb1 : bundle tA 1 = {2} := by decide
  have hv0 : value tv tA 0 = 7 := by
    unfold value bundleValue
    rw [hb0, Finset.sum_insert (by decide), Finset.sum_singleton]
    show (4 : ℝ) + 3 = 7
    norm_num
  have hv1 : value tv tA 1 = 4 := by
    unfold value bundleValue
    rw [hb1, Finset.sum_singleton]
    rfl
  have hw : positiveWelfare tv tA = 28 := by
    have hall : ∀ i : Fin 2, 0 < value tv tA i := by
      rw [Fin.forall_fin_two]
      constructor
      · rw [hv0]
        norm_num
      · rw [hv1]
        norm_num
    have hpos : positiveAgents tv tA = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hall i
    unfold positiveWelfare
    rw [hpos]
    have hprod : (∏ i ∈ Finset.univ, value tv tA i) = ∏ i, value tv tA i := by
      simp
    rw [hprod, Fin.prod_univ_two, hv0, hv1]
    norm_num
  exact ⟨hv0, hv1, hw⟩

/-- Test transfer values: moving good `1` to agent `1` gives values `4`
and `7`, with bundle `{1, 2}`. -/
theorem t2_transfer_values :
    value tv (transfer tA 1 1) 0 = 4 ∧ value tv (transfer tA 1 1) 1 = 7 ∧
    bundle (transfer tA 1 1) 1 = {1, 2} := by
  have hbB0 : bundle (transfer tA 1 1) 0 = {0} := by decide
  have hbB1 : bundle (transfer tA 1 1) 1 = {1, 2} := by decide
  have hvB0 : value tv (transfer tA 1 1) 0 = 4 := by
    unfold value bundleValue
    rw [hbB0, Finset.sum_singleton]
    rfl
  have hvB1 : value tv (transfer tA 1 1) 1 = 7 := by
    unfold value bundleValue
    rw [hbB1, Finset.sum_insert (by decide), Finset.sum_singleton]
    show (3 : ℝ) + 4 = 7
    norm_num
  exact ⟨hvB0, hvB1, hbB1⟩

end

end MathlibExtTest.GameTheory.FairDivision.MaxNashWelfareEF1
