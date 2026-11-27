/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.GenericGroup.Shoup

@[expose] public section

namespace CSLibExtTest.Crypto.Framework.GenericGroup.ShoupTests

open Cslib.Crypto.Framework Cslib.Crypto.Framework.GenericGroup Finset

instance fact7 : Fact (Nat.Prime 7) := ⟨by decide⟩

def enc7 : Equiv.Perm (ZMod 7) := Equiv.swap 0 3

def T0 : GTree (ZMod 7) 3 := .eqTest 2 0 (.out 0) (.eqTest 2 1 (.out 1) (.out 2))

example : (univ.filter fun x : ZMod 7 =>
    GTree.eval (oracleOf enc7) (dlogInputs enc7 x) T0 = x).card = 3 := by decide

example : (univ.filter fun x : ZMod 7 =>
    GTree.eval (oracleOf enc7) (dlogInputs enc7 x) T0 = x).card ≤ 4 :=
  (dlog_success_card_le enc7 T0 (m := 0) (by decide)).trans (by decide)

example : (univ.filter fun x : ZMod 7 => ∃ u ∈ symLabels (q := 7) T0,
    ∃ v ∈ symLabels (q := 7) T0, u ≠ v ∧ affEval x u = affEval x v).card = 2 := by decide

example : (univ.filter fun x : ZMod 7 =>
    affEval x ((0, 1) : Aff 7) = affEval x (1, 0)).card = 1 := by decide

example : (univ.filter fun x : ZMod 7 =>
    affEval x ((0, 1) : Aff 7) = affEval x (1, 1)).card = 0 := by decide

example : (univ.filter fun x : ZMod 4 =>
    affEval x ((0, 2) : Aff 4) = affEval x (0, 0)).card = 2 := by decide

example : winProb ((Cslib.Probability.PMF.uniformOfFintype (ZMod 7)).map fun x =>
    decide (affEval x ((0, 1) : Aff 7) = affEval x (1, 0))) = 1 / 7 := by
  rw [winProb_map_uniform, ZMod.card]
  have h : (univ.filter fun x : ZMod 7 =>
      decide (affEval x ((0, 1) : Aff 7) = affEval x (1, 0)) = true).card = 1 := by decide
  rw [h]
  norm_num

example : winProb ((Cslib.Probability.PMF.uniformOfFintype (ZMod 7)).map fun x =>
    decide (GTree.eval (oracleOf enc7) (dlogInputs enc7 x) T0 = x)) = 3 / 7 := by
  rw [winProb_map_uniform, ZMod.card]
  have h : (univ.filter fun x : ZMod 7 =>
      decide (GTree.eval (oracleOf enc7) (dlogInputs enc7 x) T0 = x) = true).card = 3 := by
    decide
  rw [h]
  norm_num

-- With the identity label, a count over the `m + 2` forms of Shoup's game fails: `T0` makes no
-- group operation and wins with probability `3 / 7`, above `((0 + 2).choose 2 + 1) / 7`.
example : ¬ winProb ((Cslib.Probability.PMF.uniformOfFintype (ZMod 7)).map fun x =>
    decide (GTree.eval (oracleOf enc7) (dlogInputs enc7 x) T0 = x)) ≤
      (((0 + 2).choose 2 + 1 : ℕ) : ℝ) / 7 := by
  rw [winProb_map_uniform, ZMod.card]
  have h : (univ.filter fun x : ZMod 7 =>
      decide (GTree.eval (oracleOf enc7) (dlogInputs enc7 x) T0 = x) = true).card = 3 := by
    decide
  rw [h]
  norm_num

example : winProb ((Cslib.Probability.PMF.uniformOfFintype (ZMod 7)).map fun x =>
    decide (GTree.eval (oracleOf enc7) (dlogInputs enc7 x) T0 = x)) ≤
      (((0 + 3).choose 2 + 1 : ℕ) : ℝ) / 7 := by
  exact_mod_cast dlog_winProb_le enc7 T0 (m := 0) (by decide)

example : winProb (genericDlogGame 7 T0) ≤ (((0 + 3).choose 2 + 1 : ℕ) : ℝ) / 7 :=
  genericDlog_winProb_le T0 (m := 0) (by decide)

example : winProb (genericDlogGame 7 T0) ≤ (((0 : ℕ) : ℝ) + 3) ^ 2 / 7 :=
  genericDlog_winProb_le_sq T0 (m := 0) (by decide)

def T2 : GTree (ZMod 2) 3 := .eqTest 2 0 (.out 0) (.out 1)

instance fact2 : Fact (1 < 2) := ⟨by decide⟩

example : winProb (genericDlogGame 2 T2) = 1 := by
  rw [genericDlogGame, winProb_map_uniform, Fintype.card_prod, ZMod.card]
  have h : (univ.filter fun ω : Equiv.Perm (ZMod 2) × ZMod 2 =>
      decide (GTree.eval (oracleOf ω.1) (dlogInputs ω.1 ω.2) T2 = ω.2) = true).card = 4 := by
    decide
  rw [h, Fintype.card_perm, ZMod.card]
  norm_num

#print axioms affEval_eq_card_le_one
#print axioms affEval_agree_winProb_le
#print axioms collision_card_le
#print axioms dlog_success_card_le
#print axioms dlog_winProb_le
#print axioms genericDlogGame
#print axioms genericDlog_winProb_le
#print axioms genericDlog_winProb_le_sq

end CSLibExtTest.Crypto.Framework.GenericGroup.ShoupTests
