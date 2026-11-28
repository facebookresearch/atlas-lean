/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ChocolateBarNSPropertyGrundy

namespace MathlibExtTest.GameTheory.ChocolateBarNSPropertyGrundy

open MetaMathlibExt

-- The two bounds clamp differently when the width is cut.
example : chocolateBarGrundy ![fun n ↦ n / 2 ^ 1, fun n ↦ n / 2 ^ 2] ![2, 1] 6 = 5 :=
  (hasNSProperty_and_iff_chocolateBarGrundy_eq_xor
    (fun _ _ h ↦ Nat.div_le_div_right h) (fun _ _ h ↦ Nat.div_le_div_right h)).mp
      ⟨hasNSProperty_div_two_pow (by decide), hasNSProperty_div_two_pow (by decide)⟩
      2 1 6 (by decide) (by decide)

-- The identity as the second bound prevents a nim-sum formula at all legal positions.
example : ¬ ∀ x y z : ℕ, x ≤ 2 → y ≤ z →
    chocolateBarGrundy ![fun _ ↦ 2, id] ![x, y] z = x ^^^ y ^^^ z := by
  intro h
  exact not_hasNSProperty_id
    ((hasNSProperty_and_iff_chocolateBarGrundy_eq_xor monotone_const monotone_id).mpr h).2

local notation "flatGrundy" f:max x:max z:max =>
  chocolateBarGrundy ![f, fun _ ↦ 0] ![x, 0] z

-- The terminal bar has no moves. At (0, 1) the only follower is the terminal bar.
private theorem flatGrundy_zero_zero (f : ℕ → ℕ) : flatGrundy f 0 0 = 0 := by
  rw [chocolateBarGrundy_eq]
  exact Nat.sInf_eq_zero.mpr (Or.inl (by simp [Fin.forall_fin_two]))

private theorem flatGrundy_zero_one (f : ℕ → ℕ) : flatGrundy f 0 1 = 1 := by
  have hcut : (fun i : Fin 2 ↦ min (![0, 0] i) (![f, fun _ ↦ 0] i 0)) = ![0, 0] := by
    funext i
    revert i
    simp [Fin.forall_fin_two]
  rw [chocolateBarGrundy_eq]
  simp [Fin.forall_fin_two, Nat.lt_one_iff, hcut, flatGrundy_zero_zero]
  apply le_antisymm (Nat.sInf_le (show 0 ≠ 1 by decide))
  exact le_csInf ⟨1, by decide⟩ (fun n hn ↦ Nat.pos_of_ne_zero (Ne.symm hn))

-- At (1, 0) the height cut is the only move; at (1, 1) a width cut is also possible.
private theorem flatGrundy_one_zero (f : ℕ → ℕ) : flatGrundy f 1 0 = 1 := by
  have hcut : Function.update (![1, 0] : Fin 2 → ℕ) 0 0 = ![0, 0] := by
    funext i
    revert i
    simp [Fin.forall_fin_two]
  rw [chocolateBarGrundy_eq]
  simp [Fin.forall_fin_two, Nat.lt_one_iff, hcut, flatGrundy_zero_zero]
  apply le_antisymm (Nat.sInf_le (show 0 ≠ 1 by decide))
  exact le_csInf ⟨1, by decide⟩ (fun n hn ↦ Nat.pos_of_ne_zero (Ne.symm hn))

private theorem flatGrundy_one_one_mex (f : ℕ → ℕ) :
    flatGrundy f 1 1 = sInf {m | 1 ≠ m ∧ flatGrundy f (min 1 (f 0)) 0 ≠ m} := by
  have hheight : Function.update (![1, 0] : Fin 2 → ℕ) 0 0 = ![0, 0] := by
    funext i
    revert i
    simp [Fin.forall_fin_two]
  have hwidth : (fun i : Fin 2 ↦ min (![1, 0] i) (![f, fun _ ↦ 0] i 0)) =
      ![min 1 (f 0), 0] := by
    funext i
    revert i
    simp [Fin.forall_fin_two]
  conv_lhs => rw [chocolateBarGrundy_eq]
  simp [Fin.forall_fin_two, Nat.lt_one_iff, hheight, hwidth, flatGrundy_zero_one]

-- The constant-one profile satisfies NS. Both cuts from (1, 1) have Grundy value one.
example : HasNSProperty (fun _ ↦ 1) ∧ flatGrundy (fun _ ↦ 1) 1 1 = (1 : ℕ) ^^^ 1 := by
  refine ⟨hasNSProperty_const 1, ?_⟩
  rw [flatGrundy_one_one_mex, min_self, flatGrundy_one_zero]
  exact Nat.sInf_eq_zero.mpr (Or.inl (by decide))

-- The identity fails NS. Cutting the width now clamps the height to zero, so the two
-- followers have values one and zero, and the mex differs from the nim-sum.
example : ¬ HasNSProperty id ∧ flatGrundy id 1 1 = 2 ∧ flatGrundy id 1 1 ≠ (1 : ℕ) ^^^ 1 := by
  have hvalue : flatGrundy id 1 1 = 2 := by
    rw [flatGrundy_one_one_mex, id_eq, min_zero, flatGrundy_zero_zero]
    apply le_antisymm (Nat.sInf_le (show 1 ≠ 2 ∧ 0 ≠ 2 by decide))
    apply le_csInf ⟨2, by decide⟩
    intro n hn
    change 1 ≠ n ∧ 0 ≠ n at hn
    omega
  exact ⟨not_hasNSProperty_id, hvalue, hvalue ▸ (by decide : 2 ≠ (1 : ℕ) ^^^ 1)⟩

-- A client can apply the characterization at a legal boundary position with nonzero nim-sum.
example : flatGrundy (fun _ ↦ 1) 1 0 = 1 :=
  (hasNSProperty_iff_chocolateBarGrundy_depth_zero monotone_const).mp
    (hasNSProperty_const 1) 1 0 le_rfl

end MathlibExtTest.GameTheory.ChocolateBarNSPropertyGrundy
