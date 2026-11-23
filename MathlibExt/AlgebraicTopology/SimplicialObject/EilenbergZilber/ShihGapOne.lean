/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihFormula

/-!
# The gap-one family in the explicit Shih formula

These are the terms not obtained by deriving a lower-degree Shih term.  The
lemmas below put their two simplex maps into the pointwise form used for the
`F'_n s_0` edge calculation in the Eilenberg--Mac Lane recursion.
-/

@[expose] public section

set_option autoImplicit false

namespace AlgebraicTopology.EilenbergZilber.ShihIndex

theorem gap_eq_one_iff {n : ℕ} (i : ShihIndex n) :
    i.gap = 1 ↔ (i.p : ℕ) + 1 + i.q = n := by
  have hsum := i.p_add_q_add_gap
  constructor <;> intro h <;> omega

theorem q_eq_of_gap_eq_one {n : ℕ} (i : ShihIndex n) (hi : i.gap = 1) :
    (i.q : ℕ) = n - 1 - i.p := by
  have hsum := i.p_add_q_add_gap
  omega

theorem p_add_one_add_q_eq {n : ℕ} (i : ShihIndex n) (hi : i.gap = 1) :
    (i.p : ℕ) + 1 + i.q = n := by
  have hsum := i.p_add_q_add_gap
  omega

@[simp]
theorem leftHom_zero_of_gap_eq_one {n : ℕ} (i : ShihIndex n)
    (hi : i.gap = 1) : i.leftHom.toOrderHom 0 = 0 := by
  simp [leftHom, hi]

@[simp]
theorem rightHom_zero_of_gap_eq_one {n : ℕ} (i : ShihIndex n)
    (hi : i.gap = 1) : i.rightHom.toOrderHom 0 = 0 := by
  simp [rightHom, hi]

theorem leftHom_succ_of_gap_eq_one {n : ℕ} (i : ShihIndex n)
    (hi : i.gap = 1) (k : Fin (n + 1)) :
    (i.leftHom.toOrderHom k.succ).val =
      (i.shuffle.leftHom.toOrderHom
        (Fin.cast (by rw [i.p_add_one_add_q_eq hi]) k)).val := by
  simp [leftHom, hi, suffixInput]
  congr 2

theorem rightHom_succ_of_gap_eq_one {n : ℕ} (i : ShihIndex n)
    (hi : i.gap = 1) (k : Fin (n + 1)) :
    (i.rightHom.toOrderHom k.succ).val =
      (i.p : ℕ) + 1 +
        (i.shuffle.rightHom.toOrderHom
          (Fin.cast (by rw [i.p_add_one_add_q_eq hi]) k)).val := by
  let input : Fin (i.p + 1 + i.q + 1) :=
    i.suffixInput k.succ (by
      rw [hi]
      exact Nat.succ_le_succ (Nat.zero_le k))
  let castInput : Fin (i.p + 1 + i.q + 1) :=
    Fin.cast (by rw [i.p_add_one_add_q_eq hi]) k
  have hinput : input = castInput := by
    apply Fin.ext
    simp [input, castInput, suffixInput, hi]
  have h :
      1 + (i.p : ℕ) + (i.shuffle.rightHom.toOrderHom input).val =
        (i.p : ℕ) + 1 + (i.shuffle.rightHom.toOrderHom castInput).val := by
    rw [hinput, Nat.add_comm 1 (i.p : ℕ)]
  simpa [rightHom, hi, input, castInput, suffixInput] using h

theorem sign_of_gap_eq_one {n : ℕ} (i : ShihIndex n) (hi : i.gap = 1) :
    i.sign = shuffleSignZ i.shuffle := by
  simp [sign, hi]

end AlgebraicTopology.EilenbergZilber.ShihIndex
