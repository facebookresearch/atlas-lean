/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.LevRectification

open MathlibExt.Combinatorics.ValidOrderingWanted

-- The empty domain also has an empty image, even when the order exceeds the modulus.
example : ∃ f : ZMod 2 → ℤ, IsAddFreimanIso 7 ∅ ∅ f := by
  obtain ⟨B, f, hf⟩ := exists_freimanIso_to_int 7 2 (by decide) (by decide) ∅ (by simp)
  have hb := hf.bijOn.image_eq
  simp only [Finset.coe_empty, Set.image_empty] at hb hf
  exact ⟨f, hb.symm ▸ hf⟩

-- Three elements fit because of the ceiling. In ZMod 5, 3 + 3 wraps to 0 + 1.
-- The images preserve that relation and distinguish it from 1 + 1.
example : ∃ f : ZMod 5 → ℤ, f 3 + f 3 = f 0 + f 1 ∧ f 3 + f 3 ≠ f 1 + f 1 := by
  let A : Finset (ZMod 5) := {0, 1, 3}
  have hcard : A.card ≤ ⌈Real.log 5 / Real.log 2⌉₊ := by
    rw [show A.card = 3 by decide, Nat.succ_le_iff, Nat.lt_ceil]
    apply (lt_div_iff₀ (Real.log_pos (by norm_num))).mpr
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 ^ 2) (by norm_num : (2 : ℝ) ^ 2 < 5)
    simpa [Real.log_pow] using h
  obtain ⟨_, f, hf⟩ := exists_freimanIso_to_int 2 5 (by decide) (by decide) A (by simpa using hcard)
  have h (a b : ZMod 5) (ha : a ∈ A) (hb : b ∈ A) :=
    hf.add_eq_add (a := 3) (b := 3) (by decide) (by decide) ha hb
  exact ⟨f, (h 0 1 (by decide) (by decide)).mpr (by decide),
    fun he => (by decide : (3 : ZMod 5) + 3 ≠ 1 + 1) ((h 1 1 (by decide) (by decide)).mp he)⟩
