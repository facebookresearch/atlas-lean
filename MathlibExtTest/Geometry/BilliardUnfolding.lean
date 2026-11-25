/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.BilliardUnfolding
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum

open MathlibExt.Geometry.ScottishBook147Wanted

-- In a square the first corner lies one tile away, with no intervening reflections.
example (a : ℝ) (ha : 0 < a) :
    ∃ k l N : ℕ, (k : ℝ) * a = a ∧ (l : ℝ) * a = a ∧ N + 2 = k + l ∧ N = 0 := by
  obtain ⟨t, k, l, N, _, _, _, htk, htl, hN, hcop, _⟩ :=
    billiardUnfoldingDiagonalLemma a a ha ha ⟨2, 2, by decide, by decide, rfl⟩
  have hkl : k = l := Nat.cast_inj.mp (mul_right_cancel₀ ha.ne' (htk.symm.trans htl))
  subst l
  have hk : k = 1 := by simpa using hcop.gcd_eq_one
  subst k
  exact ⟨1, 1, N, by simp, by simp, hN, by omega⟩

-- In a 1 × 2 rectangle the unreduced relation 4 = 2 · 2 folds to the corner (0, 2).
example : ∃ k l N : ℕ, (k : ℝ) * 1 = l * 2 ∧ N + 2 = k + l ∧ N = 1 ∧
    (if k % 2 = 1 then (1 : ℝ) else 0, if l % 2 = 1 then (2 : ℝ) else 0) = (0, 2) := by
  obtain ⟨t, k, l, N, _, _, _, htk, htl, hN, hcop, _⟩ :=
    billiardUnfoldingDiagonalLemma 1 2 (by norm_num) (by norm_num)
      ⟨2, 4, by decide, by decide, by norm_num⟩
  have hkl : k = l * 2 := by exact_mod_cast (by simpa using htk.symm.trans htl : (k : ℝ) = l * 2)
  have hl : l = 1 := Nat.eq_one_of_dvd_coprimes hcop (hkl ▸ dvd_mul_right l 2) (dvd_refl l)
  subst l
  subst k
  exact ⟨_, _, N, htk.symm.trans htl, hN, by omega, by norm_num⟩
