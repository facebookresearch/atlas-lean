/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.GDifferenceBases
import Mathlib.Tactic.NormNum.RealSqrt

/-! # Tests for difference representation counts and the interval lower bound -/

open MetaMathlibExt

-- Two different ordered pairs give difference 2, even though one uses a negative integer.
example : subRepCount ({-1, 0, 1, 2} : Finset ℤ) 2 = 2 := by decide

-- Multiplicities multiply for coordinate differences in different finite groups.
example :
    4 ≤ subRepCount (({0, 1} : Finset (ZMod 2)) ×ˢ ({0, 1, 2} : Finset (ZMod 4))) (1, 3) :=
  subRepCount_prod_ge 2 2 ({0, 1} : Finset (ZMod 2)) ({0, 1, 2} : Finset (ZMod 4))
    (by decide) (by decide) (1, 3)

-- At multiplicity zero the empty set attains the minimum.
example (n : ℕ) : diffBasisNumber 0 n = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le (s := {k | ∃ A : Finset ℤ, A.card = k ∧
    ∀ x ∈ Finset.Icc (1 : ℤ) n, 0 ≤ subRepCount A x})
  exact ⟨∅, rfl, fun _ _ => Nat.zero_le _⟩

-- Four positive differences, each required twice, force at least four elements.
example : 4 ≤ diffBasisNumber 2 4 := by
  have h := sqrt_two_mul_le_diffBasisNumber_div_sqrt 2 4 (by decide)
  norm_num at h
  exact_mod_cast (by linarith : (4 : ℝ) ≤ diffBasisNumber 2 4)

-- For n = 1 the short interval is empty, so both witnesses are multiples of k.
example : 1 ≤ subRepCount ({1, 2} : Finset ℤ) 1 := by
  have h := redeiRenyi_diffBasis 1 (by decide)
  have hk : ⌈Real.sqrt ((1 : ℕ) : ℝ)⌉₊ = 1 := by norm_num
  dsimp only at h
  rw [hk] at h
  have hB : Finset.Icc (1 : ℤ) ((1 : ℤ) - 1) ∪
      (Finset.Icc (1 : ℤ) (1 + 1)).image (· * (1 : ℤ)) = {1, 2} := by decide
  exact hB ▸ h.2 1 (by decide)

-- At a square endpoint both the zero and nonzero remainder cases occur.
example : 1 ≤ subRepCount ({1, 2, 4, 6} : Finset ℤ) 3 ∧
    1 ≤ subRepCount ({1, 2, 4, 6} : Finset ℤ) 4 := by
  have h := redeiRenyi_diffBasis 4 (by decide)
  have hk : ⌈Real.sqrt ((4 : ℕ) : ℝ)⌉₊ = 2 := by norm_num
  dsimp only at h
  rw [hk] at h
  have hB : Finset.Icc (1 : ℤ) ((2 : ℤ) - 1) ∪
      (Finset.Icc (1 : ℤ) (2 + 1)).image (· * (2 : ℤ)) = {1, 2, 4, 6} := by decide
  exact ⟨hB ▸ h.2 3 (by decide), hB ▸ h.2 4 (by decide)⟩
