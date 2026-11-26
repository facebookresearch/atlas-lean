/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StirlingTripleProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MetaMathlibExt

noncomputable section

private abbrev E (m k : ℕ) : ℝ :=
  MvPolynomial.eval (fun i : Fin m => (((i : ℕ) + 1 : ℕ) : ℝ)) (MvPolynomial.esymm (Fin m) ℝ k)

private abbrev H (m k : ℕ) : ℝ :=
  MvPolynomial.eval (fun i : Fin m => (((i : ℕ) + 1 : ℕ) : ℝ)) (MvPolynomial.hsymm (Fin m) ℝ k)

private theorem pos (k : ℕ) (hk : 1 ≤ k) : 0 < (k : ℝ) := by
  exact_mod_cast (show 0 < k by omega)

private theorem lc (k : ℕ) (hk : 2 ≤ k) :
    ((k - 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by
  rw [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_add, Nat.cast_one]
  nlinarith

-- The common boundary: both elementary denominators of top degree are nonzero.
example : E 3 2 / E 2 2 ≤ E 3 1 / E 2 1 * (E 2 1 / E 1 1) ∧
    H 3 1 / H 2 1 * (H 2 1 / H 1 1) ≤ H 2 2 / H 1 2 :=
  symm_triple_ratio_of_logConcave (fun k => (k : ℝ)) (hpos := pos) (hlc := lc)
    (n := 1) (p := 1) (j := 1) (by decide) (by decide) (by decide) (h11 := Or.inl ⟨rfl, rfl⟩)

-- Use a strictly log-concave, nonconstant sequence and visit each disjunct alone.
example : E 5 2 / E 4 2 ≤ E 5 1 / E 4 1 * (E 4 1 / E 3 1) ∧
    H 5 1 / H 4 1 * (H 4 1 / H 3 1) ≤ H 4 2 / H 3 2 :=
  symm_triple_ratio_of_logConcave (fun k => (k : ℝ)) pos lc
    (n := 1) (p := 1) (j := 3) (by decide) (by decide) (by decide) (Or.inl ⟨rfl, rfl⟩)

example : E 5 4 / E 4 4 ≤ E 5 1 / E 4 1 * (E 4 3 / E 3 3) ∧
    H 5 1 / H 4 1 * (H 2 3 / H 1 3) ≤ H 2 4 / H 1 4 :=
  symm_triple_ratio_of_logConcave (fun k => (k : ℝ)) pos lc
    (n := 1) (p := 3) (j := 1) (by decide) (by decide) (by decide) (Or.inr (Or.inl ⟨rfl, rfl⟩))

example : E 5 4 / E 4 4 ≤ E 5 3 / E 4 3 * (E 2 1 / E 1 1) ∧
    H 3 3 / H 2 3 * (H 2 1 / H 1 1) ≤ H 2 4 / H 1 4 :=
  symm_triple_ratio_of_logConcave (fun k => (k : ℝ)) pos lc
    (n := 3) (p := 1) (j := 1) (by decide) (by decide) (by decide) (Or.inr (Or.inr ⟨rfl, rfl⟩))

-- Both bounds are strict when n = 4, p = 2 and j = 2.
example :
    (Nat.stirlingFirst 4 2 : ℚ) * Nat.stirlingFirst 6 4 / Nat.stirlingFirst 6 2 <
        (Nat.choose 4 2 : ℚ) ∧
      (Nat.choose 4 2 : ℚ) <
        (Nat.stirlingSecond 4 2 : ℚ) * Nat.stirlingSecond 6 4 / Nat.stirlingSecond 6 2 := by
  constructor <;> norm_num [Nat.stirlingFirst, Nat.stirlingSecond, Nat.choose]

-- At p = n = 3 the positive denominators cancel and both bounds are equalities.
example :
    (Nat.stirlingFirst 5 2 : ℚ) * Nat.stirlingFirst 5 5 / Nat.stirlingFirst 5 2 =
        (Nat.choose 3 3 : ℚ) ∧
      (Nat.choose 3 3 : ℚ) =
        (Nat.stirlingSecond 5 2 : ℚ) * Nat.stirlingSecond 5 5 / Nat.stirlingSecond 5 2 := by
  constructor <;> norm_num [Nat.stirlingFirst, Nat.stirlingSecond, Nat.choose]

-- Apply the public theorem at the minimum p and j, with p < n.
example :
    (Nat.choose 2 1 : ℚ) ≤
        (Nat.stirlingSecond 2 1 : ℚ) * Nat.stirlingSecond 3 2 / Nat.stirlingSecond 3 1 ∧
      (Nat.stirlingFirst 2 1 : ℚ) * Nat.stirlingFirst 3 2 / Nat.stirlingFirst 3 1 ≤
        (Nat.choose 2 1 : ℚ) :=
  stirling_triple_ratio_bounds_choose (n := 2) (p := 1) (j := 1)
    (hp := by decide) (hj := by decide) (hpn := by decide)
