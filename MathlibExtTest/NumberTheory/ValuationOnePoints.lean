/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ValuationOnePoints
import Mathlib.Tactic.NormNum

/-!
# Tests for polynomial lifts modulo a prime square

Modulo three, the root two of `x - 8` lifts at index two.
Modulo two, the nonsingular root `(1, 0)` of `x² + y + 1` has two lifts of valuation one.
At the origin modulo three, `x² + y² + 3` has nine lifts with valuation one, and `xy` has none.
-/

namespace MetaMathlibExt

example :
    ((Finset.range 3).filter fun k : ℕ => (9 : ℤ) ∣ 2 + (k : ℤ) * 3 - 8) = {2} := by
  let g : Polynomial ℤ := Polynomial.X - Polynomial.C 8
  have h := card_lift_padicVal_gt_one_le_one Nat.prime_three g (r := 2) (by decide)
    (by norm_num [g])
  have hcard : ((Finset.range 3).filter fun k : ℕ => (9 : ℤ) ∣ 2 + (k : ℤ) * 3 - 8).card ≤ 1 := by
    simpa [g] using h
  apply Finset.eq_singleton_iff_unique_mem.mpr
  exact ⟨by decide, fun k hk => Finset.card_le_one.mp hcard k hk 2 (by decide)⟩

-- The derivative may vanish when the residue is not a root.
example (p : ℕ) (hp : p.Prime) :
    ((Finset.range p).filter fun k : ℕ => (p : ℤ) ^ 2 ∣ ((k : ℤ) * p) ^ 2 + 1).card ≤ 1 := by
  let g : Polynomial ℤ := Polynomial.X ^ 2 + 1
  have hp₁ : ¬ (p : ℤ) ∣ 1 := by exact_mod_cast hp.not_dvd_one
  have h := card_lift_padicVal_gt_one_le_one hp g (r := 0) hp.pos (by simpa [g] using hp₁)
  simpa [g] using h

open MvPolynomial

-- Only the y derivative is nonzero modulo two, and the base value is already two.
example :
    ((Finset.range 2 ×ˢ Finset.range 2).filter fun kl : ℕ × ℕ =>
      let z : ℤ := (1 + (kl.1 : ℤ) * 2) ^ 2 + kl.2 * 2 + 1
      2 ∣ z ∧ ¬ 4 ∣ z).card = 2 := by
  let f : MvPolynomial (Fin 2) ℤ := X 0 ^ 2 + X 1 + 1
  have h := card_lift_padicVal_eq_one Nat.prime_two f (r := 1) (s := 0)
    (by decide) (by decide) (by norm_num [f]) (by norm_num [f, pderiv_X])
  simpa [f] using h

example :
    ((Finset.range 3 ×ˢ Finset.range 3).filter fun kl : ℕ × ℕ =>
      let z : ℤ := (kl.1 * 3 : ℤ) ^ 2 + (kl.2 * 3 : ℤ) ^ 2 + 3
      3 ∣ z ∧ ¬ 9 ∣ z).card = 9 := by
  let f : MvPolynomial (Fin 2) ℤ := X 0 ^ 2 + X 1 ^ 2 + C 3
  have grad (i : Fin 2) : (3 : ℤ) ∣ eval ![0, 0] (pderiv i f) := by
    simp only [f, map_add, pderiv_C]
    simp
  have h := card_lift_padicVal_eq_one_of_singular Nat.prime_three f
    (r := 0) (s := 0) (by decide) (by decide) (by norm_num [f]) (grad 0) (grad 1)
  simpa [f] using h

example :
    ((Finset.range 3 ×ˢ Finset.range 3).filter fun kl : ℕ × ℕ =>
      let z : ℤ := (kl.1 * 3 : ℤ) * (kl.2 * 3 : ℤ)
      3 ∣ z ∧ ¬ 9 ∣ z).card = 0 := by
  let f : MvPolynomial (Fin 2) ℤ := X 0 * X 1
  have h := card_lift_padicVal_eq_one_of_singular Nat.prime_three f
    (r := 0) (s := 0) (by decide) (by decide) (by simp [f]) (by simp [f]) (by simp [f])
  simpa [f] using h

-- For `x + y` modulo three, the residues with `3 ∣ r + s` are `(0, 0)`, `(1, 2)` and
-- `(2, 1)`, and each contributes `3 * 2` pairs of valuation one modulo nine.
example :
    ((Finset.range 9 ×ˢ Finset.range 9).filter fun xy : ℕ × ℕ =>
      let z : ℤ := (xy.1 : ℤ) + xy.2
      3 ∣ z ∧ ¬ 9 ∣ z).card = 18 := by
  let f : MvPolynomial (Fin 2) ℤ := X 0 + X 1
  have hns : ∀ (r s : ℕ), r < 3 → s < 3 → ((3 : ℕ) : ℤ) ∣
      MvPolynomial.eval ![(r : ℤ), s] f →
      ¬ (((3 : ℕ) : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f) ∧
        ((3 : ℕ) : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f)) := by
    intro r _ s _ _
    simp only [f, map_add, pderiv_X]
    norm_num
  have h := card_padicVal_eq_one_mod_sq_eq Nat.prime_three f (fun r hr s hs => hns r s hr hs)
  have hm : ((Finset.range 3 ×ˢ Finset.range 3).filter fun rs : ℕ × ℕ =>
      ((3 : ℕ) : ℤ) ∣ MvPolynomial.eval ![(rs.1 : ℤ), rs.2] f).card = 3 := by
    simp only [f, map_add, eval_X]
    decide
  rw [hm] at h
  simpa [f] using h

end MetaMathlibExt
