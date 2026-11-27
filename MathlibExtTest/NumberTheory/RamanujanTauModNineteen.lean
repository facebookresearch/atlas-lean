/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RamanujanTauModNineteen
import Mathlib.Tactic.Linarith

open MetaMathlibExt

/-- Only `r = 0` has `P(r) = 0`. -/
private theorem ramanujanTauModNineteenTest_eq_zero {r : ℤ} (h : pentagonal r = 0) : r = 0 :=
  pentagonal_injective (h.trans (by simp [pentagonal_def]))

/-- `19 P(r) ≤ 19` only for `r = 0` and `r = 1`. -/
private theorem ramanujanTauModNineteenTest_eq_zero_or_one {r : ℤ}
    (h : 19 * pentagonal r ≤ 19) : r = 0 ∨ r = 1 := by
  have h₂ := two_mul_natCast_pentagonal r
  have h' : (pentagonal r : ℤ) ≤ 1 := by exact_mod_cast (by omega : pentagonal r ≤ 1)
  rcases (by omega : r ≤ -1 ∨ r = 0 ∨ r = 1 ∨ 2 ≤ r) with hr | hr | hr | hr
  · nlinarith
  · exact Or.inl hr
  · exact Or.inr hr
  · nlinarith

/-- `19 P(r) ≤ 38` only for `r = -1`, `r = 0` and `r = 1`. -/
private theorem ramanujanTauModNineteenTest_mem {r : ℤ}
    (h : 19 * pentagonal r ≤ 38) : r ∈ ({-1, 0, 1} : Finset ℤ) := by
  have h₂ := two_mul_natCast_pentagonal r
  have h' : (pentagonal r : ℤ) ≤ 2 := by exact_mod_cast (by omega : pentagonal r ≤ 2)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases (by omega : r ≤ -2 ∨ r = -1 ∨ r = 0 ∨ r = 1 ∨ 2 ≤ r) with hr | hr | hr | hr | hr
  · nlinarith
  · exact Or.inl hr
  · exact Or.inr (Or.inl hr)
  · exact Or.inr (Or.inr hr)
  · nlinarith

-- At n = 1 only r = 0 contributes: τ(2) ≡ τ_5(2) (mod 19), that is -24 ≡ -5. The printed form,
-- with τ_5(1) = 1 in place of τ_5(2), fails here.
example : generalizedTau 24 2 ≡ generalizedTau 5 2 [ZMOD 19] := by
  have h := ramanujanTau_succ_modEq_pentagonal_tau_five 1 one_pos
  rw [Finset.sum_eq_single_of_mem (0 : ℤ) (by simp) fun r _ hr => ite_eq_right fun h' =>
    hr (ramanujanTauModNineteenTest_eq_zero (by omega))] at h
  simpa [pentagonal_def] using h

-- At n = 19 the term r = 1 enters with 19 P(1) = n, and contributes -τ_5(1) = -1.
example : generalizedTau 24 20 ≡ generalizedTau 5 20 - 1 [ZMOD 19] := by
  have h := ramanujanTau_succ_modEq_pentagonal_tau_five 19 (by norm_num)
  rw [Finset.sum_eq_add_of_mem (0 : ℤ) 1 (by simp) (by simp) (by norm_num)
      fun r _ hr => ite_eq_right fun h' =>
        ((ramanujanTauModNineteenTest_eq_zero_or_one h').elim hr.1 hr.2).elim] at h
  simpa [pentagonal_def, generalizedTau_one, sub_eq_add_neg] using h

-- At n = 38 the negative index r = -1 enters, with P(-1) = 2 and sign (-1)^(-1) = -1.
example : generalizedTau 24 39 ≡ generalizedTau 5 39 - generalizedTau 5 20 - 1 [ZMOD 19] := by
  have h := ramanujanTau_succ_modEq_pentagonal_tau_five 38 (by norm_num)
  rw [← Finset.sum_subset (s₁ := {-1, 0, 1})
      (by
        intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl <;> simp)
      fun r _ hr => ite_eq_right fun h' => hr (ramanujanTauModNineteenTest_mem h')] at h
  simpa [pentagonal_def, generalizedTau_one, sub_eq_add_neg, add_comm, add_left_comm] using h
