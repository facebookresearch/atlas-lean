/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Generalized Fuss–Catalan numbers

This file defines the generalized Fuss–Catalan numbers, also called Raney numbers.

Provenance: JIS semantic concept `jis_sem_69c4f50c7aa0eee05d643c54`, statement
`jis_059ca809c2428bd341da0fee`, from
<https://cs.uwaterloo.ca/journals/JIS/VOL21/He/he61.tex>, SHA-256
`c73d8bdaba1725e18630db49af924a0cb5433b6b00878e556c2c9fdb7e2ae320`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The generalized Fuss–Catalan number `F_m(n, k)`:
`k * Nat.choose (m * n + k) n / (m * n + k)`.

The source considers `m ≥ 2` and `n, k ≥ 1`. The definition is totalized over natural numbers.
-/
def generalizedFussCatalanNumber (m n k : ℕ) : ℕ :=
  k * Nat.choose (m * n + k) n / (m * n + k)

/-- The defining equation for `generalizedFussCatalanNumber`. -/
theorem generalizedFussCatalanNumber_eq (m n k : ℕ) :
    generalizedFussCatalanNumber m n k =
      k * Nat.choose (m * n + k) n / (m * n + k) :=
  rfl

/-- The specialization `F_m(1, k) = k`, corresponding to case (c) of the source theorem. -/
theorem generalizedFussCatalanNumber_one (m k : ℕ) :
    generalizedFussCatalanNumber m 1 k = k := by
  unfold generalizedFussCatalanNumber
  have hmk : m * 1 + k = m + k := by omega
  rw [hmk, Nat.choose_one_right]
  by_cases h : m + k = 0
  · have hk : k = 0 := by omega
    simp [hk]
  · have hpos : 0 < m + k := by omega
    exact Nat.mul_div_cancel k hpos

/-- The Fuss-Catalan (Raney) number `A_n(p, r)` is the canonical
`generalizedFussCatalanNumber p n r`, cast to `ℚ`; it equals `r/(pn + r) · C(pn + r, n)` (with
`x / 0 = 0`, so `A_0(p, 0) = 0`), the paper's definition.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Section 1. -/
theorem generalizedFussCatalanNumber_cast_eq_div_mul_choose (p n r : ℕ) :
    (generalizedFussCatalanNumber p n r : ℚ) =
      (r : ℚ) / (p * n + r) * ((p * n + r).choose n : ℚ) := by
  rcases Nat.eq_zero_or_pos (p * n + r) with h0 | hpos
  · have hr : r = 0 := by omega
    simp [generalizedFussCatalanNumber, hr]
  have hdvd : p * n + r ∣ r * (p * n + r).choose n := by
    rcases n with _ | m
    · simp
    · obtain ⟨M, hM⟩ : ∃ M, p * (m + 1) + r = M + 1 := ⟨p * (m + 1) + r - 1, by omega⟩
      have key := Nat.add_one_mul_choose_eq M m
      have e : r * (M + 1).choose (m + 1) + (M + 1) * (p * M.choose m) =
          (M + 1) * (M + 1).choose (m + 1) := by
        have : (M + 1) * (M + 1).choose (m + 1) =
            (r + p * (m + 1)) * (M + 1).choose (m + 1) := by rw [← hM]; ring
        rw [this]
        nlinarith [key]
      rw [hM]
      exact (Nat.dvd_add_left (dvd_mul_right _ _)).mp (e ▸ dvd_mul_right _ _)
  rw [generalizedFussCatalanNumber, Nat.cast_div hdvd (by positivity)]
  push_cast
  ring

end

end MetaMathlibExt
