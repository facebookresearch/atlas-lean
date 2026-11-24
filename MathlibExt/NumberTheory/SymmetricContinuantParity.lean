/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticIrrationalCFNonexistence
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Parity of even-length symmetric continuants

Splitting just before the midpoint expresses the final denominator as the central
coefficient times a square, plus twice a product of neighboring denominators.
-/

namespace MetaMathlibExt

private theorem square_modEq_two (q : ℕ) : q * q ≡ q [MOD 2] := by
  change (q * q) % 2 = q % 2
  rw [Nat.mul_mod]
  have hlt : q % 2 < 2 := Nat.mod_lt _ (by decide)
  have h : q % 2 = 0 ∨ q % 2 = 1 := by omega
  rcases h with h | h <;> simp [h]

/-- **Parity of $q_{l-1}$ for a symmetric sequence, even $l$.** Let $l \ge 2$ be even and let
$a_0, a_1, a_2, \dots$ be natural numbers with convergent denominators $q_0, q_1, q_2, \dots$,
such that $a_i = a_{l-i}$ for $1 \le i < l$. Then $q_{l-1} \equiv a_{l/2} \, q_{l/2-1} \pmod 2$.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Corollary 1 (i)
(`integers-2026-A69-cor-1`). -/
public theorem convergentDen_parity_of_even (l : ℕ) (hl : Even l) (hl0 : 0 < l)
    (a : ℕ → ℕ) (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    convergentDen a (l - 1) ≡ a (l / 2) * convergentDen a (l / 2 - 1) [MOD 2] := by
  obtain ⟨m, hm⟩ := hl
  by_cases hm1 : m = 1
  · rw [show l = 2 by omega]
    norm_num [convergentDen_zero, convergentDen_one, Nat.ModEq]
  have hsplit := convergentDen_symm_split l a hsymm (m - 1) (by omega) (by omega)
  rw [show l - 1 - (m - 1) = m by omega, show m - 1 - 1 = m - 2 by omega,
    show l - 2 - (m - 1) = m - 1 by omega] at hsplit
  have hrec := convergentDen_add_two a (m - 2)
  rw [show m - 2 + 2 = m by omega, show m - 2 + 1 = m - 1 by omega] at hrec
  rw [show l / 2 = m by omega]
  let q := convergentDen a (m - 1)
  let q' := convergentDen a (m - 2)
  calc
    convergentDen a (l - 1) = a m * (q * q) + 2 * (q * q') := by
      rw [hsplit, hrec]
      dsimp only [q, q']
      ring
    _ ≡ a m * (q * q) + 0 [MOD 2] :=
      (Nat.ModEq.refl _).add (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right 2 _))
    _ ≡ a m * q [MOD 2] := by
      rw [add_zero]
      exact (square_modEq_two q).mul_left (a m)

end MetaMathlibExt
