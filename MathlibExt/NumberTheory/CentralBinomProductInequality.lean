/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Central
import MathlibExt.NumberTheory.CentralBinomProductEquationOne

/-!
# Allen's inequality for central binomial products

We prove the upper bound and characterize equality by comparing consecutive products
on the diagonal `x = a`, then increasing the shift `x`.
-/

namespace MetaMathlibExt

namespace centralBinom_add_le_centralBinom_mul_choose_of_le

/-- For positive `a` and `b`, increasing `a` on the diagonal makes the bound strict. -/
private theorem diagonal_step {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : (a + b).centralBinom ≤ a.centralBinom * (a + 2 * b).choose b) :
    (a + 1 + b).centralBinom < (a + 1).centralBinom * (a + 1 + 2 * b).choose b := by
  let k := a + b
  let n := a + 2 * b
  change k.centralBinom ≤ a.centralBinom * n.choose b at h
  rw [show a + 1 + b = k + 1 by omega, show a + 1 + 2 * b = n + 1 by omega]
  have hc : n.choose b * (n + 1) = (n + 1).choose b * (k + 1) := by
    rw [Nat.choose_mul_succ_eq, show n + 1 - b = k + 1 by dsimp [n, k]; omega]
  have hg : (a + 1) * (2 * (2 * k + 1)) < (2 * (2 * a + 1)) * (n + 1) := by
    dsimp [k, n]
    nlinarith [Nat.mul_pos ha hb]
  apply Nat.lt_of_mul_lt_mul_left (a := (a + 1) * (k + 1))
  calc
    _ = ((a + 1) * (2 * (2 * k + 1))) * k.centralBinom := by
      rw [mul_assoc, Nat.succ_mul_centralBinom_succ, ← mul_assoc]
    _ < ((2 * (2 * a + 1)) * (n + 1)) * k.centralBinom :=
      Nat.mul_lt_mul_of_pos_right hg (Nat.centralBinom_pos k)
    _ ≤ ((2 * (2 * a + 1)) * (n + 1)) * (a.centralBinom * n.choose b) :=
      Nat.mul_le_mul_left _ h
    _ = ((2 * (2 * a + 1)) * a.centralBinom) * (n.choose b * (n + 1)) := by ac_rfl
    _ = _ := by rw [← Nat.succ_mul_centralBinom_succ, hc]; ac_rfl

private theorem diagonal (a b : ℕ) (hb : 0 < b) :
    (a + b).centralBinom ≤ a.centralBinom * (a + 2 * b).choose b ∧
      ((a + b).centralBinom = a.centralBinom * (a + 2 * b).choose b ↔ a ≤ 1) := by
  induction a with
  | zero => simp [Nat.centralBinom]
  | succ a ih =>
    obtain rfl | ha := a.eq_zero_or_pos
    · have heq := (centralBinom_add_eq_centralBinom_mul_choose_one_iff 1 b (by decide) hb).2 rfl
      simp [heq]
    · have hlt := diagonal_step ha hb ih.1
      exact ⟨hlt.le, iff_of_false hlt.ne (by omega)⟩

end centralBinom_add_le_centralBinom_mul_choose_of_le

/-- **Allen's inequality for central binomial products.** Let $x$ and $b$ be positive integers
and let $a$ be a nonnegative integer with $a \le x$. Then
$\binom{2(a+b)}{a+b} \le \binom{2a}{a}\binom{x+2b}{b}$, and equality holds if and only if
$x = 1$ and $a = 1$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Proposition 1 (`integers-2026-A26-prop-1`). -/
public theorem centralBinom_add_le_centralBinom_mul_choose_of_le (x a b : ℕ) (hx : 0 < x)
    (hb : 0 < b) (hax : a ≤ x) :
    (a + b).centralBinom ≤ a.centralBinom * (x + 2 * b).choose b ∧
      ((a + b).centralBinom = a.centralBinom * (x + 2 * b).choose b ↔ x = 1 ∧ a = 1) := by
  obtain ⟨hle, heq⟩ := centralBinom_add_le_centralBinom_mul_choose_of_le.diagonal a b hb
  rcases eq_or_lt_of_le hax with rfl | hlt
  · exact ⟨hle, heq.trans (by omega)⟩
  · have hchoose : (a + 2 * b).choose b < (x + 2 * b).choose b := by
      obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
      calc
        _ < (a + 2 * (c + 1) + 1).choose (c + 1) := by
          rw [Nat.choose_succ_succ]
          exact lt_add_of_pos_left _ (Nat.choose_pos (by omega))
        _ ≤ _ := Nat.choose_le_choose _ (by omega)
    have h := hle.trans_lt (Nat.mul_lt_mul_of_pos_left hchoose (Nat.centralBinom_pos a))
    exact ⟨h.le, iff_of_false h.ne (by omega)⟩

end MetaMathlibExt
