/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralPellBisectors
import Mathlib.Tactic.LinearCombination

/-!
# Divisibility in the negative Pell sequence

The second coordinate of a power of the fundamental negative Pell solution divides that of
another power exactly when its index divides the other index.
-/

namespace MetaMathlibExt

private theorem negPellFund_pos_spec {d : ℕ} (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) :
    0 < negPellFundX d ∧ 0 < negPellFundY d ∧
      negPellFundX d ^ 2 + 1 = d * negPellFundY d ^ 2 := by
  obtain ⟨x, y, hxy⟩ := hneg
  have hy : y ≠ 0 := by
    rintro rfl
    simp at hxy
    linarith [sq_nonneg x]
  have habs : (x.natAbs : ℤ) ^ 2 + 1 = (d : ℤ) * (y.natAbs : ℤ) ^ 2 := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs, sq_abs, sq_abs]
    linarith
  have ⟨hY, hnorm⟩ := negPellFund_spec (d := d)
    ⟨y.natAbs, Int.natAbs_pos.mpr hy, x.natAbs, by exact_mod_cast habs⟩
  have hge : 2 ≤ d * negPellFundY d ^ 2 :=
    calc 2 = 2 * 1 := by simp
      _ ≤ d * negPellFundY d ^ 2 := Nat.mul_le_mul (by omega) (Nat.succ_le_of_lt (pow_pos hY _))
  refine ⟨Nat.pos_of_ne_zero ?_, hY, hnorm⟩
  intro hX
  simp [hX] at hnorm
  omega

private theorem negPellG_strictMono {d : ℕ} (hX : 0 < negPellFundX d)
    (hY : 0 < negPellFundY d) : StrictMono (negPellG d) := by
  have hpos (n : ℕ) : 0 < negPellF d n ∧ 0 ≤ negPellG d n := by
    induction n with
    | zero => simp [negPellF_zero_negPellG_zero]
    | succ n ih =>
      rw [(negPell_succ d n).1, (negPell_succ d n).2]
      obtain ⟨_, _⟩ := ih
      constructor <;> positivity
  apply strictMono_nat_of_lt_succ
  intro n
  rw [(negPell_succ d n).2]
  have hX' : (1 : ℤ) ≤ negPellFundX d := by exact_mod_cast hX
  have hmul := mul_le_mul_of_nonneg_left hX' (hpos n).2
  rw [mul_one] at hmul
  exact hmul.trans_lt (lt_add_of_pos_left _ (mul_pos (hpos n).1 (by exact_mod_cast hY)))

private theorem negPellG_add (d a b : ℕ) :
    negPellG d (a + b) = negPellF d a * negPellG d b + negPellG d a * negPellF d b := by
  simp only [negPellG, negPellF, pow_add, Zsqrtd.im_mul]

private theorem negPellG_dvd_mul_index (d n q : ℕ) : negPellG d n ∣ negPellG d (n * q) := by
  induction q with
  | zero => simp [negPellF_zero_negPellG_zero]
  | succ q ih =>
    rw [Nat.mul_succ, negPellG_add]
    exact dvd_add (dvd_mul_left _ _) (ih.mul_right _)

private theorem negPell_norm {d : ℕ}
    (hfund : negPellFundX d ^ 2 + 1 = d * negPellFundY d ^ 2) (k : ℕ) :
    negPellF d k ^ 2 - d * negPellG d k ^ 2 = (-1) ^ k := by
  let u : ℤ√(d : ℤ) := ⟨negPellFundX d, negPellFundY d⟩
  have hcast : (negPellFundX d : ℤ) ^ 2 + 1 = (d : ℤ) * (negPellFundY d : ℤ) ^ 2 := by
    exact_mod_cast hfund
  have hu : u.norm = -1 := by
    change (negPellFundX d : ℤ) * negPellFundX d - (d : ℤ) * negPellFundY d * negPellFundY d = -1
    linear_combination hcast
  have hk := map_pow (Zsqrtd.normMonoidHom (d := (d : ℤ))) u k
  change (u ^ k).norm = u.norm ^ k at hk
  rw [hu, Zsqrtd.norm_def, ← sq, mul_assoc, ← sq] at hk
  exact hk

/-- **Divisibility of the second coordinates of negative Pell powers.** Let $d > 1$ be a natural
number such that $x^2 - d y^2 = -1$ has an integer solution, let $(X, Y)$ be its fundamental
solution (the one with $X, Y > 0$ and $Y$ least), and write
$(X + Y \sqrt{d})^n = f_n + g_n \sqrt{d}$. For natural numbers $0 < n \le m$, $g_n$ divides $g_m$
if and only if $n$ divides $m$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 11(d) (`integers-2024-A111-thm-11`). -/
public theorem negPellG_dvd_iff (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (m n : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    negPellG d n ∣ negPellG d m ↔ n ∣ m := by
  refine ⟨?_, ?_⟩
  · intro hdiv
    obtain ⟨hX, hY, hfund⟩ := negPellFund_pos_spec hd hneg
    have hmono := negPellG_strictMono hX hY
    let k := n * (m / n)
    let r := m % n
    have hsplit : k + r = m := Nat.div_add_mod m n
    have hk : negPellG d n ∣ negPellG d k := negPellG_dvd_mul_index d n (m / n)
    rw [← hsplit, negPellG_add] at hdiv
    have hprod : negPellG d n ∣ negPellF d k * negPellG d r := by
      simpa only [add_sub_cancel_right] using dvd_sub hdiv (hk.mul_right (negPellF d r))
    -- The signed norm gives an inverse for the first coordinate modulo `negPellG d n`.
    have hnorm := negPell_norm hfund k
    have hsigned : negPellG d n ∣ (-1 : ℤ) ^ k * negPellG d r := by
      rw [← hnorm, sub_mul]
      have hsq := (hk.mul_right (negPellG d k)).mul_left (d : ℤ)
      rw [← sq] at hsq
      exact dvd_sub (by simpa only [pow_two, mul_assoc] using hprod.mul_left (negPellF d k))
        (hsq.mul_right _)
    have hr : negPellG d n ∣ negPellG d r :=
      ((isUnit_one.neg.pow k).dvd_mul_left).mp hsigned
    have hzero := (negPellF_zero_negPellG_zero d).2
    have hr0 : r = 0 := by
      by_contra hne
      have hrpos : 0 < negPellG d r := hzero ▸ hmono (Nat.pos_of_ne_zero hne)
      exact (not_lt_of_ge (Int.le_of_dvd hrpos hr)) (hmono (Nat.mod_lt m hn))
    exact Nat.dvd_of_mod_eq_zero hr0
  · rintro ⟨q, rfl⟩
    exact negPellG_dvd_mul_index d n q

end MetaMathlibExt
