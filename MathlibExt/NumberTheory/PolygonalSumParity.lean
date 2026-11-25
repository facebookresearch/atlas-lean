/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import MathlibExt.NumberTheory.PolygonalNumber

/-!
# Parity of polygonal sums

Pascal's identity shows that shifting an index by four changes its binomial
coefficient by an even number. Thus each polygonal summand has constant parity
on a residue class modulo four.
-/

namespace MetaMathlibExt

private theorem polygonalNumber_add_four_modEq_two (s x : ℕ) :
    Nat.polygonalNumber s (x + 4) ≡ Nat.polygonalNumber s x [MOD 2] := by
  have pascal (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
    simpa [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ k 1
  have hchoose : (x + 4).choose 2 = x.choose 2 + (4 * x + 6) := by
    rw [show x + 4 = (((x + 1) + 1) + 1) + 1 by omega, pascal, pascal, pascal, pascal]
    omega
  have hc : (x + 4).choose 2 ≡ x.choose 2 [MOD 2] := by
    rw [hchoose]
    unfold Nat.ModEq
    omega
  have hx : x + 4 ≡ x [MOD 2] := by
    unfold Nat.ModEq
    omega
  exact (hc.mul_left (s - 2)).add hx

private theorem polygonalNumber_modEq_two_of_modEq_four (s : ℕ) {x y : ℕ}
    (h : x ≡ y [MOD 4]) : Nat.polygonalNumber s x ≡ Nat.polygonalNumber s y [MOD 2] := by
  have shift (a k : ℕ) :
      Nat.polygonalNumber s (a + 4 * k) ≡ Nat.polygonalNumber s a [MOD 2] := by
    induction k with
    | zero =>
      simpa only [Nat.mul_zero, Nat.add_zero] using
        (show Nat.polygonalNumber s a ≡ Nat.polygonalNumber s a [MOD 2] from Nat.ModEq.rfl)
    | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc]
      exact (polygonalNumber_add_four_modEq_two s (a + 4 * k)).trans ih
  have reduce (a : ℕ) : Nat.polygonalNumber s a ≡ Nat.polygonalNumber s (a % 4) [MOD 2] := by
    simpa only [Nat.mod_add_div] using shift (a % 4) (a / 4)
  change x % 4 = y % 4 at h
  exact (reduce x).trans (h.symm ▸ (reduce y).symm)

@[expose] public section

/-- **Parity of sums of two polygonal numbers.** For a natural number $s > 3$ and a natural
number $x$, let $P_s(x) = (s-2)\binom{x}{2} + x$ be the $x$-th $s$-gonal number. For every
natural number $n > 0$ there are natural numbers $x, y > 0$ such that
$P_s(x_1) + P_s(y_1) \equiv n \pmod{2}$ for all natural numbers $x_1, y_1 > 0$ with
$x_1 \equiv x \pmod{4}$ and $y_1 \equiv y \pmod{4}$.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 7
(arXiv Lemma 4.2; `jis-2024-24.5.1-lem-7`). -/
public theorem exists_polygonal_add_polygonal_modEq_two (n s : ℕ) (hn : 0 < n)
    (hs : 3 < s) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ ∀ x₁ y₁ : ℕ, 0 < x₁ → 0 < y₁ → x₁ ≡ x [MOD 4] → y₁ ≡ y [MOD 4] →
      Nat.polygonalNumber s x₁ + Nat.polygonalNumber s y₁ ≡ n [MOD 2] := by
  have lift {x y : ℕ} (h : Nat.polygonalNumber s x + Nat.polygonalNumber s y ≡ n [MOD 2])
      (x₁ y₁ : ℕ) (hx : x₁ ≡ x [MOD 4]) (hy : y₁ ≡ y [MOD 4]) :
      Nat.polygonalNumber s x₁ + Nat.polygonalNumber s y₁ ≡ n [MOD 2] :=
    ((polygonalNumber_modEq_two_of_modEq_four s hx).add
      (polygonalNumber_modEq_two_of_modEq_four s hy)).trans h
  by_cases h : n % 2 = 0
  · refine ⟨1, 1, by decide, by decide, fun x₁ y₁ _ _ hx hy => lift ?_ x₁ y₁ hx hy⟩
    rw [Nat.polygonalNumber_one]
    change 0 = n % 2
    exact h.symm
  · refine ⟨4, 1, by decide, by decide, fun x₁ y₁ _ _ hx hy => lift ?_ x₁ y₁ hx hy⟩
    have hfour : Nat.polygonalNumber s 4 ≡ 0 [MOD 2] := by
      rw [Nat.polygonalNumber_at_four s (by omega)]
      unfold Nat.ModEq
      omega
    have hone : 1 ≡ n [MOD 2] :=
      (Nat.modEq_iff_dvd' hn).mpr (by omega)
    simpa only [Nat.polygonalNumber_one, zero_add] using
      (hfour.add (Nat.ModEq.refl 1)).trans hone

end -- public section

end MetaMathlibExt
