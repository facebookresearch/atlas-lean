/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.OddGreedyChoice

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Odd greedy expansions and sums of odd unit fractions

Clearing the denominators gives an odd product. Each summand then contributes the product of
all denominators except its own. The first odd greedy denominator of a positive fraction is
characterized by comparing consecutive odd denominators.
-/

public section

namespace MathlibExt.NumberTheory.OddGreedyExpansionWanted

/-- **Even sums of odd unit fractions have even numerator.** Let $m$ be an even natural number
and let $d_1, \dots, d_m$ be odd natural numbers. If integers $a$ and $b$ with $b \ne 0$ satisfy
$a/b = \sum_{i=1}^{m} 1/d_i$, then $a$ is even.

See Joel Louwsma and Joseph Martino, *Rational numbers with odd greedy expansion of fixed length*,
[Proposition 2.1](https://arxiv.org/html/2309.07280).

Source: Joel Louwsma and Joseph Martino, "Rational
Numbers with Two-Term Odd Greedy Expansion",
Proposition 1. -/
theorem even_num_of_even_sum_unit_fractions
    (m : ℕ) (hm : Even m) (d : Fin m → ℕ)
    (hd : ∀ i, Odd (d i)) (a b : ℤ) (hb : b ≠ 0)
    (h : (a : ℚ) / (b : ℚ) = ∑ i, (1 : ℚ) / (d i : ℚ)) :
    Even a := by
  let D := ∏ i, d i
  let cofactor (i : Fin m) := ∏ j ∈ Finset.univ.erase i, d j
  have odd_prod (s : Finset (Fin m)) : Odd (∏ j ∈ s, d j) :=
    s.prod_induction d Odd (fun _ _ => Odd.mul) odd_one (fun j _ => hd j)
  have hD : Odd D := odd_prod _
  have hD₀ : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD.pos.ne'
  have hsum : Even (∑ i, cofactor i) := by
    rw [Finset.even_sum_iff_even_card_odd]
    have hcofactor (i : Fin m) : Odd (cofactor i) := odd_prod _
    simpa [hcofactor] using hm
  have hfrac : (a : ℚ) / b = ((∑ i, cofactor i : ℕ) : ℚ) / D := by
    rw [h, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_eq_div_iff (Nat.cast_ne_zero.mpr (hd i).pos.ne') hD₀, one_mul]
    exact_mod_cast (Finset.prod_erase_mul Finset.univ d (Finset.mem_univ i)).symm
  have hcross : a * (D : ℤ) = ((∑ i, cofactor i : ℕ) : ℤ) * b := by
    exact_mod_cast (div_eq_div_iff (Int.cast_ne_zero.mpr hb) hD₀).mp hfrac
  have he : Even (a * (D : ℤ)) := hcross ▸ hsum.natCast.mul_right b
  exact (Int.even_mul.mp he).resolve_right (by simpa using hD)

/-- **Odd greedy choice at a fraction.** Let $n$ and $d$ be positive natural numbers and let $x_1$
be an odd natural number. Then $x_1$ is the odd greedy choice at $n/d$ (the first denominator of
the odd greedy expansion of $n/d$) if and only if $d \le n x_1$ and $n x_1 < d + 2n$, that is,
$0 \le n x_1 - d < 2n$ in the integers.

Source: Joel Louwsma and Joseph Martino, "Rational
Numbers with Two-Term Odd Greedy Expansion", Lemma 2. -/
theorem isOddGreedyChoice_iff (n d x1 : ℕ)
    (hn : 0 < n) (hd : 0 < d) (hx : Odd x1) :
    MetaMathlibExt.IsOddGreedyChoice ((n : ℚ) / (d : ℚ)) x1 ↔
      d ≤ n * x1 ∧ n * x1 < d + 2 * n := by
  have admissible {e : ℕ} (he : 0 < e) :
      (1 : ℚ) / e ≤ (n : ℚ) / d ↔ d ≤ n * e := by
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr he) (Nat.cast_pos.mpr hd), one_mul]
    norm_cast
  constructor
  · intro h
    refine ⟨(admissible hx.pos).mp h.inv_le, ?_⟩
    by_contra! hlarge
    have hprev : d ≤ n * (x1 - 2) := by
      rw [Nat.mul_sub, Nat.mul_comm n 2]
      omega
    have hpos : 0 < x1 - 2 := Nat.pos_of_mul_pos_left (hd.trans_le hprev)
    have hodd := Nat.Odd.sub_even (by omega : 2 ≤ x1) hx even_two
    have hmin := h.min hpos hodd ((admissible hpos).mpr hprev)
    omega
  · rintro ⟨hlower, hupper⟩
    refine ⟨div_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hd), hx.pos, hx,
      (admissible hx.pos).mpr hlower, ?_⟩
    intro e he hodd hle
    have hlt : x1 < e + 2 := by
      apply (Nat.mul_lt_mul_left hn).mp
      rw [Nat.mul_add, Nat.mul_comm n 2]
      exact hupper.trans_le (Nat.add_le_add_right ((admissible he).mp hle) _)
    rw [Nat.odd_iff] at hx hodd
    omega

end MathlibExt.NumberTheory.OddGreedyExpansionWanted
