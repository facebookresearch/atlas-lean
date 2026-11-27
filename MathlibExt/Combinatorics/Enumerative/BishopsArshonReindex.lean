/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.NonattackingBishopsAnassas
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Arshon's formula for nonattacking bishops

We prove Santos's formula (Theorem 3) for arbitrary board size $m$ and bishop count $k$ by
reindexing the two color sums in `bishopsSquare_eq_sum` and using the support of the extended
Stirling numbers. The specialization $k = m$ recovers Kotěšovec's refinement of Arshon's count.

## References

* Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
  Journal of Integer Sequences 28 (2025), Article 25.8.6, pp. 1–19, Theorem 3 and §2,
  <https://cs.uwaterloo.ca/journals/JIS/VOL28/Santos/santos3.html>.
* S. E. Arshon, *Reshenie odnoĭ kombinatornoĭ zadachi*, Matematicheskoe Prosveshchenie
  8 (1936), pp. 24–29, <https://www.mathnet.ru/eng/mp694>. This is the original count.
* Václav Kotěšovec, *Non-Attacking Chess Pieces (Chess and Mathematics)*, 6th edition
  (2013), pp. 242–248. Page 248 gives the $k = m$ case, counting $m$ bishops on an $m \times m$
  board.
-/

namespace MetaMathlibExt

open Finset

private theorem sum_range_eq_of_zero {f : ℕ → ℕ} {a b : ℕ}
    (hab : ∀ i, a ≤ i → i < b → f i = 0) (hba : ∀ i, b ≤ i → i < a → f i = 0) :
    (∑ i ∈ range a, f i) = ∑ i ∈ range b, f i := by
  rcases le_total a b with h | h
  · exact sum_subset (range_mono h) fun i hi hia =>
      hab i (Nat.le_of_not_gt fun hlt => hia (mem_range.mpr hlt)) (mem_range.mp hi)
  · exact (sum_subset (range_mono h) fun i hi hib =>
      hba i (Nat.le_of_not_gt fun hlt => hib (mem_range.mpr hlt)) (mem_range.mp hi)).symm

private theorem extStirlingSecond_eq_zero_of_lt {n : ℕ} {d : ℤ} (h : (n : ℤ) < d) :
    extStirlingSecond n d = 0 := by
  have hd : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (by omega)
  rw [← hd, extStirlingSecond_natCast]
  exact Nat.stirlingSecond_eq_zero_of_lt (by omega)

private def arshonColorSum (a b : ℕ) (d : ℤ) : ℕ :=
  ∑ i ∈ range (a + 1), a.choose i * extStirlingSecond (i + b : ℕ) d

private theorem arshonColorSum_eq_zero (a b : ℕ) (d : ℤ)
    (h : d < 0 ∨ (a : ℤ) + b < d) : arshonColorSum a b d = 0 := by
  unfold arshonColorSum
  refine sum_eq_zero fun i hi => ?_
  have hi' := mem_range.mp hi
  rcases h with h | h
  · simp [extStirlingSecond, not_le.mpr h, show ¬ (i : ℤ) + b < 0 by omega]
  · rw [extStirlingSecond_eq_zero_of_lt (by omega), mul_zero]

-- The Stirling factor cuts the original sum off at s; the binomial factor cuts it off at a.
private theorem sum_choose_stirling_eq_arshonColorSum (m a b s : ℕ) (hab : a + b = m) :
    (∑ i ∈ range (s + 1), a.choose i * extStirlingSecond ((m : ℤ) - i) ((m : ℤ) - s)) =
      arshonColorSum a b ((m : ℤ) - s) := by
  calc
    _ = ∑ i ∈ range (a + 1), a.choose i * extStirlingSecond ((m : ℤ) - i) ((m : ℤ) - s) := by
      apply sum_range_eq_of_zero
      · intro i hs hi
        rw [show (m : ℤ) - i = (↑(m - i : ℕ) : ℤ) by omega,
          extStirlingSecond_eq_zero_of_lt (by omega), mul_zero]
      · intro i ha _
        rw [Nat.choose_eq_zero_of_lt (by omega : a < i), zero_mul]
    _ = ∑ i ∈ range (a + 1), a.choose (a - i) *
          extStirlingSecond ((m : ℤ) - (↑(a - i : ℕ) : ℤ)) ((m : ℤ) - s) := by
      simpa only [Nat.add_sub_cancel] using
        (sum_range_reflect (fun i => a.choose i *
          extStirlingSecond ((m : ℤ) - i) ((m : ℤ) - s)) (a + 1)).symm
    _ = _ := by
      unfold arshonColorSum
      refine sum_congr rfl fun i hi => ?_
      have hi' := mem_range.mp hi
      rw [Nat.choose_symm (by omega : i ≤ a),
        show (m : ℤ) - (↑(a - i : ℕ) : ℤ) = (↑(i + b : ℕ) : ℤ) by omega]

/-- **Arshon's formula for nonattacking bishops (Kotěšovec's form).** For all natural numbers $m$
and $k$, the number $B_S(m, k)$ of placements of $k$ nonattacking bishops on the $m \times m$
board satisfies

$$
B_S(m, k) = \sum_{j=0}^{m} \sum_{i=0}^{\lfloor (m+1)/2 \rfloor}
\binom{\lfloor (m+1)/2 \rfloor}{i} S\bigl(i + \lfloor m/2 \rfloor, m - j\bigr)
\sum_{l=0}^{\lfloor m/2 \rfloor} \binom{\lfloor m/2 \rfloor}{l}
S\bigl(l + \lfloor (m+1)/2 \rfloor, m - k + j\bigr),
$$

where, for integers $a \ge 0$ and $b$, $S(a, b)$ is the Stirling number of the second kind when
$b \ge 0$ and $0$ when $b < 0$ (Knuth's extended Stirling numbers of the second kind).

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 3 (Arshon, Kotěšovec)
(`jis-2025-25.8.6-thm-3`). -/
public theorem bishopsSquare_eq_arshon (m k : ℕ) :
    bishopsSquare m k =
      ∑ j ∈ range (m + 1), ∑ i ∈ range ((m + 1) / 2 + 1),
        ((m + 1) / 2).choose i * extStirlingSecond (i + m / 2 : ℕ) ((m : ℤ) - j) *
          ∑ l ∈ range (m / 2 + 1),
            (m / 2).choose l * extStirlingSecond (l + (m + 1) / 2 : ℕ) ((m : ℤ) - k + j) := by
  let a := m / 2
  let b := (m + 1) / 2
  have hab : a + b = m := by dsimp [a, b]; omega
  rw [bishopsSquare_eq_sum]
  calc
    _ = ∑ j ∈ range (k + 1), arshonColorSum a b ((m : ℤ) - j) *
          arshonColorSum b a ((m : ℤ) - k + j) := by
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.mp hj
      rw [← sum_mul, sum_choose_stirling_eq_arshonColorSum m a b j hab,
        ← show (m : ℤ) - (↑(k - j : ℕ) : ℤ) = (m : ℤ) - k + j by omega,
        sum_choose_stirling_eq_arshonColorSum m b a (k - j) (by omega)]
    -- Reflect the split of k bishops so the white-board count comes first.
    _ = ∑ j ∈ range (k + 1), arshonColorSum b a ((m : ℤ) - j) *
          arshonColorSum a b ((m : ℤ) - k + j) := by
      conv_lhs =>
        rw [← sum_range_reflect]
      simp only [Nat.add_sub_cancel]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.mp hj
      rw [show (m : ℤ) - (↑(k - j : ℕ) : ℤ) = (m : ℤ) - k + j by omega,
        show (m : ℤ) - k + (↑(k - j : ℕ) : ℤ) = (m : ℤ) - j by omega,
        Nat.mul_comm]
    -- For j > k the black factor is above its support; for j > m the white factor is negative.
    _ = ∑ j ∈ range (m + 1), arshonColorSum b a ((m : ℤ) - j) *
          arshonColorSum a b ((m : ℤ) - k + j) := by
      apply sum_range_eq_of_zero
      · intro j hkj _
        rw [arshonColorSum_eq_zero a b _ (Or.inr (by omega)), mul_zero]
      · intro j hmj _
        rw [arshonColorSum_eq_zero b a _ (Or.inl (by omega)), zero_mul]
    _ = _ := by simp only [arshonColorSum, sum_mul, a, b]

end MetaMathlibExt
