/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Ring

/-!
# Non-intersecting pairs of words

The number of pairs of nonempty words with disjoint alphabets is expressed using Stirling
numbers of the second kind and coefficients of rational generating functions.

## References

* Aubrey Blecher and Arnold Knopfmacher, [*Intersections in Pairs of Words*][bk2024],
  INTEGERS 24 (2024), Article A107, pp. 1–12, Theorem 1 and Corollaries 1–2.

[bk2024]: https://math.colgate.edu/~integers/y107/y107.pdf
-/

open Finset PowerSeries

namespace MetaMathlibExt

namespace WordPairIntersections

/-- Each position of a word avoiding `s` can take any letter in its complement. -/
private theorem count_avoiding {k : ℕ} (n : ℕ) (s : Finset (Fin k)) :
    (∑ u : Fin n → Fin k, if Disjoint (univ.image u) s then 1 else 0) = sᶜ.card ^ n := by
  simp only [sum_boole, Nat.cast_id]
  rw [← Fintype.card_piFinset_const sᶜ n]
  congr 1
  ext u
  simp [← subset_compl_iff_disjoint_right, image_subset_iff]

/-- Count a word and a disjoint set of `j` letters in either order. -/
private theorem sum_choose_unused (k r j : ℕ) :
    (∑ v : Fin r → Fin k, ((univ.image v)ᶜ.card).choose j) =
      k.choose j * (k - j) ^ r := by
  let sets := (univ : Finset (Fin k)).powersetCard j
  have choices (v : Fin r → Fin k) :
      ((univ.image v)ᶜ.card).choose j =
        ∑ s ∈ sets, if Disjoint (univ.image v) s then 1 else 0 := by
    rw [sum_boole, ← card_powersetCard]
    congr 1
    ext s
    simp [sets, ← subset_compl_iff_disjoint_left, and_comm]
  simp_rw [choices]
  rw [sum_comm]
  calc
    _ = ∑ _s ∈ sets, (k - j) ^ r := by
      refine sum_congr rfl fun s hs => ?_
      rw [count_avoiding, card_compl, Fintype.card_fin, (mem_powersetCard.mp hs).2]
    _ = _ := by simp [sets]

/-- Expand the choices for the first word in falling factorials of the unused alphabet size. -/
private theorem count_pairs (k n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ((univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p =>
      Disjoint (univ.image p.1) (univ.image p.2)).card =
        ∑ j ∈ Icc 1 (k - 1), k.choose j * j.factorial * n.stirlingSecond j * (k - j) ^ r := by
  let term (j : ℕ) := k.choose j * j.factorial * n.stirlingSecond j * (k - j) ^ r
  calc
    _ = ∑ v : Fin r → Fin k, (univ.image v)ᶜ.card ^ n := by
      rw [← Nat.cast_id ((univ.filter _).card), natCast_card_filter,
        Fintype.sum_prod_type_right]
      exact sum_congr rfl fun v _ => count_avoiding n (univ.image v)
    _ = ∑ v : Fin r → Fin k, ∑ j ∈ range (n + 1),
          n.stirlingSecond j * j.factorial * ((univ.image v)ᶜ.card).choose j := by
      simp_rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial,
        Nat.descFactorial_eq_factorial_mul_choose, mul_assoc]
    _ = ∑ j ∈ range (n + 1), term j := by
      rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      rw [← mul_sum, sum_choose_unused]
      dsimp [term]
      ac_rfl
    _ = ∑ j ∈ Icc 1 (k - 1), term j := by
      apply sum_congr_of_eq_on_inter
      · intro j _ hj
        simp only [mem_Icc, not_and] at hj
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
          simp [term]
        · have hsub : k - j = 0 := by specialize hj hjpos; omega
          simp [term, hsub, zero_pow (by omega : r ≠ 0)]
      · intro j _ hj
        have hlt : n < j := by simpa using hj
        simp [term, Nat.stirlingSecond_eq_zero_of_lt hlt]
      · intros
        rfl

private noncomputable def column (j : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (n.stirlingSecond j : ℚ)

private theorem column_step (j : ℕ) :
    column (j + 1) * (1 - ((j + 1 : ℕ) : ℚ⟦X⟧) * X) = column j * X := by
  rw [mul_sub, mul_one, ← mul_assoc]
  ext (_ | n)
  · simp [column]
  · rw [map_sub, coeff_succ_mul_X, coeff_succ_mul_X, coeff_mul_natCast]
    simp only [column, coeff_mk, Nat.stirlingSecond_succ_succ, Nat.cast_add, Nat.cast_mul]
    ring

/-- Multiplying the column generating function by its denominator clears one factor per step. -/
private theorem column_mul_prod (j : ℕ) :
    column j * (∏ i ∈ Icc 1 j, (1 - (i : ℚ⟦X⟧) * X)) = X ^ j := by
  induction j with
  | zero =>
    simp only [Icc_eq_empty_of_lt (by decide : 0 < 1), prod_empty, mul_one, pow_zero]
    ext (_ | n) <;> simp [column]
  | succ j ih =>
    rw [prod_Icc_succ_top (by omega : 1 ≤ j + 1), ← mul_assoc, mul_right_comm,
      column_step, mul_right_comm, ih, pow_succ]

private theorem coeff_stirling_factor (j n : ℕ) :
    coeff n ((j.factorial : ℚ⟦X⟧) * X ^ j * (∏ i ∈ Icc 1 j, (1 - (i : ℚ⟦X⟧) * X))⁻¹) =
      (j.factorial : ℚ) * n.stirlingSecond j := by
  have h : column j = X ^ j * (∏ i ∈ Icc 1 j, (1 - (i : ℚ⟦X⟧) * X))⁻¹ :=
    (eq_mul_inv_iff_mul_eq (by simp)).2 (column_mul_prod j)
  rw [mul_assoc, ← h, coeff_natCast_mul, column, coeff_mk]

private theorem coeff_geometric_factor (a r : ℕ) (hr : 1 ≤ r) :
    coeff r ((a : ℚ⟦X⟧) * X * (1 - (a : ℚ⟦X⟧) * X)⁻¹) = (a : ℚ) ^ r := by
  have h : (1 - (a : ℚ⟦X⟧) * X)⁻¹ = PowerSeries.mk (fun n => (a : ℚ) ^ n) := by
    apply (inv_eq_iff_mul_eq_one (by simp)).2
    rw [mul_sub, mul_one, ← mul_assoc]
    ext (_ | n)
    · simp
    · simp [coeff_succ_mul_X, pow_succ]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  rw [h, mul_right_comm, coeff_succ_mul_X, coeff_natCast_mul, coeff_mk, pow_succ']

end WordPairIntersections

open WordPairIntersections

/-- **Non-intersecting pairs of words.** Fix natural numbers $k$, $n \ge 1$ and $r \ge 1$, and call
a pair of words over an alphabet of $k$ letters non-intersecting when no letter occurs in both.
Write $[x^m] F$ for the coefficient of $x^m$ in a formal power series $F$ over $\mathbb{Q}$ and
$S(m, j)$ for the Stirling numbers of the second kind. Let $N$ be the number of non-intersecting
pairs $(u, v)$ with $u$ of length $n$ and $v$ of length $r$. Then
$N = \sum_{j=1}^{k-1} \binom{k}{j} \,
[x^n]\Bigl(j! \, x^j \bigl(\prod_{i=1}^{j} (1 - i x)\bigr)^{-1}\Bigr) \,
[x^r]\bigl((k-j) x \, (1 - (k-j) x)^{-1}\bigr)$
and
$N = \sum_{j=1}^{k-1} \binom{k}{j} \, j! \, S(n, j) \,
[x^r]\bigl((k-j) x \, (1 - (k-j) x)^{-1}\bigr)$.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24
(2024), Article A107, Theorem 1 (`integers-2024-A107-thm-1`). -/
public theorem nonIntersectingWordPairs_card_eq_coeff (k n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (((Finset.univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p =>
        Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ) =
        ∑ j ∈ Finset.Icc 1 (k - 1), (k.choose j : ℚ) *
          coeff n ((j.factorial : ℚ⟦X⟧) * X ^ j * (∏ i ∈ Finset.Icc 1 j, (1 - (i : ℚ⟦X⟧) * X))⁻¹) *
          coeff r (((k - j : ℕ) : ℚ⟦X⟧) * X * (1 - ((k - j : ℕ) : ℚ⟦X⟧) * X)⁻¹) ∧
      (((Finset.univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p =>
        Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ) =
        ∑ j ∈ Finset.Icc 1 (k - 1), (k.choose j : ℚ) * j.factorial * Nat.stirlingSecond n j *
          coeff r (((k - j : ℕ) : ℚ⟦X⟧) * X * (1 - ((k - j : ℕ) : ℚ⟦X⟧) * X)⁻¹) := by
  simp_rw [coeff_stirling_factor, coeff_geometric_factor _ _ hr, ← mul_assoc]
  constructor <;> exact_mod_cast count_pairs k n r hn hr

/-- **Non-intersecting pairs of words of equal length.**
Let $S(n, j)$ denote the Stirling numbers of the second kind.
For natural numbers $k$ and $n \ge 1$, the number of pairs $(u, v)$ of words
of length $n$ over an alphabet of $k$ letters such that no letter occurs in both $u$ and $v$ is
$\sum_{j=1}^{k-1} \binom{k}{j} \, j! \, S(n, j) \, (k-j)^n$.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24
(2024), Article A107, Corollary 2 (`integers-2024-A107-cor-2`). -/
public theorem nonIntersectingWordPairs_sameLength_card (k n : ℕ) (hn : 1 ≤ n) :
    ((Finset.univ : Finset ((Fin n → Fin k) × (Fin n → Fin k))).filter fun p =>
      Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card =
      ∑ j ∈ Finset.Icc 1 (k - 1), k.choose j * j.factorial * Nat.stirlingSecond n j * (k - j) ^ n :=
  count_pairs k n n hn hn

/-- **Generating function of non-intersecting pairs of words of equal length.** Let $k$ be a
natural number, let $S(n, j)$ denote the Stirling numbers of the second kind, and for $n \ge 1$ let
$h(n)$ be the number of pairs $(u, v)$ of words of length $n$ over an alphabet of $k$ letters such
that no letter occurs in both. Then, as formal power series over $\mathbb{Q}$,
$\sum_{n \ge 1} h(n) x^n = \sum_{n \ge 0} \sum_{j=1}^{k-1} \binom{k}{j} \, j! \, S(n, j) \,
(k-j)^n x^n$.

The constant term on the right is $0$ because $S(0, j) = 0$ for $j \ge 1$: the empty pair is not
counted.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24
(2024), Article A107, Corollary 1 (`integers-2024-A107-cor-1`). -/
public theorem nonIntersectingWordPairs_sameLength_generatingFunction (k : ℕ) :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else
        (((Finset.univ : Finset ((Fin n → Fin k) × (Fin n → Fin k))).filter fun p =>
          Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ)) =
      PowerSeries.mk fun n => ∑ j ∈ Finset.Icc 1 (k - 1),
        (k.choose j : ℚ) * j.factorial * Nat.stirlingSecond n j * ((k - j : ℕ) : ℚ) ^ n := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_mk]
  cases n with
  | zero =>
    change (0 : ℚ) = _
    symm
    apply Finset.sum_eq_zero
    intro j hj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Finset.mem_Icc.mp hj).1)
    simp [Nat.stirlingSecond_zero_succ]
  | succ n =>
    rw [ite_eq_right (Nat.succ_ne_zero n)]
    exact_mod_cast nonIntersectingWordPairs_sameLength_card k (n + 1) (Nat.succ_pos n)

end MetaMathlibExt
