/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Int.ModEq
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.SecondOrderGenValueNeighbors
public import MathlibExt.NumberTheory.SecondOrderGenValueTrivialFamilies
public import MathlibExt.NumberTheory.SecondOrderMValue
public import MathlibExt.NumberTheory.SecondOrderMValueSmallNonneg
import Mathlib.Data.Int.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A small value of `M` when `a b p + a ^ 2 - b ^ 2 < 0`

For `p ≠ 0`, this module proves that some value of `secondOrderMValue` along a nonvanishing
two-sided family has absolute value at most `√(b ^ 2 - a ^ 2 - a b p)` when
`a b p + a ^ 2 - b ^ 2 < 0` and the initial reduced fraction gives an integer value of
`secondOrderGenValue`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a
Type of Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 9 (`jis-2025-25.8.3-lem-9`).
-/

namespace MetaMathlibExt

/-- A rational number whose square is an integer is an integer. -/
private theorem exists_intCast_eq_of_sq_eq {x : ℚ} {n : ℤ} (h : x ^ 2 = n) :
    ∃ z : ℤ, x = z := by
  have hden : x.den = 1 := by
    have := congrArg Rat.den h
    rw [Rat.den_pow, Rat.den_intCast] at this
    simpa using this
  exact ⟨x.num, (Rat.intCast_num_of_den_eq_one hden).symm⟩

/-- An integer value of the generating function at `u / v` makes `M(u, v)` an integer. -/
private theorem exists_mValue_eq_intCast {a b p u v : ℤ} (hv : v ≠ 0)
    (h : ∃ z : ℤ, secondOrderGenValue a b p ((u : ℚ) / v) = z) :
    ∃ z : ℤ, secondOrderMValue a b p u v = z := by
  obtain ⟨k, hk⟩ := h
  have hvq : (v : ℚ) ≠ 0 := by exact_mod_cast hv
  by_cases hD : (v : ℚ) ^ 2 - p * u * v - u ^ 2 = 0
  · exact ⟨0, by simp [secondOrderMValue, hD]⟩
  have hδ : 1 - p * ((u : ℚ) / v) - ((u : ℚ) / v) ^ 2 ≠ 0 := by
    have heq : 1 - p * ((u : ℚ) / v) - ((u : ℚ) / v) ^ 2 =
        ((v : ℚ) ^ 2 - p * u * v - u ^ 2) / v ^ 2 := by field_simp
    rw [heq]
    exact div_ne_zero hD (pow_ne_zero 2 hvq)
  have hval : secondOrderGenValue a b p ((u : ℚ) / v) =
      v * (a * v - a * p * u + b * u) / (v ^ 2 - p * u * v - u ^ 2) := by
    unfold secondOrderGenValue
    rw [div_eq_div_iff hδ hD]
    field_simp
  apply exists_intCast_eq_of_sq_eq (n := (k * p + b - a * p) ^ 2 - 4 * k * (a - k))
  push_cast
  rw [← hk, hval]
  unfold secondOrderMValue
  generalize hDdef : (v : ℚ) ^ 2 - p * u * v - u ^ 2 = D at hD ⊢
  field_simp
  rw [← hDdef]
  ring

/-- An integer recurrence with negative quadratic invariant has a term satisfying
`(q - 2) * μ n ^ 2 ≤ -E`. -/
private theorem exists_sq_le {q E : ℤ} (hq : 2 < q) (hE : E < 0) (μ : ℤ → ℤ)
    (hlin : ∀ n, μ (n - 1) + q * μ n + μ (n + 1) = 0)
    (hquad : ∀ n, μ n ^ 2 + q * μ n * μ (n + 1) + μ (n + 1) ^ 2 = E) :
    ∃ n, (q - 2) * μ n ^ 2 ≤ -E := by
  classical
  have hex : ∃ k : ℕ, ∃ n : ℤ, (μ n).natAbs = k := ⟨_, 0, rfl⟩
  obtain ⟨n, hn⟩ := Nat.find_spec hex
  have hmin (m : ℤ) : μ n ^ 2 ≤ μ m ^ 2 :=
    Int.natAbs_le_iff_sq_le.mp (hn ▸ Nat.find_min' hex ⟨m, rfl⟩)
  refine ⟨n, ?_⟩
  have h1 := hlin n
  have h2 := hquad n
  have h3 : μ (n - 1) ^ 2 + q * μ (n - 1) * μ n + μ n ^ 2 = E := by
    simpa using hquad (n - 1)
  have hy := hmin (n + 1)
  have hz := hmin (n - 1)
  generalize μ n = x at *
  generalize μ (n + 1) = y at *
  generalize μ (n - 1) = z at *
  have hq0 : 0 ≤ q := by omega
  have hxy : x * y < 0 := by
    by_contra! h
    nlinarith [mul_nonneg hq0 h]
  have hzx : z * x < 0 := by
    by_contra! h
    nlinarith [mul_nonneg hq0 h]
  have hxy' : x * y ≤ -x ^ 2 := by
    calc x * y = -(|x| * |y|) := by rw [← abs_mul, abs_of_neg hxy, neg_neg]
      _ ≤ -(|x| * |x|) :=
        neg_le_neg (mul_le_mul_of_nonneg_left (sq_le_sq.mp hy) (abs_nonneg x))
      _ = -x ^ 2 := by rw [abs_mul_abs_self, sq]
  have hzx' : z * x ≤ -x ^ 2 := by
    calc z * x = -(|z| * |x|) := by rw [← abs_mul, abs_of_neg hzx, neg_neg]
      _ ≤ -(|x| * |x|) :=
        neg_le_neg (mul_le_mul_of_nonneg_right (sq_le_sq.mp hz) (abs_nonneg x))
      _ = -x ^ 2 := by rw [abs_mul_abs_self, sq]
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxy
  have hx2 : 0 < x ^ 2 := by positivity
  have hA : x * y + x ^ 2 ≤ 0 := by linarith
  have hB : 0 ≤ x * y + (q - 1) * x ^ 2 := by
    have hz' : z = -(q * x) - y := by linarith
    subst hz'
    nlinarith
  by_contra! hbad
  have hpos : 0 < (E + (q - 2) * x ^ 2) * x ^ 2 :=
    mul_pos (by linarith) hx2
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hA hB]

@[expose] public section

/-- **A small value of $M$ in the family of $r/s$ when $abp + a^2 - b^2 < 0$.** Let $a, b, p$ be
integers with $p \ne 0$ and $abp + a^2 - b^2 < 0$. Let $A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$
for rational $x$, and for integers $u, v$ let
$M(u, v) = \frac{bu^2 + bv^2 - apu^2 + 2auv}{v^2 - puv - u^2}$, where in both a fraction with
denominator $0$ is read as $0$. Let $r, s$ be coprime integers with $s \ne 0$ such that $A(r/s)$
is an integer, and let $(A^{(r,s)}_n)_{n \in \mathbb{Z}}$ be the two-sided sequence with
$A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and $A^{(r,s)}_{n+1} = pA^{(r,s)}_n + A^{(r,s)}_{n-1}$ for
every integer $n$. If $A^{(r,s)}_n \ne 0$ for every integer $n$, then there is an integer $n$
with $|M(A^{(r,s)}_n, A^{(r,s)}_{n+1})| \le \sqrt{b^2 - a^2 - abp}$.

The hypothesis that no term vanishes is the paper's assumption before Lemma 8 ("we can assume
that the conditions $r \ne 0, s \ne 0, r + ps \ne 0$ automatically hold"). Without it the paper's
claim fails: for $(a, b, p) = (-1, 8, -1)$ and $x = 0$, the members $A_n/A_{n+1}$ of the family
$A^{(0,1)}$ with $A_{n+1} \ne 0$ have $\min |M| = 8 > \sqrt{55}$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 9 (`jis-2025-25.8.3-lem-9`). -/
public theorem exists_small_secondOrderMValue_of_neg (a b p : ℤ) (hp : p ≠ 0)
    (hneg : a * b * p + a ^ 2 - b ^ 2 < 0) (r s : ℤ) (hs : s ≠ 0) (hrs : Int.gcd r s = 1)
    (hint : ∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z)
    (hnz : ∀ n : ℤ, secondOrderBiSeq p r s n ≠ 0) :
    ∃ n : ℤ, |(secondOrderMValue a b p (secondOrderBiSeq p r s n)
        (secondOrderBiSeq p r s (n + 1)) : ℝ)| ≤ √((-a * b * p - a ^ 2 + b ^ 2 : ℤ) : ℝ) := by
  set A := secondOrderBiSeq p r s
  have hrec (n : ℤ) : A (n + 2) = p * A (n + 1) + A n := secondOrderBiSeq_add_two p r s n
  have hprev (n : ℤ) : A (n + 1) - p * A n = A (n - 1) := by
    have h := hrec (n - 1)
    have heq : n - 1 + 2 = n + 1 := by ring
    rw [heq, sub_add_cancel] at h
    linarith
  have hnext (n : ℤ) : A n + p * A (n + 1) = A (n + 1 + 1) := by
    rw [add_assoc, one_add_one_eq_two, hrec]
    ring
  have hrel (n : ℤ) := secondOrderMValue_relations a b p hp (A n) (A (n + 1))
    (by simp [hnz n])
  have hlin (n : ℤ) : secondOrderMValue a b p (A (n - 1)) (A n) +
      (p ^ 2 + 2) * secondOrderMValue a b p (A n) (A (n + 1)) +
      secondOrderMValue a b p (A (n + 1)) (A (n + 1 + 1)) = 0 := by
    have h := (hrel n).1
    rwa [hprev, hnext] at h
  have hquad (n : ℤ) : secondOrderMValue a b p (A n) (A (n + 1)) ^ 2 +
      (p ^ 2 + 2) * secondOrderMValue a b p (A n) (A (n + 1)) *
        secondOrderMValue a b p (A (n + 1)) (A (n + 1 + 1)) +
      secondOrderMValue a b p (A (n + 1)) (A (n + 1 + 1)) ^ 2 =
        ((a * b * p ^ 3 + (a ^ 2 - b ^ 2) * p ^ 2 : ℤ) : ℚ) := by
    have h := (hrel n).2
    rw [hnext] at h
    push_cast
    exact h
  have hm0 : ∃ z : ℤ, secondOrderMValue a b p (A 0) (A (0 + 1)) = z :=
    exists_mValue_eq_intCast hs hint
  have hm1 : ∃ z : ℤ, secondOrderMValue a b p (A 1) (A (1 + 1)) = z := by
    have h2 : A (1 + 1) = p * s + r := rfl
    have hne : p * s + r ≠ 0 := h2 ▸ hnz (1 + 1)
    have hnb := (secondOrderGenValue_neighbors_integer a b p hp r s (hnz 0) hs
      (by rwa [add_comm]) hrs hint).1
    rw [h2]
    refine exists_mValue_eq_intCast hne ?_
    push_cast
    rwa [add_comm]
  have hint_all (n : ℤ) : ∃ z : ℤ, secondOrderMValue a b p (A n) (A (n + 1)) = z := by
    have key : (∃ z : ℤ, secondOrderMValue a b p (A n) (A (n + 1)) = z) ∧
        ∃ z : ℤ, secondOrderMValue a b p (A (n + 1)) (A (n + 1 + 1)) = z := by
      refine Int.inductionOn' n 0 ⟨hm0, hm1⟩ ?_ ?_
      · rintro k - ⟨⟨z₁, hz₁⟩, z₂, hz₂⟩
        refine ⟨⟨z₂, hz₂⟩, -(p ^ 2 + 2) * z₂ - z₁, ?_⟩
        have h := hlin (k + 1)
        rw [add_sub_cancel_right, hz₁, hz₂] at h
        push_cast
        linear_combination h
      · rintro k - ⟨⟨z₁, hz₁⟩, z₂, hz₂⟩
        rw [sub_add_cancel]
        refine ⟨⟨-(p ^ 2 + 2) * z₁ - z₂, ?_⟩, z₁, hz₁⟩
        have h := hlin k
        rw [hz₁, hz₂] at h
        push_cast
        linear_combination h
    exact key.1
  choose μ hμ using hint_all
  have hμlin (n : ℤ) : μ (n - 1) + (p ^ 2 + 2) * μ n + μ (n + 1) = 0 := by
    have h := hlin n
    have e := hμ (n - 1)
    rw [sub_add_cancel] at e
    rw [e, hμ n, hμ (n + 1)] at h
    exact_mod_cast h
  have hμquad (n : ℤ) : μ n ^ 2 + (p ^ 2 + 2) * μ n * μ (n + 1) + μ (n + 1) ^ 2 =
      a * b * p ^ 3 + (a ^ 2 - b ^ 2) * p ^ 2 := by
    have h := hquad n
    rw [hμ n, hμ (n + 1)] at h
    exact_mod_cast h
  have hp2 : 0 < p ^ 2 := by positivity
  have hE : a * b * p ^ 3 + (a ^ 2 - b ^ 2) * p ^ 2 < 0 := by
    have heq : a * b * p ^ 3 + (a ^ 2 - b ^ 2) * p ^ 2 =
        p ^ 2 * (a * b * p + a ^ 2 - b ^ 2) := by ring
    rw [heq]
    exact mul_neg_of_pos_of_neg hp2 hneg
  obtain ⟨n, hn⟩ := exists_sq_le (by omega) hE μ hμlin hμquad
  have hn' : p ^ 2 * μ n ^ 2 ≤ p ^ 2 * (-a * b * p - a ^ 2 + b ^ 2) := by
    convert hn using 1 <;> ring
  have hsmall := (mul_le_mul_iff_of_pos_left hp2).mp hn'
  refine ⟨n, Real.abs_le_sqrt ?_⟩
  rw [hμ n]
  have h := (Int.cast_le (R := ℝ)).mpr hsmall
  push_cast at h ⊢
  exact h

end

end MetaMathlibExt
