/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.SecondOrderGenValueTrivialFamilies
public import MathlibExt.NumberTheory.SecondOrderMValue
import Mathlib.Data.Int.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.SecondOrderGenValueNeighbors

/-!
# A small value of `M` along a family when `a b p + a ^ 2 - b ^ 2 ≥ 0`

For integers `a`, `b`, `p` with `p ≠ 0`, let `A(x) = (a (1 - p x) + b x) / (1 - p x - x ^ 2)` be
the generating function of the sequence with `A_0 = a`, `A_1 = b` and `A_{n+1} = p A_n + A_{n-1}`,
and let `M(u, v) = (b u ^ 2 + b v ^ 2 - a p u ^ 2 + 2 a u v) / (v ^ 2 - p u v - u ^ 2)`. The main
result, `MetaMathlibExt.exists_small_secondOrderMValue_of_nonneg`, states the following. Suppose
that `a b p + a ^ 2 - b ^ 2 ≥ 0`, that `r` and `s ≠ 0` are coprime integers with `A(r / s)` an
integer, and that no term of the two-sided sequence `A^{(r,s)}` with `A^{(r,s)}_0 = r`,
`A^{(r,s)}_1 = s` and `A^{(r,s)}_{n+1} = p A^{(r,s)}_n + A^{(r,s)}_{n-1}` vanishes. Then some value
`M(A^{(r,s)}_n, A^{(r,s)}_{n+1})` has absolute value at most
`√((a b p ^ 3 + (a ^ 2 - b ^ 2) p ^ 2) / (p ^ 2 + 4))`. The declaration's docstring cites the
source of the statement, a paper of Luu Ba Thang and Nguyen Duy Nguyen in the Journal of Integer
Sequences (2025).

## Proof

Write `M_n = M(A_n, A_{n+1})` and
`E = a b p ^ 3 + (a ^ 2 - b ^ 2) p ^ 2 = p ^ 2 (a b p + a ^ 2 - b ^ 2)`. If `A(u / v) = k` is an
integer, then `M(u, v) ^ 2 = (k p + b - a p) ^ 2 - 4 k (a - k)`, so the rational number `M(u, v)`
is an integer. This gives `M_0, M_1 ∈ ℤ`, using the integer value `A(s / (r + p s))` at the
neighbouring fraction, and the relation `M_{n-1} + (p ^ 2 + 2) M_n + M_{n+1} = 0` spreads
integrality to every `M_n`. Take `n` with `|M_n|` least. The invariant
`M_n ^ 2 + (p ^ 2 + 2) M_n M_{n+1} + M_{n+1} ^ 2 = E` gives `E ≥ (p ^ 2 + 4) M_n ^ 2` when
`M_n M_{n+1} ≥ 0` or `M_{n-1} M_n ≥ 0`. Otherwise both neighbours have the sign opposite to `M_n`,
and `|M_n| ≤ |M_{n±1}|` together with the linear relation forces `E ≤ -p ^ 2 M_n ^ 2 < 0`.
-/

namespace MetaMathlibExt

namespace exists_small_secondOrderMValue_of_nonneg

/-- A rational number whose square is an integer is an integer. -/
private theorem exists_intCast_eq_of_sq_eq {x : ℚ} {n : ℤ} (h : x ^ 2 = n) :
    ∃ z : ℤ, x = z := by
  have hden : x.den = 1 := by
    have := congrArg Rat.den h
    rw [Rat.den_pow, Rat.den_intCast] at this
    simpa using this
  exact ⟨x.num, (Rat.intCast_num_of_den_eq_one hden).symm⟩

/-- If the generating function takes an integer value `k` at `u / v`, then
`M(u, v) ^ 2 = (k p + b - a p) ^ 2 - 4 k (a - k)`, so `M(u, v)` is an integer. -/
private theorem exists_mValue_eq_intCast {a b p u v : ℤ} (hv : v ≠ 0)
    (h : ∃ z : ℤ, secondOrderGenValue a b p ((u : ℚ) / v) = z) :
    ∃ z : ℤ, secondOrderMValue a b p u v = z := by
  obtain ⟨k, hk⟩ := h
  have hvq : (v : ℚ) ≠ 0 := by exact_mod_cast hv
  -- With a zero denominator, `M(u, v)` is `0` by convention.
  by_cases hD : (v : ℚ) ^ 2 - p * u * v - u ^ 2 = 0
  · exact ⟨0, by simp [secondOrderMValue, hD]⟩
  have hδ : 1 - p * ((u : ℚ) / v) - ((u : ℚ) / v) ^ 2 ≠ 0 := by
    rw [show 1 - p * ((u : ℚ) / v) - ((u : ℚ) / v) ^ 2 =
      ((v : ℚ) ^ 2 - p * u * v - u ^ 2) / v ^ 2 by field_simp]
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

/-- Let `μ` be an integer sequence with `μ (n - 1) + q μ n + μ (n + 1) = 0` and
`μ n ^ 2 + q μ n μ (n + 1) + μ (n + 1) ^ 2 = E` for all `n`, where `q > 2` and `E ≥ 0`. Then a
term of least absolute value satisfies `(q + 2) μ n ^ 2 ≤ E`. -/
private theorem exists_sq_le {q E : ℤ} (hq : 2 < q) (hE : 0 ≤ E) (μ : ℤ → ℤ)
    (hlin : ∀ n, μ (n - 1) + q * μ n + μ (n + 1) = 0)
    (hquad : ∀ n, μ n ^ 2 + q * μ n * μ (n + 1) + μ (n + 1) ^ 2 = E) :
    ∃ n, (q + 2) * μ n ^ 2 ≤ E := by
  classical
  have hex : ∃ k : ℕ, ∃ n : ℤ, (μ n).natAbs = k := ⟨_, 0, rfl⟩
  obtain ⟨n, hn⟩ := Nat.find_spec hex
  have hmin (m : ℤ) : μ n ^ 2 ≤ μ m ^ 2 :=
    Int.natAbs_le_iff_sq_le.mp (hn ▸ Nat.find_min' hex ⟨m, rfl⟩)
  refine ⟨n, ?_⟩
  have h1 : μ (n - 1) + q * μ n + μ (n + 1) = 0 := hlin n
  have h2 : μ n ^ 2 + q * μ n * μ (n + 1) + μ (n + 1) ^ 2 = E := hquad n
  have h3 : μ (n - 1) ^ 2 + q * μ (n - 1) * μ n + μ n ^ 2 = E := by
    simpa using hquad (n - 1)
  have hy := hmin (n + 1)
  have hz := hmin (n - 1)
  generalize μ n = x at *
  generalize μ (n + 1) = y at *
  generalize μ (n - 1) = z at *
  -- A neighbour with the sign of `x` (or a zero product) gives the bound directly.
  rcases le_or_gt 0 (x * y) with hxy | hxy
  · have hle : x ^ 2 ≤ x * y := by
      calc x ^ 2 = |x| * |x| := by rw [abs_mul_abs_self, sq]
        _ ≤ |x| * |y| := mul_le_mul_of_nonneg_left (sq_le_sq.mp hy) (abs_nonneg x)
        _ = x * y := by rw [← abs_mul, abs_of_nonneg hxy]
    nlinarith [mul_le_mul_of_nonneg_left hle (show (0 : ℤ) ≤ q by omega)]
  rcases le_or_gt 0 (z * x) with hzx | hzx
  · have hle : x ^ 2 ≤ z * x := by
      calc x ^ 2 = |x| * |x| := by rw [abs_mul_abs_self, sq]
        _ ≤ |z| * |x| := mul_le_mul_of_nonneg_right (sq_le_sq.mp hz) (abs_nonneg x)
        _ = z * x := by rw [← abs_mul, abs_of_nonneg hzx]
    nlinarith [mul_le_mul_of_nonneg_left hle (show (0 : ℤ) ≤ q by omega)]
  -- Both neighbours have the sign opposite to `x`: then `E < 0`.
  exfalso
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
  have hE' : 0 ≤ x ^ 2 + q * x * y + y ^ 2 := h2 ▸ hE
  have hA : x * y + x ^ 2 ≤ 0 := by linarith
  have hB : 0 ≤ x * y + (q - 1) * x ^ 2 := by
    have hz' : z = -(q * x) - y := by linarith
    subst hz'
    nlinarith
  have hx2 : 0 < x ^ 2 := by positivity
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hA hB, mul_nonneg hE' hx2.le,
    mul_pos (show (0 : ℤ) < q - 2 by omega) (pow_pos hx2 2)]

end exists_small_secondOrderMValue_of_nonneg

open exists_small_secondOrderMValue_of_nonneg in
/-- **A small value of $M$ in the family of $r/s$ when $abp + a^2 - b^2 \ge 0$.** Let $a, b, p$
be integers with $p \ne 0$ and $abp + a^2 - b^2 \ge 0$. Let
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ for rational $x$, and for integers $u, v$ let
$M(u, v) = \frac{bu^2 + bv^2 - apu^2 + 2auv}{v^2 - puv - u^2}$, where in both a fraction with
denominator $0$ is read as $0$. Let $r, s$ be coprime integers with $s \ne 0$ such that $A(r/s)$
is an integer, and let $(A^{(r,s)}_n)_{n \in \mathbb{Z}}$ be the two-sided sequence with
$A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and $A^{(r,s)}_{n+1} = pA^{(r,s)}_n + A^{(r,s)}_{n-1}$ for
every integer $n$. If $A^{(r,s)}_n \ne 0$ for every integer $n$, then there is an integer $n$
with $|M(A^{(r,s)}_n, A^{(r,s)}_{n+1})| \le \sqrt{(abp^3 + (a^2 - b^2)p^2)/(p^2 + 4)}$.

The hypothesis that no term vanishes is the paper's assumption before Lemma 8. Without it the
paper's claim fails: for $(a, b, p) = (-3, -8, 5)$ and $x = 0$, the members $A_n/A_{n+1}$ of the
family $A^{(0,1)}$ with $A_{n+1} \ne 0$ have $\min |M| = 8$, while
$(abp^3 + (a^2 - b^2)p^2)/(p^2 + 4) = 1625/29 < 64$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 10 (`jis-2025-25.8.3-lem-10`). -/
public theorem exists_small_secondOrderMValue_of_nonneg (a b p : ℤ) (hp : p ≠ 0)
    (hnonneg : 0 ≤ a * b * p + a ^ 2 - b ^ 2) (r s : ℤ) (hs : s ≠ 0) (hrs : Int.gcd r s = 1)
    (hint : ∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z)
    (hnz : ∀ n : ℤ, secondOrderBiSeq p r s n ≠ 0) :
    ∃ n : ℤ, |(secondOrderMValue a b p (secondOrderBiSeq p r s n)
        (secondOrderBiSeq p r s (n + 1)) : ℝ)| ≤
      √(((a * b * p ^ 3 + (a ^ 2 - b ^ 2) * p ^ 2 : ℤ) : ℝ) / (p ^ 2 + 4)) := by
  set A := secondOrderBiSeq p r s
  have hrec (n : ℤ) : A (n + 2) = p * A (n + 1) + A n := secondOrderBiSeq_add_two p r s n
  have hprev (n : ℤ) : A (n + 1) - p * A n = A (n - 1) := by
    have h := hrec (n - 1)
    rw [show n - 1 + 2 = n + 1 by ring, sub_add_cancel] at h
    linarith
  have hnext (n : ℤ) : A n + p * A (n + 1) = A (n + 1 + 1) := by
    rw [add_assoc, one_add_one_eq_two, hrec]
    ring
  -- The relations between neighbouring values of `M` hold along the whole family.
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
  -- `M` is an integer at `(r, s)` and at `(s, p s + r)`, hence everywhere along the family.
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
  -- Descent on `|M_n|` gives `(p ^ 2 + 4) M_n ^ 2 ≤ E` for some `n`.
  have hp2 : 0 < p ^ 2 := by positivity
  have hE : 0 ≤ a * b * p ^ 3 + (a ^ 2 - b ^ 2) * p ^ 2 := by
    rw [show a * b * p ^ 3 + (a ^ 2 - b ^ 2) * p ^ 2 =
      p ^ 2 * (a * b * p + a ^ 2 - b ^ 2) by ring]
    exact mul_nonneg hp2.le hnonneg
  obtain ⟨n, hn⟩ := exists_sq_le (by omega) hE μ hμlin hμquad
  refine ⟨n, Real.abs_le_sqrt ?_⟩
  rw [hμ n, le_div_iff₀ (by positivity)]
  have h := (Int.cast_le (R := ℝ)).mpr hn
  push_cast at h ⊢
  linarith

end MetaMathlibExt
