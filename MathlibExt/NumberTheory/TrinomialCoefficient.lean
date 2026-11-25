/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Ring

/-!
# Trinomial coefficients

The trinomial coefficient in row `n` and column `k` is the coefficient of `X ^ k` in
`(1 + X + X ^ 2) ^ n`. Consequently it is zero when `k > 2 * n`. Sun's generalized central
trinomial coefficient `T_n(b, c)` is the coefficient of `X ^ n` in `(X ^ 2 + b X + c) ^ n`.

Sources:

* Emanuele Munarini, *Shifting Property for Riordan, Sheffer and Connection Constants
  Matrices*, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Munarini/muna4.tex>.
* Wen-jin Woan, *The Lagrange Inversion Formula and Divisibility Properties*,
  <https://cs.uwaterloo.ca/journals/JIS/VOL10/Woan/woan655.tex>.
* Chahinaze Djadi and Hacène Belbachir, *Congruence Properties for the Delannoy Triangle
  Coefficients*, Journal of Integer Sequences 29 (2026), Article 26.5.2, Section 4.

JIS concept: `jis_sem_ad18425839072c449c4e8a69`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Trinomial coefficient.** For natural numbers $n$ and $k$, the trinomial coefficient in row
$n$ and column $k$ is the coefficient of $X^k$ in the polynomial $(1 + X + X^2)^n$. -/
noncomputable def trinomialCoefficient (n k : ℕ) : ℕ :=
  ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) ^ n).coeff k

/-- The trinomial coefficient `T(0, 0)` is `1`. -/
theorem trinomialCoefficient_zero_zero : trinomialCoefficient 0 0 = 1 := by
  simp [trinomialCoefficient]

/-- The trinomial coefficient `T(1, 1)` is `1`. -/
theorem trinomialCoefficient_one_one : trinomialCoefficient 1 1 = 1 := by
  unfold trinomialCoefficient
  simp [pow_one, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
    Polynomial.coeff_X_pow]

/-- **Absorption identity for trinomial coefficients.** Write $\binom{n}{k}_2$ for the
trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$. For natural numbers $n \ge 1$
and $k$, $\frac{k}{n} \binom{n}{k}_2 = \binom{n-1}{k-1}_2 + 2 \binom{n-1}{k-2}_2$, where a term
whose lower index is negative is read as $0$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Lemma 31 (`jis-2025-25.3.5-lem-31`). -/
public theorem trinomialCoefficient_absorption (n k : ℕ) (hn : 0 < n) :
    (k : ℚ) / n * trinomialCoefficient n k =
      (if 1 ≤ k then (trinomialCoefficient (n - 1) (k - 1) : ℚ) else 0) +
        2 * (if 2 ≤ k then (trinomialCoefficient (n - 1) (k - 2) : ℚ) else 0) :=
  open Polynomial in
  by
    let p : Polynomial ℕ := 1 + X + X ^ 2
    -- Multiplying the derivative by `X` lets us compare coefficients at `k`.
    have hderiv : X * derivative (p ^ n) =
        C n * (X * p ^ (n - 1) + C 2 * (X ^ 2 * p ^ (n - 1))) := by
      rw [derivative_pow, Nat.cast_id, show derivative p = 1 + C 2 * X by
        simp only [p, derivative_add, derivative_one, derivative_X, zero_add, derivative_X_sq]]
      ring
    have hcoeff : (X * derivative (p ^ n)).coeff k = k * (p ^ n).coeff k := by
      cases k with
      | zero => simp
      | succ k => simp [coeff_derivative, mul_comm]
    have hshift : (X * p ^ (n - 1)).coeff k =
        if 1 ≤ k then (p ^ (n - 1)).coeff (k - 1) else 0 := by
      simpa only [pow_one] using coeff_X_pow_mul' (p ^ (n - 1)) 1 k
    have hnat : k * trinomialCoefficient n k =
        n * ((if 1 ≤ k then trinomialCoefficient (n - 1) (k - 1) else 0) +
          2 * (if 2 ≤ k then trinomialCoefficient (n - 1) (k - 2) else 0)) := by
      change k * (p ^ n).coeff k = _
      rw [← hcoeff, hderiv, coeff_C_mul, coeff_add, coeff_C_mul, hshift, coeff_X_pow_mul']
      rfl
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [div_mul_eq_mul_div₀, div_eq_iff hnq, mul_comm _ (n : ℚ)]
    exact_mod_cast hnat

/-- **Roots-of-unity filter for trinomial coefficients.** Write $\binom{n}{k}_2$ for the trinomial
coefficient, the coefficient of $t^k$ in $(1 + t + t^2)^n$. Let $n$, $x$, $b$ be natural
numbers with $x < b$, let $z \ne 0$ be a complex number, and let $w = e^{2\pi i/b}$. Then

$$\sum_{k=0}^{\lfloor (2n - x)/b \rfloor} \binom{n}{x + bk}_2 z^{x + bk} =
\frac{z^n}{b} \sum_{j=1}^{b} w^{j(n - x)} \left(1 + z w^j + \frac{1}{z w^j}\right)^n,$$

where for $x > 2n$ the left side is $0$. The hypothesis $z \ne 0$ is implicit in the
paper's $(z w^j)^{-1}$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 9 (`jis-2025-25.3.5-thm-9`). -/
public theorem sum_trinomialCoefficient_arith_prog (n x b : ℕ) (hxb : x < b) (z : ℂ)
    (hz : z ≠ 0) :
    let w := Complex.exp (2 * Real.pi * Complex.I / b)
    ∑ k ∈ Finset.range ((2 * n - x) / b + 1), (trinomialCoefficient n (x + b * k) : ℂ) *
        z ^ (x + b * k) =
      z ^ n * (1 / b) * ∑ j ∈ Finset.Icc 1 b,
        w ^ ((j : ℤ) * ((n : ℤ) - x)) * (1 + z * w ^ j + (z * w ^ j)⁻¹) ^ n :=
  open Polynomial in
  by
    intro w
    have hb : 0 < b := Nat.zero_lt_of_lt hxb
    have hbC : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    have hw : IsPrimitiveRoot w b := Complex.isPrimitiveRoot_exp b hb.ne'
    have hw0 := hw.ne_zero hb.ne'
    let p : Polynomial ℕ := (1 + X + X ^ 2) ^ n
    have hdegree : p.natDegree ≤ 2 * n := by
      rw [Nat.mul_comm 2 n]
      apply natDegree_pow_le_of_le
      apply natDegree_add_le_of_degree_le
      · apply natDegree_add_le_of_degree_le <;> simp
      · simp
    have heval (t : ℂ) :
        ∑ i ∈ Finset.range (2 * n + 1), (trinomialCoefficient n i : ℂ) * t ^ i =
          (1 + t + t ^ 2) ^ n := by
      calc
        _ = p.eval₂ (Nat.castRingHom ℂ) t :=
          (eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hdegree) t).symm
        _ = _ := by simp only [p, eval₂_pow, eval₂_add, eval₂_one, eval₂_X]
    let c (i : ℕ) := (trinomialCoefficient n i : ℂ) * z ^ i
    -- Convert the Laurent expression to a polynomial evaluation times a phase.
    have hterm (j : ℕ) :
        z ^ n * (w ^ ((j : ℤ) * ((n : ℤ) - x)) * (1 + z * w ^ j + (z * w ^ j)⁻¹) ^ n) =
          ∑ i ∈ Finset.range (2 * n + 1), c i * (w ^ ((i : ℤ) - x)) ^ j := by
      let v := w ^ j
      have hv : v ≠ 0 := pow_ne_zero j hw0
      have hmul : z * v * (1 + z * v + (z * v)⁻¹) = 1 + z * v + (z * v) ^ 2 := by
        rw [mul_add, mul_inv_cancel₀ (mul_ne_zero hz hv)]
        ring
      rw [zpow_mul, zpow_natCast, zpow_sub₀ hv, zpow_natCast]
      calc
        _ = v ^ (-(x : ℤ)) * (z * v * (1 + z * v + (z * v)⁻¹)) ^ n := by
          simp only [zpow_neg, zpow_natCast, div_eq_mul_inv, mul_pow]
          ring
        _ = _ := by
          rw [hmul, ← heval, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hphase : v ^ (-(x : ℤ)) * v ^ i = (w ^ ((i : ℤ) - x)) ^ j := by
            rw [← zpow_natCast v i, ← zpow_add₀ hv]
            change (w ^ j) ^ (-(x : ℤ) + i) = _
            rw [← zpow_natCast w j, ← zpow_mul,
              ← zpow_natCast (w ^ ((i : ℤ) - x)) j, ← zpow_mul]
            congr 1
            ring
          rw [mul_pow, ← hphase]
          dsimp only [c]
          ring
    -- Summing the phases keeps exactly the indices congruent to `x` modulo `b`.
    have hsum (i : ℕ) : (∑ j ∈ Finset.Icc 1 b, (w ^ ((i : ℤ) - x)) ^ j) =
        if i % b = x then (b : ℂ) else 0 := by
      let r := w ^ ((i : ℤ) - x)
      have hrb : r ^ b = 1 := by
        change (w ^ ((i : ℤ) - x)) ^ b = 1
        rw [← zpow_natCast r b, ← zpow_mul, mul_comm, zpow_mul, hw.zpow_eq_one, one_zpow]
      have hr_iff : r = 1 ↔ i % b = x := by
        change w ^ ((i : ℤ) - x) = 1 ↔ _
        rw [hw.zpow_eq_one_iff_dvd, ← Nat.modEq_iff_dvd]
        simp [Nat.ModEq, Nat.mod_eq_of_lt hxb, eq_comm]
      change (∑ j ∈ Finset.Icc 1 b, r ^ j) = _
      by_cases hr : r = 1
      · simp [hr, hr_iff.mp hr]
      · rw [ite_eq_right (mt hr_iff.mpr hr), ← Finset.Ico_succ_right_eq_Icc]
        have hgeom := geom_sum_Ico_mul r (m := 1) (n := b + 1) (by omega)
        rw [pow_succ, hrb, one_mul, pow_one, sub_self] at hgeom
        exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hr)
    have hindices : (∑ k ∈ Finset.range ((2 * n - x) / b + 1), c (x + b * k)) =
        ∑ i ∈ (Finset.range (2 * n + 1)).filter (fun i => i % b = x), c i := by
      by_cases hx : x ≤ 2 * n
      · refine Finset.sum_bij (fun k _ => x + b * k) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro k hk
          have hk' := (Nat.le_div_iff_mul_le hb).mp (by simpa using hk)
          rw [Nat.mul_comm k b] at hk'
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by
            simp [Nat.mod_eq_of_lt hxb]⟩
        · intro k _ l _ hkl
          exact Nat.eq_of_mul_eq_mul_left hb (Nat.add_left_cancel hkl)
        · intro i hi
          obtain ⟨hi, hmod⟩ := Finset.mem_filter.mp hi
          have heq : x + b * (i / b) = i := by rw [← hmod, Nat.mod_add_div]
          refine ⟨i / b, Finset.mem_range.mpr (Nat.lt_succ_of_le ?_), heq⟩
          apply (Nat.le_div_iff_mul_le hb).mpr
          rw [Nat.mul_comm (i / b)]
          have := Finset.mem_range.mp hi
          omega
      · have hempty : (Finset.range (2 * n + 1)).filter (fun i => i % b = x) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro i hi hmod
          have := Finset.mem_range.mp hi
          have := Nat.mod_le i b
          omega
        -- Truncated subtraction leaves one term, whose coefficient is past the degree.
        have hcoeff : trinomialCoefficient n x = 0 :=
          coeff_eq_zero_of_natDegree_lt (hdegree.trans_lt (Nat.lt_of_not_ge hx))
        simp [hempty, Nat.sub_eq_zero_of_le (le_of_not_ge hx), c, hcoeff]
    calc
      _ = ∑ i ∈ Finset.range (2 * n + 1), if i % b = x then c i else 0 := by
        simpa only [Finset.sum_filter] using hindices
      _ = (1 / (b : ℂ)) * ∑ i ∈ Finset.range (2 * n + 1),
          c i * ∑ j ∈ Finset.Icc 1 b, (w ^ ((i : ℤ) - x)) ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsum]
        by_cases hi : i % b = x
        · rw [ite_eq_left hi, ite_eq_left hi, one_div, mul_left_comm, inv_mul_cancel₀ hbC, mul_one]
        · simp [hi]
      _ = (1 / (b : ℂ)) * ∑ j ∈ Finset.Icc 1 b,
          ∑ i ∈ Finset.range (2 * n + 1), c i * (w ^ ((i : ℤ) - x)) ^ j := by
        apply congrArg ((1 / (b : ℂ)) * ·)
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
      _ = _ := by
        simp_rw [← hterm]
        rw [← Finset.mul_sum]
        ring

/-- Sun's generalized central trinomial coefficient
`T_n(b, c) = [xⁿ] (x² + b x + c)ⁿ`.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Journal of Integer Sequences 29 (2026),
Article 26.5.2, Section 4 (definition quoted from
Z.-W. Sun, Sci. China Math. 57 (2014)). -/
noncomputable def generalizedCentralTrinomial (b c : ℤ) (n : ℕ) : ℤ :=
  ((Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) ^ n).coeff n

/-- `T_0(b, c) = 1`.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Section 4. -/
theorem generalizedCentralTrinomial_zero (b c : ℤ) :
    generalizedCentralTrinomial b c 0 = 1 := by
  simp [generalizedCentralTrinomial]

/-- `T_1(b, c) = b`.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Section 4. -/
theorem generalizedCentralTrinomial_one (b c : ℤ) :
    generalizedCentralTrinomial b c 1 = b := by
  rw [generalizedCentralTrinomial, pow_one, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  simp

/-- Binomial-sum form of Sun's generalized central trinomial coefficient, before
folding the two binomials: `T_n(b, c) = ∑_{k ≤ n} C(n, k) C(n - k, k) b^(n - 2k) cᵏ`.

Source: Z.-W. Sun, *Congruences involving generalized central trinomial coefficients*,
Sci. China Math. 57 (2014), introduction; quoted in Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle Coefficients", Journal of Integer
Sequences 29 (2026), Article 26.5.2, Section 4. -/
theorem generalizedCentralTrinomial_eq_sum_choose_choose_sub (b c : ℤ) (n : ℕ) :
    generalizedCentralTrinomial b c n =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k * (n - k).choose k : ℤ) * b ^ (n - 2 * k) * c ^ k := by
  have hbase : (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c : Polynomial ℤ) =
      Polynomial.C c + Polynomial.X * (Polynomial.X + Polynomial.C b) := by
    ring
  rw [generalizedCentralTrinomial, hbase, add_pow, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Polynomial.coeff_mul_natCast, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul']
  simp only [Nat.sub_le, ite_true]
  rw [Polynomial.coeff_X_add_C_pow, Nat.sub_sub_self hkn,
    show n - k - k = n - 2 * k by omega]
  ring

/-- Sun's binomial-sum formula for the generalized central trinomial coefficient:
`T_n(b, c) = ∑_{k=0}^{⌊n/2⌋} C(n, 2k) C(2k, k) b^(n - 2k) cᵏ`.

Source: Z.-W. Sun, *Congruences involving generalized central trinomial coefficients*,
Sci. China Math. 57 (2014), introduction; quoted in Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle Coefficients", Journal of Integer
Sequences 29 (2026), Article 26.5.2, Section 4. -/
theorem generalizedCentralTrinomial_eq_sum (b c : ℤ) (n : ℕ) :
    generalizedCentralTrinomial b c n =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * k) * (2 * k).choose k : ℤ) * b ^ (n - 2 * k) * c ^ k := by
  rw [generalizedCentralTrinomial_eq_sum_choose_choose_sub]
  calc
    (∑ k ∈ Finset.range (n + 1),
        (n.choose k * (n - k).choose k : ℤ) * b ^ (n - 2 * k) * c ^ k) =
        ∑ k ∈ Finset.range (n / 2 + 1),
          (n.choose k * (n - k).choose k : ℤ) * b ^ (n - 2 * k) * c ^ k := by
      refine (Finset.sum_subset (fun k hk => ?_) fun k hk hnot => ?_).symm
      · simp only [Finset.mem_range] at hk ⊢
        omega
      · simp only [Finset.mem_range] at hk hnot
        rw [Nat.choose_eq_zero_of_lt (by omega : n - k < k)]
        simp
    _ = ∑ k ∈ Finset.range (n / 2 + 1),
          (n.choose (2 * k) * (2 * k).choose k : ℤ) * b ^ (n - 2 * k) * c ^ k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hchoose := Nat.choose_mul (n := n) (k := 2 * k) (s := k) (by omega)
      rw [show 2 * k - k = k by omega] at hchoose
      rw [← Nat.cast_mul, ← Nat.cast_mul, hchoose]

end

end MetaMathlibExt
