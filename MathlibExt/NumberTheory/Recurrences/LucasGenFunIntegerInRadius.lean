/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import MathlibExt.NumberTheory.Recurrences.LucasAdditionCompanion
import MathlibExt.NumberTheory.Recurrences.LucasCompanionIdentity
import MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition
import MathlibExt.NumberTheory.Recurrences.OddFibonacciLucasPell

/-!
# Integer values of the Lucas generating function inside its radius of convergence

For positive natural numbers $a,b$ with $b \mid a$ and $a \ne 1$, a rational input strictly
inside the radius gives an integer value precisely at the even Fibonacci ratios and odd Lucas
ratios evaluated at $x=1$. Inside the radius, an integer value is at least two and its input
is nonnegative. Completing the square gives the odd Pell equation, and the two parities of
its index give the two ratio families. Conversely, Cassini's identity evaluates the generating
function at these ratios, and divisibility by the corresponding power of $b$ gives integrality.

## References

* Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
  Fibonacci Polynomials*, The Fibonacci Quarterly 62(2) (2024), 157–172, Corollary 1.7 and
  Proposition 2.3, with the square completion from §3.2 and §3.4.
* Andrew Bulawa and Whan Ki Lee, *Integer Values of Generating Functions for the Fibonacci and
  Related Sequences*, The Fibonacci Quarterly 55(1) (2017), 74–81, Lemma 1.3 and Proposition 1.4,
  credited by Tsuno for the squarefree Pell classification and the reduction to it.
* Yuji Tsuno, *Extended Results on Integer Values of Generating Functions for Sequences Given
  by Pell's Equations*, The Fibonacci Quarterly 59(2) (2021), 158–166, §2, for the Pell approach
  to generating-function values.
-/

namespace MetaMathlibExt

open Polynomial

local notation "𝔽[" a ", " b "]" =>
  generalizedFibonacciPolynomial 0 1 (C ((a : ℕ) : ℤ) * X) (C ((b : ℕ) : ℤ))

local notation "𝕃[" a ", " b "]" =>
  generalizedFibonacciPolynomial 2 (C ((a : ℕ) : ℤ) * X) (C ((a : ℕ) : ℤ) * X) (C ((b : ℕ) : ℤ))

private def lucasGenFunParams (a b : ℕ) (hb : 0 < b) : LucasSequenceParams :=
  ⟨a, -(b : ℤ), neg_ne_zero.mpr (by exact_mod_cast hb.ne')⟩

section

variable {a b : ℕ} (hb : 0 < b)

local notation "S" => lucasGenFunParams a b hb
local notation "U" => lucasU S
local notation "V" => lucasV S

private theorem eval_fibonacci_eq_lucasU (n : ℕ) : (𝔽[a, b] n).eval 1 = U n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucasU.eq_1]
  | one => simp [lucasU.eq_2]
  | more n h₀ h₁ =>
    simp only [generalizedFibonacciPolynomial_add_two, eval_add, eval_mul, h₀, h₁,
      eval_C, eval_X, mul_one, lucasU_add_two]
    simp [lucasGenFunParams]

private theorem eval_lucas_eq_lucasV (n : ℕ) : (𝕃[a, b] n).eval 1 = V n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucasV.eq_1]
  | one => simp [lucasV.eq_2, lucasGenFunParams]
  | more n h₀ h₁ =>
    simp only [generalizedFibonacciPolynomial_add_two, eval_add, eval_mul, h₀, h₁,
      eval_C, eval_X, mul_one, lucasV.eq_3]
    simp [lucasGenFunParams]

private theorem genFun_even_odd_dvd (hba : b ∣ a) (r : ℕ) :
    (b : ℤ) ^ r ∣ U (2 * r) ∧ (b : ℤ) ^ r ∣ U (2 * r + 1) := by
  have hba' : (b : ℤ) ∣ a := by exact_mod_cast hba
  have hstep (r n : ℕ) (hx : (b : ℤ) ^ r ∣ U n) (hy : (b : ℤ) ^ r ∣ U (n + 1)) :
      (b : ℤ) ^ (r + 1) ∣ U (n + 2) := by
    rw [lucasU_add_two, pow_succ]
    simp only [lucasGenFunParams, neg_mul, sub_neg_eq_add, mul_comm ((b : ℤ) ^ r) (b : ℤ)]
    exact dvd_add (mul_dvd_mul hba' hy) (mul_dvd_mul (dvd_refl (b : ℤ)) hx)
  induction r with
  | zero => simp
  | succ r ih =>
    obtain ⟨he, ho⟩ := ih
    have he' := hstep r (2 * r) he ho
    have he'' : (b : ℤ) ^ r ∣ U (2 * r + 1 + 1) :=
      dvd_trans (dvd_mul_right _ _) (by simpa only [pow_succ] using he')
    have ho' := hstep r (2 * r + 1) ho he''
    exact ⟨by simpa only [Nat.mul_succ] using he', by simpa only [Nat.mul_succ] using ho'⟩

-- The same ratio gives a Fibonacci quotient at even indices and a Lucas quotient at odd ones.
private theorem genFun_doubled_ratio (r : ℕ) (hden : (U (2 * r + 1) : ℚ) + (b : ℚ) ^ r ≠ 0) :
    (U (2 * r) : ℚ) / ((U (2 * r + 1) : ℚ) + (b : ℚ) ^ r) =
      if Even r then (U r : ℚ) / U (r + 1) else (V r : ℚ) / V (r + 1) := by
  have hadd : U (2 * r + 1) = U (r + 1) * V r - (-(b : ℤ)) ^ r := by
    have h := lucasU_add_eq_mul_lucasV_sub S (m := r + 1) (n := r) (by omega)
    simpa only [lucasGenFunParams, show r + 1 + r = 2 * r + 1 by omega,
      show r + 1 - r = 1 by omega, lucasU.eq_2, mul_one] using h
  have hdouble : (U (2 * r) : ℚ) = (U r : ℚ) * V r := by
    exact_mod_cast lucasU_two_mul_eq_lucasU_mul_lucasV S r
  by_cases hr : Even r
  · have hprod : (U (2 * r + 1) : ℚ) + (b : ℚ) ^ r = (U (r + 1) : ℚ) * V r := by
      exact_mod_cast (by rw [hadd, hr.neg_pow, sub_add_cancel] :
        U (2 * r + 1) + (b : ℤ) ^ r = U (r + 1) * V r)
    rw [hprod] at hden
    rw [ite_eq_left hr, hdouble, hprod, mul_div_mul_right _ _ (right_ne_zero_of_mul hden)]
  · have hodd : Odd r := Nat.not_even_iff_odd.mp hr
    have hprod : (U (2 * r + 1) : ℚ) + (b : ℚ) ^ r = (U r : ℚ) * V (r + 1) := by
      have h :=
        MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted.two_mul_lucasU_add
          S (r + 1) r
      rw [show r + 1 + r = 2 * r + 1 by omega] at h
      rw [hodd.neg_pow] at hadd
      exact_mod_cast (by linear_combination h - hadd :
        U (2 * r + 1) + (b : ℤ) ^ r = U r * V (r + 1))
    rw [hprod] at hden
    rw [ite_eq_right hr, hdouble, hprod, mul_div_mul_left _ _ (left_ne_zero_of_mul hden)]

-- The denominator of the generating function and the factor controlling its difference from 2.
private theorem genFun_radius_bounds {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : 2 * b ≤ a ^ 2)
    {q : ℚ} (hq : |(q : ℝ)| < 2 / (a + Real.sqrt (a ^ 2 + 4 * b))) :
    0 < 1 - (a : ℚ) * q - b * q ^ 2 ∧ 0 < (a : ℚ) + 2 * b * q := by
  let s := Real.sqrt ((a : ℝ) ^ 2 + 4 * b)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
  have hs₂ : s ^ 2 = (a : ℝ) ^ 2 + 4 * b := Real.sq_sqrt (by positivity)
  have hs : (a : ℝ) ≤ s := by
    apply (sq_le_sq₀ ha'.le hs₀).mp
    rw [hs₂]
    linarith only [hb']
  have hsum : 0 < (a : ℝ) + s := add_pos_of_pos_of_nonneg ha' hs₀
  have hupper : |(q : ℝ)| * ((a : ℝ) + s) < 2 := (lt_div_iff₀ hsum).mp hq
  have hqSq : (q : ℝ) ^ 2 = |(q : ℝ)| ^ 2 := (sq_abs _).symm
  have hA : (a : ℝ) * |(q : ℝ)| < 1 := by
    nlinarith only [hupper, mul_nonneg (sub_nonneg.mpr hs) (abs_nonneg (q : ℝ))]
  have hD : 0 < 1 - (a : ℝ) * |(q : ℝ)| - b * |(q : ℝ)| ^ 2 := by
    have hleft : 0 < 2 - (a + s) * |(q : ℝ)| := by linarith only [hupper]
    have hright : 0 < 2 + (s - a) * |(q : ℝ)| := by positivity
    nlinarith only [mul_pos hleft hright, congrArg (fun x : ℝ ↦ x * |(q : ℝ)| ^ 2) hs₂]
  constructor
  · have hle := mul_le_mul_of_nonneg_left (le_abs_self (q : ℝ)) ha'.le
    exact_mod_cast (by rw [hqSq]; linarith only [hD, hle] :
      0 < 1 - (a : ℝ) * q - b * (q : ℝ) ^ 2)
  · have hab' : (2 : ℝ) * b ≤ (a : ℝ) ^ 2 := by exact_mod_cast hab
    have hsmall : (2 : ℝ) * b * |(q : ℝ)| < a := by
      calc
        _ ≤ (a : ℝ) ^ 2 * |(q : ℝ)| := mul_le_mul_of_nonneg_right hab' (abs_nonneg _)
        _ = (a : ℝ) * (a * |(q : ℝ)|) := by ring
        _ < a := by simpa only [mul_one] using mul_lt_mul_of_pos_left hA ha'
    have hlower := mul_le_mul_of_nonneg_left (neg_abs_le (q : ℝ)) (by positivity : 0 ≤ (2 : ℝ) * b)
    exact_mod_cast (by linarith only [hsmall, hlower] : 0 < (a : ℝ) + 2 * b * (q : ℝ))

private theorem genFun_odd_pell {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {q : ℚ} {z : ℤ}
    (hD : 0 < 1 - (a : ℚ) * q - b * q ^ 2) (hA : 0 < (a : ℚ) + 2 * b * q)
    (hz : (2 - (a : ℚ) * q) / (1 - a * q - b * q ^ 2) = z) :
    ∃ P Q : ℕ, (P : ℤ) ^ 2 - (a ^ 2 + 4 * b) * Q ^ 2 = -4 * b ∧
      (P : ℚ) = a * (Q : ℚ) + 2 * b * ((Q : ℚ) + 1) * q := by
  let D : ℚ := 1 - (a : ℚ) * q - b * q ^ 2
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hzD : 2 - (a : ℚ) * q = (z : ℚ) * D := (div_eq_iff hD.ne').mp hz
  have hz₁ : (1 : ℚ) < z := by
    apply lt_of_mul_lt_mul_right (a := D) _ hD.le
    dsimp [D] at hzD ⊢
    nlinarith only [hzD, mul_nonneg hb'.le (sq_nonneg q)]
  have hz₂ : 2 ≤ z := by
    have : (1 : ℤ) < z := by exact_mod_cast hz₁
    omega
  have hz₂' : (2 : ℚ) ≤ z := by exact_mod_cast hz₂
  have hq₀ : 0 ≤ q := by
    apply nonneg_of_mul_nonneg_left _ hA
    have hprod := mul_nonneg (sub_nonneg.mpr hz₂') hD.le
    change 0 ≤ ((z : ℚ) - 2) * D at hprod
    dsimp [D] at hzD hprod
    nlinarith only [hzD, hprod]
  let Q := (z - 1).toNat
  have hQ : (Q : ℤ) = z - 1 := Int.toNat_of_nonneg (by omega)
  have hQ' : (Q : ℚ) = (z : ℚ) - 1 := by exact_mod_cast hQ
  let p : ℚ := (a : ℚ) * Q + 2 * b * z * q
  have hp₀ : 0 ≤ p := by dsimp [p]; positivity
  let k : ℤ := (a ^ 2 + 4 * (b : ℤ)) * Q ^ 2 - 4 * b
  have hp₂ : p ^ 2 = (k : ℚ) := by
    dsimp [p, k]
    push_cast
    rw [hQ']
    dsimp [D] at hzD
    linear_combination 4 * (b : ℚ) * z * hzD
  have hden : p.den = 1 := by
    have h := congrArg Rat.den hp₂
    rw [Rat.den_pow, Rat.den_intCast] at h
    exact (Nat.pow_eq_one.mp h).resolve_right (by decide)
  have hpnum : (p.num : ℚ) = p := Rat.intCast_num_of_den_eq_one hden
  have hpnum₀ : 0 ≤ p.num := by exact_mod_cast (hpnum ▸ hp₀)
  let P := p.num.toNat
  have hP : (P : ℚ) = p := by
    exact (by exact_mod_cast Int.toNat_of_nonneg hpnum₀ : (P : ℚ) = (p.num : ℚ)).trans hpnum
  refine ⟨P, Q, ?_, ?_⟩
  · have hp₂' : (P : ℤ) ^ 2 = k := by exact_mod_cast (hP ▸ hp₂)
    dsimp [k] at hp₂'
    linear_combination hp₂'
  · rw [hP]
    dsimp [p]
    rw [hQ', sub_add_cancel]

end

/-- **Integer values of the generalized Lucas generating function in its interval of
convergence.** Let $a$ and $b$ be positive integers with $a \ne 1$ and $b \mid a$, and let
$F_i(x), L_i(x) \in \mathbb{Z}[x]$ be the polynomials with $F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = ax$ and $G_{i+2} = ax\,G_{i+1} + b\,G_i$ for $G = F, L$ and all $i \ge 0$. For a rational
number $q$ with $|q| < 2 / (a + \sqrt{a^2 + 4b})$, the radius of convergence of the power series
of $(2 - at) / (1 - at - bt^2)$, the number $(2 - aq) / (1 - aq - bq^2)$ is an integer if and
only if $q = F_{2i}(1) / F_{2i+1}(1)$ or $q = L_{2i+1}(1) / L_{2i+2}(1)$ for some
$i \in \mathbb{N}$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Corollary 1.7
(`fq-2024-tsuno05142024-cor-1.7`). -/
public theorem lucasGenFun_eval_isInt_iff_of_abs_lt_radius {a b : ℕ} (ha : 0 < a)
    (ha1 : a ≠ 1) (hb : 0 < b) (hba : b ∣ a) {q : ℚ}
    (hq : |(q : ℝ)| < 2 / (a + Real.sqrt (a ^ 2 + 4 * b))) :
    (∃ n : ℤ, (2 - a * q) / (1 - a * q - b * q ^ 2) = n) ↔
      ∃ i : ℕ, q = (((𝔽[a, b] (2 * i)).eval 1 : ℤ) : ℚ) / (((𝔽[a, b] (2 * i + 1)).eval 1 : ℤ) : ℚ) ∨
        q = (((𝕃[a, b] (2 * i + 1)).eval 1 : ℤ) : ℚ) / (((𝕃[a, b] (2 * i + 2)).eval 1 : ℤ) : ℚ)
    := by
  have hab : 2 * b ≤ a ^ 2 := by
    calc
      _ ≤ 2 * a := Nat.mul_le_mul_left 2 (Nat.le_of_dvd ha hba)
      _ ≤ a ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul_right a (show 2 ≤ a by omega)
  obtain ⟨hD, hA⟩ := genFun_radius_bounds ha hb hab hq
  let S := lucasGenFunParams a b hb
  let U := lucasU S
  let V := lucasV S
  have hSp : S.p = (a : ℤ) := rfl
  have hSq : S.q = -(b : ℤ) := rfl
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hU (n : ℕ) : 0 ≤ U n := by
    induction n using Nat.twoStepInduction with
    | zero => simp [U, lucasU.eq_1]
    | one => simp [U, lucasU.eq_2]
    | more n h₀ h₁ =>
      change 0 ≤ lucasU S (n + 2)
      rw [lucasU_add_two, hSp, hSq, neg_mul, sub_neg_eq_add]
      exact add_nonneg (mul_nonneg ha'.le h₁) (mul_nonneg hb'.le h₀)
  have hden (r : ℕ) : (U (2 * r + 1) : ℚ) + (b : ℚ) ^ r ≠ 0 :=
    (add_pos_of_nonneg_of_pos (by exact_mod_cast hU (2 * r + 1)) (pow_pos hbq r)).ne'
  simp only [eval_fibonacci_eq_lucasU hb, eval_lucas_eq_lucasV hb]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨P, Q, hpell, hcoord⟩ := genFun_odd_pell ha hb hD hA hz
    obtain ⟨r, hL, hF⟩ := fibLucas_odd_of_pell_eq ha hb hba hpell
    rw [eval_lucas_eq_lucasV hb] at hL
    rw [eval_fibonacci_eq_lucasU hb] at hF
    have hL' : (b : ℚ) ^ r * P = V (2 * r + 1) := by exact_mod_cast hL
    have hF' : (b : ℚ) ^ r * Q = U (2 * r + 1) := by exact_mod_cast hF
    have hcomp : (V (2 * r + 1) : ℚ) = a * (U (2 * r + 1) : ℚ) + 2 * b * U (2 * r) := by
      have h := lucasV_eq_lucasU_succ_sub S (n := 2 * r + 1) (by omega)
      simp only [hSp, hSq, Nat.add_sub_cancel, lucasU_add_two,
        neg_mul, sub_neg_eq_add] at h
      have hcomp' : lucasV S (2 * r + 1) =
          a * lucasU S (2 * r + 1) + 2 * b * lucasU S (2 * r) := by
        linear_combination h
      exact_mod_cast hcomp'
    have hq' : q = (U (2 * r) : ℚ) / ((U (2 * r + 1) : ℚ) + (b : ℚ) ^ r) := by
      apply (eq_div_iff (hden r)).2
      apply mul_left_cancel₀ (show 2 * (b : ℚ) ≠ 0 by positivity)
      linear_combination hL' + hcomp - (a + 2 * (b : ℚ) * q) * hF' - (b : ℚ) ^ r * hcoord
    rw [genFun_doubled_ratio hb r (hden r)] at hq'
    rcases Nat.even_or_odd r with hr | hr
    · rw [ite_eq_left hr] at hq'
      obtain ⟨i, hi⟩ := hr
      rw [show r = 2 * i by omega] at hq'
      exact ⟨i, Or.inl hq'⟩
    · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hr)] at hq'
      obtain ⟨i, hi⟩ := hr
      rw [show r = 2 * i + 1 by omega] at hq'
      exact ⟨i, Or.inr hq'⟩
  · intro h
    obtain ⟨r, hr⟩ : ∃ r : ℕ, q = (U (2 * r) : ℚ) / ((U (2 * r + 1) : ℚ) + (b : ℚ) ^ r) := by
      rcases h with ⟨i, hi | hi⟩
      · exact ⟨2 * i, by rwa [genFun_doubled_ratio hb _ (hden _), ite_eq_left (even_two_mul i)]⟩
      · exact ⟨2 * i + 1, by
          rwa [genFun_doubled_ratio hb _ (hden _),
            ite_eq_right (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one i))]⟩
    let F : ℚ := U (2 * r)
    let G : ℚ := U (2 * r + 1)
    let B : ℚ := (b : ℚ) ^ r
    have hcross : q * (G + B) = F := (eq_div_iff (hden r)).mp hr
    have hcass : G ^ 2 - (a : ℚ) * F * G - b * F ^ 2 = B ^ 2 := by
      have h := lucasU_cassini S (2 * r)
      simp only [lucasU_add_two, hSq, hSp, neg_mul, sub_neg_eq_add, pow_mul, neg_sq] at h
      have hcass' : lucasU S (2 * r + 1) ^ 2 - a * lucasU S (2 * r) * lucasU S (2 * r + 1) -
          b * lucasU S (2 * r) ^ 2 = ((b : ℤ) ^ r) ^ 2 := by
        linear_combination h
      dsimp only [G, F, B, U]
      exact_mod_cast hcass'
    have hvalue : (1 - (a : ℚ) * q - b * q ^ 2) * (G + B) = B * (2 - a * q) := by
      apply mul_right_cancel₀ (hden r)
      rw [← hcross] at hcass
      linear_combination hcass
    obtain ⟨k, hk⟩ := (genFun_even_odd_dvd hb hba r).2
    have hk' : G = B * (k : ℚ) := by
      dsimp only [G, B, U, S]
      exact_mod_cast hk
    refine ⟨k + 1, (div_eq_iff hD.ne').2 ?_⟩
    apply mul_left_cancel₀ (show B ≠ 0 from pow_ne_zero _ hbq.ne')
    push_cast
    linear_combination -hvalue + (1 - (a : ℚ) * q - b * q ^ 2) * hk'

end MetaMathlibExt
