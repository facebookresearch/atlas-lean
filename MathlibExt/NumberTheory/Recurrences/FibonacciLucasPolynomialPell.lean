/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Polynomial Pell equations for Fibonacci and Lucas polynomials

For positive integers $a,b$, a rational polynomial pair with nonnegative leading coefficients
satisfying $P^2-(a^2x^2+4b)Q^2=4(-b)^r$, with $r\in\{0,1\}$, is a Fibonacci–Lucas pair
at an index $n\equiv r\pmod 2$, divided by $b^{\lfloor n/2\rfloor}$. The proof descends one
index at a time, reversing the recurrences in equations (11)–(14) of the reference and
normalizing the right-hand side at each step. No divisibility condition on $a$ and $b$ is needed.

## References

* Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
  Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), no. 2, pp. 157–172,
  Proposition 2.1 and equations (11)–(14).
-/

namespace MetaMathlibExt

open Polynomial

local notation "𝔽[" a ", " b "]" =>
  generalizedFibonacciPolynomial 0 1 (C ((a : ℕ) : ℤ) * X) (C ((b : ℕ) : ℤ))

local notation "𝕃[" a ", " b "]" =>
  generalizedFibonacciPolynomial 2 (C ((a : ℕ) : ℤ) * X) (C ((a : ℕ) : ℤ) * X) (C ((b : ℕ) : ℤ))

local notation "A[" a "]" => C (a : ℚ) * (X : ℚ[X])
local notation "Δ[" a ", " b "]" => A[a] ^ 2 + C (4 * (b : ℚ))

private theorem polynomialPell_degreeStep {a b k : ℚ} (ha : 0 < a) (hb : 0 < b)
    {P Q : ℚ[X]} (hP : 0 ≤ P.leadingCoeff) (hQ : 0 < Q.leadingCoeff)
    (h : P ^ 2 - Δ[a, b] * Q ^ 2 = C k) :
    (Δ[a, b] * Q - A[a] * P).natDegree < P.natDegree ∧
      0 ≤ (Δ[a, b] * Q - A[a] * P).leadingCoeff ∧ 0 ≤ (P - A[a] * Q).leadingCoeff := by
  let A := A[a]
  let D := Δ[a, b]
  let U := P + A * Q
  let V := P - A * Q
  let W := D * Q - A * P
  change P ^ 2 - D * Q ^ 2 = C k at h
  change W.natDegree < P.natDegree ∧ 0 ≤ W.leadingCoeff ∧ 0 ≤ V.leadingCoeff
  have ha₀ : A.natDegree = 1 := natDegree_C_mul_X a ha.ne'
  have ha₁ : A.leadingCoeff = a := by simp [A]
  have ha₂ : A ≠ 0 := leadingCoeff_ne_zero.mp (ha₁ ▸ ha.ne')
  have hq₀ : Q ≠ 0 := leadingCoeff_ne_zero.mp hQ.ne'
  have hb₀ : 0 < 4 * b := by positivity
  have hd : D.natDegree = 2 := by
    change (A ^ 2 + C (4 * b)).natDegree = 2
    rw [natDegree_add_C, natDegree_pow, ha₀, mul_one]
  have hd₀ : D ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by rw [hd]; decide)
  have hpdeg : P.natDegree = Q.natDegree + 1 := by
    have hsum : P ^ 2 = D * Q ^ 2 + C k := by linear_combination h
    have hdeg := congrArg natDegree hsum
    simp only [natDegree_add_C, natDegree_mul hd₀ (pow_ne_zero _ hq₀), natDegree_pow, hd] at hdeg
    omega
  have hp₀ : P ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by rw [hpdeg]; omega)
  have hp₁ := lt_of_le_of_ne hP (leadingCoeff_ne_zero.mpr hp₀).symm
  have haqdeg : (A * Q).natDegree = P.natDegree := by
    rw [natDegree_mul ha₂ hq₀, ha₀, hpdeg, add_comm]
  have hu : U.leadingCoeff = P.leadingCoeff + a * Q.leadingCoeff := by
    dsimp only [U]
    rw [leadingCoeff_add_of_degree_eq ?_ ?_, leadingCoeff_mul, ha₁]
    · rw [degree_eq_natDegree hp₀, degree_eq_natDegree (mul_ne_zero ha₂ hq₀), haqdeg]
    · rw [leadingCoeff_mul, ha₁]
      exact (add_pos_of_pos_of_nonneg hp₁ (mul_pos ha hQ).le).ne'
  have hu₁ : 0 < U.leadingCoeff := by rw [hu]; positivity
  have hu₀ : U ≠ 0 := leadingCoeff_ne_zero.mp hu₁.ne'
  have hudeg : U.natDegree = P.natDegree := by
    have hdeg : U.degree = P.degree := by
      dsimp only [U]
      rw [degree_add_eq_of_leadingCoeff_add_ne_zero, degree_eq_natDegree hp₀,
        degree_eq_natDegree (mul_ne_zero ha₂ hq₀), haqdeg, max_self]
      simpa only [leadingCoeff_mul, ha₁, ← hu] using hu₁.ne'
    exact natDegree_eq_natDegree hdeg
  have hV : V * U = C (4 * b) * Q ^ 2 + C k := by
    dsimp only [V, U, D] at h ⊢
    linear_combination h
  by_cases hqdeg : Q.natDegree = 0
  · -- A nonzero constant Q forces P = A*Q, so the next pair has second component zero.
    have hv₀ : V = 0 := by
      by_contra hv₀
      have hdeg := congrArg natDegree hV
      simp only [natDegree_mul hv₀ hu₀, hudeg, hpdeg, hqdeg, natDegree_add_C,
        natDegree_C_mul hb₀.ne', natDegree_pow, mul_zero] at hdeg
      omega
    have hw : W = C (4 * b) * Q := by
      have hv := sub_eq_zero.mp (show P - A * Q = 0 from hv₀)
      dsimp only [W, D]
      rw [hv]
      ring
    rw [hw, natDegree_C_mul hb₀.ne', hpdeg, leadingCoeff_mul, leadingCoeff_C, hv₀,
      leadingCoeff_zero]
    exact ⟨Nat.lt_succ_self _, (mul_pos hb₀ hQ).le, le_rfl⟩
  have hVlead : 0 ≤ V.leadingCoeff := by
    have hdeg : (C (4 * b) * Q ^ 2).natDegree = 2 * Q.natDegree := by
      rw [natDegree_C_mul hb₀.ne', natDegree_pow]
    have hlt : (C k).degree < (C (4 * b) * Q ^ 2).degree :=
      degree_lt_degree (by rw [natDegree_C, hdeg]; omega)
    have hlead := congrArg leadingCoeff hV
    rw [leadingCoeff_mul, leadingCoeff_add_of_degree_lt' hlt, leadingCoeff_mul,
      leadingCoeff_C, leadingCoeff_pow] at hlead
    exact (pos_of_mul_pos_left (hlead.symm ▸ mul_pos hb₀ (pow_pos hQ _)) hu₁.le).le
  -- Multiply by the positive-leading partner U to read off the degree and sign of W.
  have hW : W * U = C (4 * b) * (P * Q) - A * C k := by
    dsimp only [W, U, D] at h ⊢
    linear_combination -A * h
  have hdegLeft : (C (4 * b) * (P * Q)).natDegree = P.natDegree + Q.natDegree := by
    rw [natDegree_C_mul hb₀.ne', natDegree_mul hp₀ hq₀]
  have hdegRight : (A * C k).natDegree ≤ 1 := by
    simpa only [ha₀, natDegree_C, add_zero] using natDegree_mul_le (p := A) (q := C k)
  have hlt : (A * C k).natDegree < (C (4 * b) * (P * Q)).natDegree := by
    rw [hdegLeft]
    omega
  have hWlead := congrArg leadingCoeff hW
  rw [leadingCoeff_mul, leadingCoeff_sub_of_degree_lt (degree_lt_degree hlt),
    leadingCoeff_mul, leadingCoeff_C, leadingCoeff_mul] at hWlead
  have hw₁ : 0 < W.leadingCoeff :=
    pos_of_mul_pos_left (hWlead.symm ▸ mul_pos hb₀ (mul_pos hp₁ hQ)) hu₁.le
  have hWdeg := congrArg natDegree hW
  rw [natDegree_mul (leadingCoeff_ne_zero.mp hw₁.ne') hu₀, hudeg,
    natDegree_sub_eq_left_of_natDegree_lt hlt, hdegLeft] at hWdeg
  exact ⟨by omega, hw₁.le, hVlead⟩

private theorem fibonacciLucas_succ (A B : ℤ[X]) (n : ℕ) :
    let L := generalizedFibonacciPolynomial 2 A A B
    let F := generalizedFibonacciPolynomial 0 1 A B
    2 * L (n + 1) = A * L n + (A ^ 2 + 4 * B) * F n ∧
      2 * F (n + 1) = L n + A * F n := by
  dsimp only
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [Nat.zero_add, generalizedFibonacciPolynomial_zero,
      generalizedFibonacciPolynomial_one]
    constructor <;> ring
  | one =>
    change 2 * generalizedFibonacciPolynomial 2 A A B (0 + 2) = _ ∧
      2 * generalizedFibonacciPolynomial 0 1 A B (0 + 2) = _
    simp only [generalizedFibonacciPolynomial_add_two, Nat.zero_add,
      generalizedFibonacciPolynomial_zero, generalizedFibonacciPolynomial_one]
    constructor <;> ring
  | more n h₀ h₁ =>
    obtain ⟨hL₀, hF₀⟩ := h₀
    obtain ⟨hL₁, hF₁⟩ := h₁
    rw [show n + 2 + 1 = (n + 1) + 2 by omega]
    simp only [generalizedFibonacciPolynomial_add_two] at hL₁ hF₁ ⊢
    constructor
    · linear_combination A * hL₁ + B * hL₀
    · linear_combination A * hF₁ + B * hF₀

private theorem polynomialPell_zero {b k : ℚ} (hb : 0 < b) {P : ℚ[X]} (hP : 0 ≤ P.leadingCoeff)
    {r : ℕ} (hr : r ≤ 1) (hk : k = 4 * (-b) ^ r) (h : P ^ 2 = C k) : P = 2 ∧ r = 0 := by
  have hdeg := congrArg natDegree h
  rw [natDegree_pow, natDegree_C] at hdeg
  have hdeg₀ : P.natDegree = 0 := by omega
  have hc := eq_C_of_natDegree_eq_zero hdeg₀
  rw [hc, ← C_pow] at h
  have he := C_injective h
  have hcoeff : 0 ≤ P.coeff 0 := by simpa only [← coeff_natDegree, hdeg₀] using hP
  have hr₀ : r = 0 := by
    by_contra hr₀
    have hr₁ : r = 1 := by omega
    rw [hk, hr₁, pow_one] at he
    nlinarith [sq_nonneg (P.coeff 0)]
  rw [hk, hr₀, pow_zero, mul_one] at he
  have hp : P.coeff 0 = 2 := by nlinarith [mul_nonneg hcoeff (show 0 ≤ (2 : ℚ) by norm_num)]
  exact ⟨by rw [hc, hp, map_ofNat], hr₀⟩

/-- **Polynomial Pell-type solutions as rescaled Fibonacci–Lucas polynomials.** Let $a$ and $b$ be
positive integers, and let $F_n(x), L_n(x) \in \mathbb{Z}[x]$ be the polynomials with $F_0 = 0$,
$F_1 = 1$, $L_0 = 2$, $L_1 = ax$ and $G_{n+2} = ax\,G_{n+1} + b\,G_n$ for $G = F, L$ and all
$n \ge 0$. Let $r_0 \in \{0, 1\}$ and let $P(x), Q(x) \in \mathbb{Q}[x]$ have nonnegative leading
coefficients (the zero polynomial has leading coefficient $0$) and satisfy
$P(x)^2 - (a^2x^2 + 4b) Q(x)^2 = 4(-b)^{r_0}$. Then there is $n \in \mathbb{N}$ with
$n \equiv r_0 \pmod 2$, $b^{\lfloor n/2 \rfloor} P(x) = L_n(x)$ and
$b^{\lfloor n/2 \rfloor} Q(x) = F_n(x)$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024,
Proposition 2.1 (`fq-2024-tsuno05142024-prop-2.1`). -/
public theorem fibLucasPoly_of_pell_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {P Q : ℚ[X]} (hP : 0 ≤ P.leadingCoeff) (hQ : 0 ≤ Q.leadingCoeff) {r₀ : ℕ} (hr₀ : r₀ ≤ 1)
    (h : P ^ 2 - (C ((a : ℚ) ^ 2) * X ^ 2 + C (4 * (b : ℚ))) * Q ^ 2 = C (4 * (-(b : ℚ)) ^ r₀)) :
    ∃ n : ℕ, C ((b : ℚ) ^ (n / 2)) * P = (𝕃[a, b] n).map (Int.castRingHom ℚ) ∧
      C ((b : ℚ) ^ (n / 2)) * Q = (𝔽[a, b] n).map (Int.castRingHom ℚ) ∧ n % 2 = r₀ := by
  rw [C_pow, ← mul_pow] at h
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  let L := fun n => (𝕃[a, b] n).map (Int.castRingHom ℚ)
  let F := fun n => (𝔽[a, b] n).map (Int.castRingHom ℚ)
  change ∃ n : ℕ, C ((b : ℚ) ^ (n / 2)) * P = L n ∧
    C ((b : ℚ) ^ (n / 2)) * Q = F n ∧ n % 2 = r₀
  change P ^ 2 - Δ[a, b] * Q ^ 2 = C (4 * (-(b : ℚ)) ^ r₀) at h
  induction hd : P.natDegree using Nat.strong_induction_on generalizing P Q r₀ with
  | ind d ih =>
    by_cases hq : Q = 0
    · subst Q
      obtain ⟨rfl, rfl⟩ := polynomialPell_zero hb' hP hr₀ rfl (by simpa using h)
      exact ⟨0, by simp [L], by simp [F], rfl⟩
    let A := A[a]
    let D := Δ[a, b]
    let c : ℚ := (2 * (b : ℚ) ^ r₀)⁻¹
    let P' := C c * (D * Q - A * P)
    let Q' := C c * (P - A * Q)
    have hc : 0 < c := inv_pos.mpr (mul_pos (by norm_num) (pow_pos hb' _))
    obtain ⟨hdeg, hP', hQ'⟩ := polynomialPell_degreeStep ha' hb' hP
      (lt_of_le_of_ne hQ (leadingCoeff_ne_zero.mpr hq).symm) h
    have hsmall : P'.natDegree < d := by
      rw [← hd, show P'.natDegree = (D * Q - A * P).natDegree from natDegree_C_mul hc.ne']
      exact hdeg
    have hP'₀ : 0 ≤ P'.leadingCoeff := by
      simpa only [P', leadingCoeff_mul, leadingCoeff_C] using mul_nonneg hc.le hP'
    have hQ'₀ : 0 ≤ Q'.leadingCoeff := by
      simpa only [Q', leadingCoeff_mul, leadingCoeff_C] using mul_nonneg hc.le hQ'
    have hr : r₀ = 0 ∨ r₀ = 1 := by omega
    have hflip : P' ^ 2 - D * Q' ^ 2 = C (4 * (-(b : ℚ)) ^ (1 - r₀)) := by
      calc
        _ = C c ^ 2 * (-C (4 * (b : ℚ)) * (P ^ 2 - D * Q ^ 2)) := by
          dsimp only [P', Q', D, A]
          ring
        _ = _ := by
          rw [h, ← C_neg, ← C_mul, ← C_pow, ← C_mul]
          congr 1
          rcases hr with hr | hr <;>
            simp only [c, hr, pow_zero, pow_one, Nat.sub_zero, Nat.sub_self]
          · norm_num; ring
          · field_simp; ring
    obtain ⟨n, hLn, hFn, hn⟩ := ih P'.natDegree hsmall hP'₀ hQ'₀ (by omega) hflip rfl
    have hscale : C c * C (4 * (b : ℚ)) = C (2 * (b : ℚ) ^ (1 - r₀)) := by
      rw [← C_mul]
      congr 1
      rcases hr with hr | hr <;> simp only [c, hr, pow_zero, pow_one, Nat.sub_zero, Nat.sub_self]
      · norm_num; ring
      · field_simp; ring
    have hbackL : A * P' + D * Q' = C (2 * (b : ℚ) ^ (1 - r₀)) * P := by
      rw [← hscale]
      dsimp only [P', Q', D, A]
      ring
    have hbackF : P' + A * Q' = C (2 * (b : ℚ) ^ (1 - r₀)) * Q := by
      rw [← hscale]
      dsimp only [P', Q', D, A]
      ring
    have hpow : (n + 1) / 2 = n / 2 + (1 - r₀) := by omega
    have hrescale : C ((b : ℚ) ^ (n / 2)) * C (2 * (b : ℚ) ^ (1 - r₀)) =
        2 * C ((b : ℚ) ^ ((n + 1) / 2)) := by
      rw [hpow, pow_add, ← C_mul, ← map_ofNat C, ← C_mul]
      congr 1
      ring
    obtain ⟨hL, hF⟩ := fibonacciLucas_succ (C (a : ℤ) * X) (C (b : ℤ)) n
    have hLs : 2 * L (n + 1) = A * L n + D * F n := by
      simpa [L, F, A, D, map_ofNat] using congrArg (Polynomial.map (Int.castRingHom ℚ)) hL
    have hFs : 2 * F (n + 1) = L n + A * F n := by
      simpa [L, F, A] using congrArg (Polynomial.map (Int.castRingHom ℚ)) hF
    have ht : (2 : ℚ[X]) ≠ 0 := by norm_num
    refine ⟨n + 1, mul_left_cancel₀ ht ?_, mul_left_cancel₀ ht ?_, by omega⟩
    · linear_combination -P * hrescale - C ((b : ℚ) ^ (n / 2)) * hbackL + A * hLn + D * hFn - hLs
    · linear_combination -Q * hrescale - C ((b : ℚ) ^ (n / 2)) * hbackF + hLn + A * hFn - hFs

end MetaMathlibExt
