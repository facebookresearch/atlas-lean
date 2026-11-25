/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.Niven
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Cubic-recurrence discriminant divisibility -/

/-- **Root condition for the Roettger–Williams cubic.** For integers $S_1, S_2, R$ and a complex
number $\gamma$, put $\rho = R(\gamma + \gamma^{-1})$ (with the convention $0^{-1} = 0$) and
$S_3 = RS_1^2 - 2RS_2 - 4R^3$. The root condition holds when $\rho$ is a root of the cubic
$x^3 - S_1x^2 + S_2x - S_3$, that is, when $\rho^3 - S_1\rho^2 + S_2\rho - S_3 = 0$. -/
def cubicRecurrenceRootCondition (S₁ S₂ R : ℤ) (γ : ℂ) : Prop :=
  let ρ := (R : ℂ) * (γ + γ⁻¹)
  let S₃ : ℤ := R * S₁ ^ 2 - 2 * R * S₂ - 4 * R ^ 3
  ρ ^ 3 - (S₁ : ℂ) * ρ ^ 2 + (S₂ : ℂ) * ρ - (S₃ : ℂ) = 0

/-- **Cubic recurrence pair.** Integer sequences $U$ and $W$ form a cubic recurrence pair for
integers $S_1, S_2, R$ when there are pairwise distinct complex numbers $\gamma_1, \gamma_2,
\gamma_3$, each different from $1$, with $\gamma_1\gamma_2\gamma_3 = 1$, such that each
$\gamma_i$ satisfies the cubic recurrence root condition for $(S_1, S_2, R)$, $U_0 = 0$,
$U_n(1 - \gamma_1)(1 - \gamma_2)(1 - \gamma_3) = R^{n-1}(1 - \gamma_1^n)(1 - \gamma_2^n)
(1 - \gamma_3^n)$ for every $n \ge 1$, and
$W_n = R^n\bigl((1 + \gamma_1^n)(1 + \gamma_2^n)(1 + \gamma_3^n) - 2\bigr)$ for every $n \ge 0$.

These equations determine every value of $U$ and $W$; the equation for $U_n$ is the source's
formula with its denominator $(1 - \gamma_1)(1 - \gamma_2)(1 - \gamma_3)$ cleared. -/
def IsCubicRecurrencePair
    (S₁ S₂ R : ℤ) (U W : ℕ → ℤ) : Prop :=
  ∃ γ₁ γ₂ γ₃ : ℂ,
    γ₁ ≠ 1 ∧ γ₂ ≠ 1 ∧ γ₃ ≠ 1 ∧
    γ₁ ≠ γ₂ ∧ γ₂ ≠ γ₃ ∧ γ₃ ≠ γ₁ ∧
    γ₁ * γ₂ * γ₃ = 1 ∧
    cubicRecurrenceRootCondition S₁ S₂ R γ₁ ∧
    cubicRecurrenceRootCondition S₁ S₂ R γ₂ ∧
    cubicRecurrenceRootCondition S₁ S₂ R γ₃ ∧
    U 0 = 0 ∧
    (∀ n : ℕ, 1 ≤ n →
      (U n : ℂ) * ((1 - γ₁) * (1 - γ₂) * (1 - γ₃)) =
        (R : ℂ) ^ (n - 1) *
          ((1 - γ₁ ^ n) * (1 - γ₂ ^ n) * (1 - γ₃ ^ n))) ∧
    ∀ n : ℕ,
      (W n : ℂ) =
        (R : ℂ) ^ n *
          ((1 + γ₁ ^ n) * (1 + γ₂ ^ n) * (1 + γ₃ ^ n) - 2)

/-- **Cubic-recurrence discriminant sequence.** For an integer $R$ and integer sequences $U$ and
$W$, the discriminant sequence is $D_n = \gcd(W_n - 6R^n, U_n)$ for $n \ge 0$: the greatest
common divisor of the natural numbers $|W_n - 6R^n|$ and $|U_n|$. -/
def cubicRecurrenceDiscriminant (R : ℤ) (U W : ℕ → ℤ) (n : ℕ) : ℕ :=
  Nat.gcd (W n - 6 * R ^ n).natAbs (U n).natAbs

private noncomputable def newtonP (S : Type*) [CommRing S] (a b c : S) : ℕ → S
  | 0 => 1 + 1 + 1
  | 1 => a
  | 2 => a ^ 2 - 2 * b
  | (k + 3) => a * newtonP S a b c (k + 2) - b * newtonP S a b c (k + 1) + c * newtonP S a b c k

private theorem newtonP_map (S T : Type*) [CommRing S] [CommRing T]
    (f : S →+* T) (a b c : S) (k : ℕ) :
    f (newtonP S a b c k) = newtonP T (f a) (f b) (f c) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [newtonP, map_add, map_one]
    | 1 => simp [newtonP]
    | 2 => simp [newtonP, map_sub, map_pow, map_mul, map_ofNat]
    | (k + 3) =>
      simp only [newtonP]
      rw [map_add, map_sub, map_mul, map_mul, map_mul, ih (k+2) (by omega),
        ih (k+1) (by omega), ih k (by omega)]

private theorem newtonP_eq_sum (S : Type*) [CommRing S] (z₁ z₂ z₃ a b c : S)
    (h1 : z₁ + z₂ + z₃ = a)
    (h2 : z₁ * z₂ + z₂ * z₃ + z₃ * z₁ = b)
    (h3 : z₁ * z₂ * z₃ = c) (k : ℕ) :
    newtonP S a b c k = z₁ ^ k + z₂ ^ k + z₃ ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [newtonP, pow_zero]
    | 1 => simp [newtonP, pow_one, ← h1]
    | 2 =>
      simp only [newtonP]
      have hsq : (z₁ + z₂ + z₃) ^ 2
          = z₁ ^ 2 + z₂ ^ 2 + z₃ ^ 2 + 2 * (z₁ * z₂ + z₂ * z₃ + z₃ * z₁) := by ring
      rw [h1, h2] at hsq
      linear_combination hsq
    | (j + 3) =>
      have key1 : z₁ ^ 3 - (z₁ + z₂ + z₃) * z₁ ^ 2
          + (z₁ * z₂ + z₂ * z₃ + z₃ * z₁) * z₁ - z₁ * z₂ * z₃ = 0 := by ring
      rw [h1, h2, h3] at key1
      have hz1 : z₁ ^ 3 = a * z₁ ^ 2 - b * z₁ + c := by linear_combination key1
      have key2 : z₂ ^ 3 - (z₁ + z₂ + z₃) * z₂ ^ 2
          + (z₁ * z₂ + z₂ * z₃ + z₃ * z₁) * z₂ - z₁ * z₂ * z₃ = 0 := by ring
      rw [h1, h2, h3] at key2
      have hz2 : z₂ ^ 3 = a * z₂ ^ 2 - b * z₂ + c := by linear_combination key2
      have key3 : z₃ ^ 3 - (z₁ + z₂ + z₃) * z₃ ^ 2
          + (z₁ * z₂ + z₂ * z₃ + z₃ * z₁) * z₃ - z₁ * z₂ * z₃ = 0 := by ring
      rw [h1, h2, h3] at key3
      have hz3 : z₃ ^ 3 = a * z₃ ^ 2 - b * z₃ + c := by linear_combination key3
      have e1 : z₁ ^ (j + 3) = a * z₁ ^ (j + 2) - b * z₁ ^ (j + 1) + c * z₁ ^ j := by
        calc z₁ ^ (j + 3) = z₁ ^ j * z₁ ^ 3 := by ring
          _ = z₁ ^ j * (a * z₁ ^ 2 - b * z₁ + c) := by rw [hz1]
          _ = a * z₁ ^ (j + 2) - b * z₁ ^ (j + 1) + c * z₁ ^ j := by ring
      have e2 : z₂ ^ (j + 3) = a * z₂ ^ (j + 2) - b * z₂ ^ (j + 1) + c * z₂ ^ j := by
        calc z₂ ^ (j + 3) = z₂ ^ j * z₂ ^ 3 := by ring
          _ = z₂ ^ j * (a * z₂ ^ 2 - b * z₂ + c) := by rw [hz2]
          _ = a * z₂ ^ (j + 2) - b * z₂ ^ (j + 1) + c * z₂ ^ j := by ring
      have e3 : z₃ ^ (j + 3) = a * z₃ ^ (j + 2) - b * z₃ ^ (j + 1) + c * z₃ ^ j := by
        calc z₃ ^ (j + 3) = z₃ ^ j * z₃ ^ 3 := by ring
          _ = z₃ ^ j * (a * z₃ ^ 2 - b * z₃ + c) := by rw [hz3]
          _ = a * z₃ ^ (j + 2) - b * z₃ ^ (j + 1) + c * z₃ ^ j := by ring
      simp only [newtonP]
      rw [ih (j+2) (by omega), ih (j+1) (by omega), ih j (by omega)]
      linear_combination -e1 - e2 - e3

private noncomputable def newtonQ (S : Type*) [CommRing S] (x y r : S) : ℕ → S
  | 0 => 0
  | 1 => 1
  | 2 => x + y + 2 * r
  | (k + 3) => y * newtonQ S x y r (k + 2) - r * x * newtonQ S x y r (k + 1)
      + r ^ 3 * newtonQ S x y r k
      + (newtonP S x (r * y) (r ^ 3) (k + 2) + r * newtonP S x (r * y) (r ^ 3) (k + 1))

private theorem newtonQ_diff (S : Type*) [CommRing S] (x y r : S) (k : ℕ) :
    newtonP S y (r * x) (r ^ 3) k - newtonP S x (r * y) (r ^ 3) k
      = (y - x) * newtonQ S x y r k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [newtonP, newtonQ]
    | 1 => simp [newtonP, newtonQ]
    | 2 =>
      simp only [newtonP, newtonQ]
      ring
    | (j + 3) =>
      have ih2 := ih (j + 2) (by omega)
      have ih1 := ih (j + 1) (by omega)
      have ih0 := ih j (by omega)
      simp only [newtonP, newtonQ]
      linear_combination y * ih2 - r * x * ih1 + r ^ 3 * ih0

private theorem newtonP_integral (x y r : ℂ)
    (hx : IsIntegral ℤ x) (hy : IsIntegral ℤ y) (hr : IsIntegral ℤ r)
    (a b c : ℂ) (ha : a = x ∨ a = y) (hb : b = r * y ∨ b = r * x)
    (hc : c = r ^ 3) (k : ℕ) :
    IsIntegral ℤ (newtonP ℂ a b c k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
      simp only [newtonP]
      exact (isIntegral_one.add isIntegral_one).add isIntegral_one
    | 1 =>
      simp only [newtonP]
      cases ha with
      | inl h => rw [h]; exact hx
      | inr h => rw [h]; exact hy
    | 2 =>
      simp only [newtonP]
      have hb' : IsIntegral ℤ b := by
        cases hb with
        | inl h => rw [h]; exact hr.mul hy
        | inr h => rw [h]; exact hr.mul hx
      have ha' : IsIntegral ℤ a := by
        cases ha with
        | inl h => rw [h]; exact hx
        | inr h => rw [h]; exact hy
      have h2 : IsIntegral ℤ (2 : ℂ) := by simpa using isIntegral_natCast (R := ℤ) (B := ℂ) 2
      exact (ha'.pow 2).sub (h2.mul hb')
    | (j + 3) =>
      simp only [newtonP]
      have ha' : IsIntegral ℤ a := by
        cases ha with
        | inl h => rw [h]; exact hx
        | inr h => rw [h]; exact hy
      have hb' : IsIntegral ℤ b := by
        cases hb with
        | inl h => rw [h]; exact hr.mul hy
        | inr h => rw [h]; exact hr.mul hx
      have hc' : IsIntegral ℤ c := by rw [hc]; exact hr.pow 3
      have h2' := ih (j + 2) (by omega)
      have h1' := ih (j + 1) (by omega)
      have h0' := ih j (by omega)
      exact ((ha'.mul h2').sub (hb'.mul h1')).add (hc'.mul h0')

private theorem newtonQ_integral (x y r : ℂ)
    (hx : IsIntegral ℤ x) (hy : IsIntegral ℤ y) (hr : IsIntegral ℤ r) (k : ℕ) :
    IsIntegral ℤ (newtonQ ℂ x y r k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp only [newtonQ]; exact isIntegral_zero
    | 1 => simp only [newtonQ]; exact isIntegral_one
    | 2 =>
      simp only [newtonQ]
      have h2 : IsIntegral ℤ (2 : ℂ) := by simpa using isIntegral_natCast (R := ℤ) (B := ℂ) 2
      exact (hx.add hy).add (h2.mul hr)
    | (j + 3) =>
      simp only [newtonQ]
      have hPX2 :=
        newtonP_integral x y r hx hy hr x (r * y) (r ^ 3)
          (Or.inl rfl) (Or.inl rfl) rfl (j + 2)
      have hPX1 :=
        newtonP_integral x y r hx hy hr x (r * y) (r ^ 3)
          (Or.inl rfl) (Or.inl rfl) rfl (j + 1)
      exact ((((hy.mul (ih (j+2) (by omega))).sub ((hr.mul hx).mul (ih (j+1) (by omega)))).add
        ((hr.pow 3).mul (ih j (by omega)))).add (hPX2.add (hr.mul hPX1)))

private theorem quad_integral (ρ c α : ℂ)
    (hρ : IsIntegral ℤ ρ) (hc : IsIntegral ℤ c)
    (heval : α ^ 2 - ρ * α + c = 0) :
    IsIntegral ℤ α := by
  have heval' : Polynomial.eval α
      (Polynomial.X ^ 2 - Polynomial.C ρ * Polynomial.X + Polynomial.C c : Polynomial ℂ) = 0 := by
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    linear_combination heval
  have hmonic : (Polynomial.X ^ 2 - Polynomial.C ρ * Polynomial.X + Polynomial.C c :
      Polynomial ℂ).Monic := by
    have h : (Polynomial.X ^ 2 - Polynomial.C ρ * Polynomial.X + Polynomial.C c : Polynomial ℂ)
        = Polynomial.X ^ 2 + (-Polynomial.C ρ * Polynomial.X + Polynomial.C c) := by ring
    rw [h]
    apply Polynomial.monic_X_pow_add
    compute_degree
    all_goals norm_num
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C ρ * Polynomial.X + Polynomial.C c :
      Polynomial ℂ).natDegree ≠ 0 := by
    have h : (Polynomial.X ^ 2 - Polynomial.C ρ * Polynomial.X + Polynomial.C c :
        Polynomial ℂ).natDegree = 2 := by
      have heq : (Polynomial.X ^ 2 - Polynomial.C ρ * Polynomial.X + Polynomial.C c : Polynomial ℂ)
          = Polynomial.X ^ 2 + (-Polynomial.C ρ * Polynomial.X + Polynomial.C c) := by ring
      rw [heq]
      compute_degree
      all_goals norm_num
    omega
  apply IsIntegral.of_aeval_monic_of_isIntegral_coeff hmonic hdeg (p :=
    (Polynomial.X ^ 2 - Polynomial.C ρ * Polynomial.X + Polynomial.C c : Polynomial ℂ))
  · rw [heval']
    exact isIntegral_zero
  · intro i
    cases i with
    | zero =>
      have h0 : (Polynomial.X ^ 2 - Polynomial.C ρ * Polynomial.X + Polynomial.C c :
          Polynomial ℂ).coeff 0 = c := by simp
      rw [h0]
      exact hc
    | succ n =>
      cases n with
      | zero =>
        have h1 : (Polynomial.X ^ 2 - Polynomial.C ρ * Polynomial.X + Polynomial.C c :
            Polynomial ℂ).coeff 1 = -ρ := by simp
        rw [h1]
        exact hρ.neg
      | succ m =>
        cases m with
        | zero =>
          have h2 : (Polynomial.X ^ 2 - Polynomial.C ρ * Polynomial.X + Polynomial.C c :
              Polynomial ℂ).coeff 2 = 1 := by simp
          rw [h2]
          exact isIntegral_one
        | succ k =>
          have hk : (Polynomial.X ^ 2 - Polynomial.C ρ * Polynomial.X + Polynomial.C c :
              Polynomial ℂ).coeff (k + 3) = 0 := by simp
          rw [hk]
          exact isIntegral_zero

private theorem rho_integral (S₁ S₂ R : ℤ) (γ : ℂ)
    (hroot : cubicRecurrenceRootCondition S₁ S₂ R γ) :
    IsIntegral ℤ ((R : ℂ) * (γ + γ⁻¹)) := by
  have h0 : ((R : ℂ) * (γ + γ⁻¹)) ^ 3 - (S₁ : ℂ) * ((R : ℂ) * (γ + γ⁻¹)) ^ 2
      + (S₂ : ℂ) * ((R : ℂ) * (γ + γ⁻¹))
      - (((R * S₁ ^ 2 - 2 * R * S₂ - 4 * R ^ 3 : ℤ)) : ℂ) = 0 := hroot
  push_cast at h0
  set p : Polynomial ℤ :=
    Polynomial.X ^ 3 +
      (-Polynomial.C S₁ * Polynomial.X ^ 2 + Polynomial.C S₂ * Polynomial.X
        - Polynomial.C (R * S₁ ^ 2 - 2 * R * S₂ - 4 * R ^ 3)) with hp
  have hmonic : p.Monic := by
    rw [hp]
    apply Polynomial.monic_X_pow_add
    compute_degree
    all_goals norm_num
  have hdeg : p.natDegree ≠ 0 := by
    have h : p.natDegree = 3 := by
      rw [hp]
      compute_degree
      all_goals norm_num
    omega
  apply IsIntegral.of_aeval_monic hmonic hdeg
  have haeval : (Polynomial.aeval ((R : ℂ) * (γ + γ⁻¹))) p = 0 := by
    simp only [hp, map_add, map_sub, map_neg, map_mul, map_pow,
      Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_int_eq]
    simp
    linear_combination h0
  rw [haeval]
  exact isIntegral_zero

private theorem alpha_integral (R : ℤ) (γ : ℂ) (hγ : γ ≠ 0)
    (hρ : IsIntegral ℤ ((R : ℂ) * (γ + γ⁻¹))) :
    IsIntegral ℤ ((R : ℂ) * γ) := by
  have hγinv : γ * γ⁻¹ = 1 := mul_inv_cancel₀ hγ
  have heval : ((R : ℂ) * γ) ^ 2 - ((R : ℂ) * (γ + γ⁻¹)) * ((R : ℂ) * γ)
      + (R : ℂ) ^ 2 = 0 := by
    linear_combination -((R : ℂ) ^ 2 * hγinv)
  exact quad_integral _ _ _ hρ ((isIntegral_intCast R).pow 2) heval

private theorem beta_integral (R : ℤ) (γ : ℂ) (hγ : γ ≠ 0)
    (hρ : IsIntegral ℤ ((R : ℂ) * (γ + γ⁻¹))) :
    IsIntegral ℤ ((R : ℂ) * γ⁻¹) := by
  have hγinv : γ⁻¹ * γ = 1 := inv_mul_cancel₀ hγ
  have heval : ((R : ℂ) * γ⁻¹) ^ 2 - ((R : ℂ) * (γ + γ⁻¹)) * ((R : ℂ) * γ⁻¹)
      + (R : ℂ) ^ 2 = 0 := by
    linear_combination -((R : ℂ) ^ 2 * hγinv)
  exact quad_integral _ _ _ hρ ((isIntegral_intCast R).pow 2) heval

private theorem diff_identity (g₁ g₂ g₃ R : ℂ) (k : ℕ)
    (hprod : g₁ * g₂ * g₃ = 1) :
    (R * g₁⁻¹) ^ k + (R * g₂⁻¹) ^ k + (R * g₃⁻¹) ^ k
      - ((R * g₁) ^ k + (R * g₂) ^ k + (R * g₃) ^ k)
      = R ^ k * ((1 - g₁ ^ k) * (1 - g₂ ^ k) * (1 - g₃ ^ k)) := by
  have hpk : g₁ ^ k * g₂ ^ k * g₃ ^ k = 1 := by
    rw [← mul_pow, ← mul_pow, hprod, one_pow]
  have e1 : (g₁ ^ k)⁻¹ = g₂ ^ k * g₃ ^ k := by
    apply inv_eq_of_mul_eq_one_right
    calc g₁ ^ k * (g₂ ^ k * g₃ ^ k) = g₁ ^ k * g₂ ^ k * g₃ ^ k := by ring
      _ = 1 := hpk
  have e2 : (g₂ ^ k)⁻¹ = g₃ ^ k * g₁ ^ k := by
    apply inv_eq_of_mul_eq_one_right
    calc g₂ ^ k * (g₃ ^ k * g₁ ^ k) = g₁ ^ k * g₂ ^ k * g₃ ^ k := by ring
      _ = 1 := hpk
  have e3 : (g₃ ^ k)⁻¹ = g₁ ^ k * g₂ ^ k := by
    apply inv_eq_of_mul_eq_one_right
    calc g₃ ^ k * (g₁ ^ k * g₂ ^ k) = g₁ ^ k * g₂ ^ k * g₃ ^ k := by ring
      _ = 1 := hpk
  have r1 : (R * g₁⁻¹) ^ k = R ^ k * (g₁ ^ k)⁻¹ := by rw [mul_pow, inv_pow]
  have r2 : (R * g₂⁻¹) ^ k = R ^ k * (g₂ ^ k)⁻¹ := by rw [mul_pow, inv_pow]
  have r3 : (R * g₃⁻¹) ^ k = R ^ k * (g₃ ^ k)⁻¹ := by rw [mul_pow, inv_pow]
  have s1 : (R * g₁) ^ k = R ^ k * g₁ ^ k := by rw [mul_pow]
  have s2 : (R * g₂) ^ k = R ^ k * g₂ ^ k := by rw [mul_pow]
  have s3 : (R * g₃) ^ k = R ^ k * g₃ ^ k := by rw [mul_pow]
  rw [r1, r2, r3, s1, s2, s3, e1, e2, e3]
  have hexpand : (1 - g₁ ^ k) * (1 - g₂ ^ k) * (1 - g₃ ^ k)
      = 1 - (g₁ ^ k + g₂ ^ k + g₃ ^ k)
        + (g₁ ^ k * g₂ ^ k + g₂ ^ k * g₃ ^ k + g₃ ^ k * g₁ ^ k)
        - g₁ ^ k * g₂ ^ k * g₃ ^ k := by ring
  rw [hexpand, hpk]
  ring

private theorem sum_identity (g₁ g₂ g₃ R : ℂ) (k : ℕ)
    (hprod : g₁ * g₂ * g₃ = 1) (Wk : ℤ)
    (hW : ((Wk : ℤ) : ℂ) = R ^ k * ((1 + g₁ ^ k) * (1 + g₂ ^ k) * (1 + g₃ ^ k) - 2)) :
    (R * g₁) ^ k + (R * g₂) ^ k + (R * g₃) ^ k
      + ((R * g₁⁻¹) ^ k + (R * g₂⁻¹) ^ k + (R * g₃⁻¹) ^ k)
      = ((Wk : ℤ) : ℂ) := by
  have hpk : g₁ ^ k * g₂ ^ k * g₃ ^ k = 1 := by
    rw [← mul_pow, ← mul_pow, hprod, one_pow]
  have e1 : (g₁ ^ k)⁻¹ = g₂ ^ k * g₃ ^ k := by
    apply inv_eq_of_mul_eq_one_right
    calc g₁ ^ k * (g₂ ^ k * g₃ ^ k) = g₁ ^ k * g₂ ^ k * g₃ ^ k := by ring
      _ = 1 := hpk
  have e2 : (g₂ ^ k)⁻¹ = g₃ ^ k * g₁ ^ k := by
    apply inv_eq_of_mul_eq_one_right
    calc g₂ ^ k * (g₃ ^ k * g₁ ^ k) = g₁ ^ k * g₂ ^ k * g₃ ^ k := by ring
      _ = 1 := hpk
  have e3 : (g₃ ^ k)⁻¹ = g₁ ^ k * g₂ ^ k := by
    apply inv_eq_of_mul_eq_one_right
    calc g₃ ^ k * (g₁ ^ k * g₂ ^ k) = g₁ ^ k * g₂ ^ k * g₃ ^ k := by ring
      _ = 1 := hpk
  have r1 : (R * g₁⁻¹) ^ k = R ^ k * (g₁ ^ k)⁻¹ := by rw [mul_pow, inv_pow]
  have r2 : (R * g₂⁻¹) ^ k = R ^ k * (g₂ ^ k)⁻¹ := by rw [mul_pow, inv_pow]
  have r3 : (R * g₃⁻¹) ^ k = R ^ k * (g₃ ^ k)⁻¹ := by rw [mul_pow, inv_pow]
  have s1 : (R * g₁) ^ k = R ^ k * g₁ ^ k := by rw [mul_pow]
  have s2 : (R * g₂) ^ k = R ^ k * g₂ ^ k := by rw [mul_pow]
  have s3 : (R * g₃) ^ k = R ^ k * g₃ ^ k := by rw [mul_pow]
  rw [r1, r2, r3, s1, s2, s3, e1, e2, e3, hW]
  have hexpand : (1 + g₁ ^ k) * (1 + g₂ ^ k) * (1 + g₃ ^ k)
      = 1 + (g₁ ^ k + g₂ ^ k + g₃ ^ k)
        + (g₁ ^ k * g₂ ^ k + g₂ ^ k * g₃ ^ k + g₃ ^ k * g₁ ^ k)
        + g₁ ^ k * g₂ ^ k * g₃ ^ k := by ring
  rw [hexpand, hpk]
  ring

private theorem pairs_identity (g₁ g₂ g₃ R : ℂ) (n : ℕ)
    (hprod : g₁ * g₂ * g₃ = 1) :
    (R * g₁) ^ n * (R * g₂) ^ n + (R * g₂) ^ n * (R * g₃) ^ n + (R * g₃) ^ n * (R * g₁) ^ n
      = R ^ n * ((R * g₁⁻¹) ^ n + (R * g₂⁻¹) ^ n + (R * g₃⁻¹) ^ n) := by
  have hpk : g₁ ^ n * g₂ ^ n * g₃ ^ n = 1 := by
    rw [← mul_pow, ← mul_pow, hprod, one_pow]
  have e12 : g₁ ^ n * g₂ ^ n = (g₃ ^ n)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc g₁ ^ n * g₂ ^ n * g₃ ^ n = g₁ ^ n * g₂ ^ n * g₃ ^ n := by ring
      _ = 1 := hpk
  have e23 : g₂ ^ n * g₃ ^ n = (g₁ ^ n)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc g₂ ^ n * g₃ ^ n * g₁ ^ n = g₁ ^ n * g₂ ^ n * g₃ ^ n := by ring
      _ = 1 := hpk
  have e31 : g₃ ^ n * g₁ ^ n = (g₂ ^ n)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc g₃ ^ n * g₁ ^ n * g₂ ^ n = g₁ ^ n * g₂ ^ n * g₃ ^ n := by ring
      _ = 1 := hpk
  have s12 : (R * g₁) ^ n * (R * g₂) ^ n = R ^ n * R ^ n * (g₁ ^ n * g₂ ^ n) := by
    rw [mul_pow, mul_pow]; ring
  have s23 : (R * g₂) ^ n * (R * g₃) ^ n = R ^ n * R ^ n * (g₂ ^ n * g₃ ^ n) := by
    rw [mul_pow, mul_pow]; ring
  have s31 : (R * g₃) ^ n * (R * g₁) ^ n = R ^ n * R ^ n * (g₃ ^ n * g₁ ^ n) := by
    rw [mul_pow, mul_pow]; ring
  have t1 : (R * g₁⁻¹) ^ n = R ^ n * (g₁ ^ n)⁻¹ := by rw [mul_pow, inv_pow]
  have t2 : (R * g₂⁻¹) ^ n = R ^ n * (g₂ ^ n)⁻¹ := by rw [mul_pow, inv_pow]
  have t3 : (R * g₃⁻¹) ^ n = R ^ n * (g₃ ^ n)⁻¹ := by rw [mul_pow, inv_pow]
  rw [s12, s23, s31, t1, t2, t3, e12, e23, e31]
  ring

private theorem triple_identity (g₁ g₂ g₃ R : ℂ) (n : ℕ)
    (hprod : g₁ * g₂ * g₃ = 1) :
    (R * g₁) ^ n * ((R * g₂) ^ n * (R * g₃) ^ n) = ((R ^ n) ^ 3) := by
  have hpk : g₁ ^ n * g₂ ^ n * g₃ ^ n = 1 := by
    rw [← mul_pow, ← mul_pow, hprod, one_pow]
  have s1 : (R * g₁) ^ n = R ^ n * g₁ ^ n := by rw [mul_pow]
  have s2 : (R * g₂) ^ n = R ^ n * g₂ ^ n := by rw [mul_pow]
  have s3 : (R * g₃) ^ n = R ^ n * g₃ ^ n := by rw [mul_pow]
  rw [s1, s2, s3]
  linear_combination (R ^ n) ^ 3 * hpk

private theorem int_dvd_of_complex (d : ℕ) (z : ℤ) (q : ℂ)
    (hqInt : IsIntegral ℤ q) (hdiv : ((z : ℤ) : ℂ) = ((d : ℕ) : ℂ) * q) :
    (d : ℤ) ∣ z := by
  by_cases hd : d = 0
  · subst hd
    simp only [Nat.cast_zero, zero_mul] at hdiv
    have hzz : ((z : ℤ) : ℂ) = ((0 : ℤ) : ℂ) := by simpa using hdiv
    have hz : z = 0 := Int.cast_injective hzz
    subst hz
    exact dvd_refl 0
  · have hdC : ((d : ℕ) : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact hd
    have hqeq : q = ((z : ℤ) : ℂ) / ((d : ℕ) : ℂ) := by
      rw [hdiv]
      field_simp
    have hcast : ((((z : ℚ) / (d : ℚ)) : ℚ) : ℂ) = ((z : ℤ) : ℂ) / ((d : ℕ) : ℂ) := by
      push_cast
      ring
    have hqrat : q ∈ Set.range (Rat.cast : ℚ → ℂ) := by
      refine ⟨(z : ℚ) / (d : ℚ), ?_⟩
      rw [hqeq, hcast]
    obtain ⟨k, hk⟩ := hqInt.mem_range_ratCast_iff.mp hqrat
    have hzk : ((z : ℤ) : ℂ) = ((((d : ℤ) * k : ℤ)) : ℂ) := by
      rw [hdiv, ← hk]
      push_cast
      ring
    have hzz : z = (d : ℤ) * k := Int.cast_injective hzk
    exact ⟨k, hzz⟩

private theorem int_dvd_of_complex_int (d z : ℤ) (q : ℂ)
    (hqInt : IsIntegral ℤ q) (hdiv : ((z : ℤ) : ℂ) = ((d : ℤ) : ℂ) * q) :
    d ∣ z := by
  by_cases hd : d = 0
  · subst hd
    simp only [Int.cast_zero, zero_mul] at hdiv
    have hzz : ((z : ℤ) : ℂ) = ((0 : ℤ) : ℂ) := by simpa using hdiv
    have hz : z = 0 := Int.cast_injective hzz
    subst hz
    exact dvd_refl 0
  · have hdC : ((d : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hd
    have hqeq : q = ((z : ℤ) : ℂ) / ((d : ℤ) : ℂ) := by
      rw [hdiv]
      field_simp
    have hcast : ((((z : ℚ) / (d : ℚ)) : ℚ) : ℂ)
        = ((z : ℤ) : ℂ) / ((d : ℤ) : ℂ) := by
      push_cast
      ring
    have hqrat : q ∈ Set.range (Rat.cast : ℚ → ℂ) := by
      refine ⟨(z : ℚ) / (d : ℚ), ?_⟩
      rw [hqeq, hcast]
    obtain ⟨k, hk⟩ := hqInt.mem_range_ratCast_iff.mp hqrat
    have hzk : ((z : ℤ) : ℂ) = ((((d * k : ℤ))) : ℂ) := by
      rw [hdiv, ← hk]
      push_cast
      ring
    have hzz : z = d * k := Int.cast_injective hzk
    exact ⟨k, hzz⟩

private theorem double_newtonP (S : Type*) [CommRing S] (X rr : S)
    (h1 : 2 * X = 6 * rr) (m : ℕ) :
    2 * newtonP S X (rr * X) (rr ^ 3) m = 6 * rr ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 =>
      simp only [newtonP]
      ring
    | 1 =>
      simp only [newtonP]
      linear_combination h1
    | 2 =>
      simp only [newtonP]
      linear_combination X * h1 + rr * h1
    | (j + 3) =>
      have ih2 := ih (j + 2) (by omega)
      have ih1 := ih (j + 1) (by omega)
      have ih0 := ih j (by omega)
      simp only [newtonP]
      linear_combination X * ih2 - rr * X * ih1 + rr ^ 3 * ih0

private theorem W_aux (x y rr : ℂ)
    (hx : IsIntegral ℤ x) (hy : IsIntegral ℤ y) (hrr : IsIntegral ℤ rr)
    (d : ℕ) (u v : ℂ) (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v)
    (hYX : y - x = ((d : ℕ) : ℂ) * u)
    (hXY : x + y - 6 * rr = ((d : ℕ) : ℂ) * v) (m : ℕ) :
    ∃ q : ℂ, IsIntegral ℤ q ∧
      (newtonP ℂ x (rr * y) (rr ^ 3) m + newtonP ℂ y (rr * x) (rr ^ 3) m
        - 6 * rr ^ m = ((d : ℕ) : ℂ) * q) := by
  let A := ↥(integralClosure ℤ ℂ)
  have hxmem : x ∈ integralClosure ℤ ℂ := (mem_integralClosure_iff ℤ ℂ).mpr hx
  have hymem : y ∈ integralClosure ℤ ℂ := (mem_integralClosure_iff ℤ ℂ).mpr hy
  have hrrmem : rr ∈ integralClosure ℤ ℂ := (mem_integralClosure_iff ℤ ℂ).mpr hrr
  have humem : u ∈ integralClosure ℤ ℂ := (mem_integralClosure_iff ℤ ℂ).mpr hu
  have hvmem : v ∈ integralClosure ℤ ℂ := (mem_integralClosure_iff ℤ ℂ).mpr hv
  have hdmem : ((d : ℕ) : ℂ) ∈ integralClosure ℤ ℂ :=
    (mem_integralClosure_iff ℤ ℂ).mpr (isIntegral_natCast d)
  let xA : A := ⟨x, hxmem⟩
  let yA : A := ⟨y, hymem⟩
  let rrA : A := ⟨rr, hrrmem⟩
  let uA : A := ⟨u, humem⟩
  let vA : A := ⟨v, hvmem⟩
  let dA : A := ⟨((d : ℕ) : ℂ), hdmem⟩
  have hYXA : yA - xA = dA * uA := by
    apply Subtype.ext
    change y - x = ((d : ℕ) : ℂ) * u
    exact hYX
  have hXYA : xA + yA - 6 * rrA = dA * vA := by
    apply Subtype.ext
    change x + y - 6 * rr = ((d : ℕ) : ℂ) * v
    exact hXY
  let I : Ideal A := Ideal.span {dA}
  let π : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hYeqX : π yA = π xA := by
    have hmem : yA - xA ∈ I := by rw [hYXA]; exact Ideal.mem_span_singleton.mpr ⟨uA, rfl⟩
    have h0 : π (yA - xA) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    have h0' : π yA - π xA = 0 := by simpa [map_sub] using h0
    exact sub_eq_zero.mp h0'
  have hsum0 : π xA + π yA - 6 * π rrA = 0 := by
    have hmem : xA + yA - 6 * rrA ∈ I := by rw [hXYA]; exact Ideal.mem_span_singleton.mpr ⟨vA, rfl⟩
    have h0 : π (xA + yA - 6 * rrA) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    have h0' : π xA + π yA - π (6 : A) * π rrA = 0 := by simpa [map_sub, map_add, map_mul] using h0
    have h6 : π (6 : A) = 6 := map_ofNat π 6
    rw [h6] at h0'
    exact h0'
  have h2X : 2 * π xA = 6 * π rrA := by
    rw [hYeqX] at hsum0
    linear_combination hsum0
  have hPXmap : π (newtonP A xA (rrA * yA) (rrA ^ 3) m)
      = newtonP (A ⧸ I) (π xA) (π rrA * π yA) ((π rrA) ^ 3) m := by
    rw [newtonP_map, map_mul, map_pow]
  have hPYmap : π (newtonP A yA (rrA * xA) (rrA ^ 3) m)
      = newtonP (A ⧸ I) (π yA) (π rrA * π xA) ((π rrA) ^ 3) m := by
    rw [newtonP_map, map_mul, map_pow]
  set S : A :=
    newtonP A xA (rrA * yA) (rrA ^ 3) m + newtonP A yA (rrA * xA) (rrA ^ 3) m
      - 6 * rrA ^ m with hS_def
  have hπS : π S = 0 := by
    have hD := double_newtonP (A ⧸ I) (π xA) (π rrA) h2X m
    have e : π S = newtonP (A ⧸ I) (π xA) (π rrA * π yA) ((π rrA) ^ 3) m
        + newtonP (A ⧸ I) (π yA) (π rrA * π xA) ((π rrA) ^ 3) m
        - 6 * (π rrA) ^ m := by
      rw [hS_def, map_sub, map_add, map_mul, hPXmap, hPYmap, map_pow, map_ofNat]
    rw [e, hYeqX]
    linear_combination hD
  have hSmem : S ∈ I := (Ideal.Quotient.eq_zero_iff_mem).mp hπS
  rw [Ideal.mem_span_singleton] at hSmem
  obtain ⟨qA, hqA⟩ := hSmem
  let val : A →+* ℂ := (integralClosure ℤ ℂ).val
  have hvalS : val S = newtonP ℂ x (rr * y) (rr ^ 3) m + newtonP ℂ y (rr * x) (rr ^ 3) m
      - 6 * rr ^ m := by
    rw [hS_def, map_sub, map_add, map_mul, newtonP_map, newtonP_map, map_pow, map_ofNat]
    rfl
  have hvald : val dA = ((d : ℕ) : ℂ) := rfl
  have hqInt : IsIntegral ℤ (val qA) := (mem_integralClosure_iff ℤ ℂ).mp qA.2
  have hvaleq : val S = val dA * val qA := by rw [hqA, map_mul]
  rw [hvalS, hvald] at hvaleq
  exact ⟨val qA, hqInt, hvaleq⟩

/--
**Divisibility of the cubic-recurrence discriminants.** Let $S_1, S_2, R$ be integers, let $U$
and $W$ be integer sequences forming a cubic recurrence pair for $(S_1, S_2, R)$, and let
$D_n = \gcd(W_n - 6R^n, U_n)$ be their discriminant sequence. Then for all integers $n \ge 1$
and $m \ge 1$, $D_n$ divides $D_{nm}$.

Proves `Wanted` entry `cubicRecurrenceDiscriminant_dvd_mul`.

Source: E. L. Roettger and H. C. Williams, "Some Arithmetic Properties of Certain
Sequences", Journal of Integer Sequences 18 (2015), Article 15.6.2, Theorem `Dndivis`,
line 269, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Roettger/roettger4.tex>.
-/
theorem cubicRecurrenceDiscriminant_dvd_mul
    (S₁ S₂ R : ℤ) (U W : ℕ → ℤ)
    (hseq : IsCubicRecurrencePair S₁ S₂ R U W)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    cubicRecurrenceDiscriminant R U W n ∣
      cubicRecurrenceDiscriminant R U W (n * m) := by
  obtain ⟨γ₁, γ₂, γ₃, h11, h22, h33, h12, h23, h31, hprod, hr1, hr2, hr3, hU0, hUeq, hWeq⟩ := hseq
  have hg10 : γ₁ ≠ 0 := by intro h; rw [h] at hprod; simp at hprod
  have hg20 : γ₂ ≠ 0 := by intro h; rw [h] at hprod; simp at hprod
  have hg30 : γ₃ ≠ 0 := by intro h; rw [h] at hprod; simp at hprod
  have f1 : (1 : ℂ) - γ₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h11)
  have f2 : (1 : ℂ) - γ₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h22)
  have f3 : (1 : ℂ) - γ₃ ≠ 0 := sub_ne_zero.mpr (Ne.symm h33)
  have hδ : (1 - γ₁) * (1 - γ₂) * (1 - γ₃) ≠ 0 := mul_ne_zero (mul_ne_zero f1 f2) f3
  by_cases hR0 : R = 0
  · subst hR0
    have hW0 : ∀ k : ℕ, 1 ≤ k → W k = 0 := by
      intro k hk
      have hWk := hWeq k
      simp only [Int.cast_zero, zero_pow (by omega : k ≠ 0), zero_mul] at hWk
      have hzz : ((W k : ℤ) : ℂ) = ((0 : ℤ) : ℂ) := by simpa using hWk
      exact Int.cast_injective hzz
    have hU1 : U 1 = 1 := by
      have h1 := hUeq 1 (le_refl 1)
      simp only [pow_one, Int.cast_zero, Nat.sub_self, pow_zero,
        one_mul] at h1
      have hbase : ((U 1 : ℤ) : ℂ) * ((1 - γ₁) * (1 - γ₂) * (1 - γ₃))
          = 1 * ((1 - γ₁) * (1 - γ₂) * (1 - γ₃)) := by
        linear_combination h1
      have hU1c : ((U 1 : ℤ) : ℂ) = 1 := mul_right_cancel₀ hδ hbase
      have hzz : ((U 1 : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by simpa using hU1c
      exact Int.cast_injective hzz
    have hUge2 : ∀ k : ℕ, 2 ≤ k → U k = 0 := by
      intro k hk
      have h1 := hUeq k (by omega)
      have hk1 : k - 1 ≠ 0 := by omega
      simp only [Int.cast_zero, zero_pow hk1, zero_mul] at h1
      have hbase : ((U k : ℤ) : ℂ) * ((1 - γ₁) * (1 - γ₂) * (1 - γ₃))
          = 0 * ((1 - γ₁) * (1 - γ₂) * (1 - γ₃)) := by
        linear_combination h1
      have hUk0 : ((U k : ℤ) : ℂ) = 0 := mul_right_cancel₀ hδ hbase
      have hzz : ((U k : ℤ) : ℂ) = ((0 : ℤ) : ℂ) := by simpa using hUk0
      exact Int.cast_injective hzz
    have hD1 : cubicRecurrenceDiscriminant 0 U W 1 = 1 := by
      unfold cubicRecurrenceDiscriminant
      rw [hW0 1 (le_refl 1), hU1]
      simp
    have hDge2 : ∀ k : ℕ, 2 ≤ k → cubicRecurrenceDiscriminant 0 U W k = 0 := by
      intro k hk
      unfold cubicRecurrenceDiscriminant
      rw [hW0 k (by omega), hUge2 k hk]
      have hk0 : k ≠ 0 := by omega
      have h0k : (0 : ℤ) ^ k = 0 := zero_pow hk0
      rw [h0k]
      simp
    by_cases hn1 : n = 1
    · subst hn1
      rw [hD1]
      exact Nat.one_dvd _
    · have hn2 : 2 ≤ n := by omega
      have hnm2 : 2 ≤ n * m := by
        have h := Nat.mul_le_mul hn2 hm
        simpa using h
      rw [hDge2 n hn2, hDge2 (n * m) hnm2]
  · have hRc0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR0
    set δ : ℂ := (1 - γ₁) * (1 - γ₂) * (1 - γ₃) with hδdef
    set K : ℂ := (R : ℂ) * δ with hKdef
    have hK0 : K ≠ 0 := by
      rw [hKdef]
      exact mul_ne_zero hRc0 hδ
    have hρ1 := rho_integral S₁ S₂ R γ₁ hr1
    have hρ2 := rho_integral S₁ S₂ R γ₂ hr2
    have hρ3 := rho_integral S₁ S₂ R γ₃ hr3
    have hα1 := alpha_integral R γ₁ hg10 hρ1
    have hα2 := alpha_integral R γ₂ hg20 hρ2
    have hα3 := alpha_integral R γ₃ hg30 hρ3
    have hβ1 := beta_integral R γ₁ hg10 hρ1
    have hβ2 := beta_integral R γ₂ hg20 hρ2
    have hβ3 := beta_integral R γ₃ hg30 hρ3
    have hRint : IsIntegral ℤ (R : ℂ) := isIntegral_intCast R
    have hdiff1 := diff_identity γ₁ γ₂ γ₃ (R : ℂ) 1 hprod
    simp only [pow_one] at hdiff1
    have hKeq : K = ((R : ℂ) * γ₁⁻¹ + (R : ℂ) * γ₂⁻¹ + (R : ℂ) * γ₃⁻¹)
        - ((R : ℂ) * γ₁ + (R : ℂ) * γ₂ + (R : ℂ) * γ₃) := by
      rw [hKdef, hδdef, ← hdiff1]
    have hx1 : IsIntegral ℤ ((R : ℂ) * γ₁ + (R : ℂ) * γ₂ + (R : ℂ) * γ₃) :=
      (hα1.add hα2).add hα3
    have hy1 : IsIntegral ℤ
        ((R : ℂ) * γ₁⁻¹ + (R : ℂ) * γ₂⁻¹ + (R : ℂ) * γ₃⁻¹) :=
      (hβ1.add hβ2).add hβ3
    have hKint : IsIntegral ℤ K := by
      rw [hKeq]
      exact hy1.sub hx1
    set x : ℂ :=
      ((R : ℂ) * γ₁) ^ n + ((R : ℂ) * γ₂) ^ n + ((R : ℂ) * γ₃) ^ n with hxdef
    set y : ℂ := ((R : ℂ) * γ₁⁻¹) ^ n + ((R : ℂ) * γ₂⁻¹) ^ n
      + ((R : ℂ) * γ₃⁻¹) ^ n with hydef
    set rr : ℂ := (R : ℂ) ^ n with hrrdef
    have hx : IsIntegral ℤ x := by
      rw [hxdef]
      exact ((hα1.pow n).add (hα2.pow n)).add (hα3.pow n)
    have hy : IsIntegral ℤ y := by
      rw [hydef]
      exact ((hβ1.pow n).add (hβ2.pow n)).add (hβ3.pow n)
    have hrr : IsIntegral ℤ rr := by
      rw [hrrdef]
      exact hRint.pow n
    have hprod_inv : γ₁⁻¹ * γ₂⁻¹ * γ₃⁻¹ = 1 := by
      have h2 : (γ₁ * γ₂ * γ₃)⁻¹ = γ₁⁻¹ * γ₂⁻¹ * γ₃⁻¹ := by
        rw [mul_inv, mul_inv]
      rw [← h2, hprod, inv_one]
    have h1x : ((R : ℂ) * γ₁) ^ n + ((R : ℂ) * γ₂) ^ n
        + ((R : ℂ) * γ₃) ^ n = x := hxdef.symm
    have h2x : ((R : ℂ) * γ₁) ^ n * (((R : ℂ) * γ₂) ^ n)
          + ((R : ℂ) * γ₂) ^ n * (((R : ℂ) * γ₃) ^ n)
          + ((R : ℂ) * γ₃) ^ n * (((R : ℂ) * γ₁) ^ n)
        = rr * y := by
      have h := pairs_identity γ₁ γ₂ γ₃ (R : ℂ) n hprod
      rw [← hrrdef, ← hydef] at h
      exact h
    have h3x : ((R : ℂ) * γ₁) ^ n * (((R : ℂ) * γ₂) ^ n)
          * (((R : ℂ) * γ₃) ^ n) = rr ^ 3 := by
      have h := triple_identity γ₁ γ₂ γ₃ (R : ℂ) n hprod
      have hassoc : ((R : ℂ) * γ₁) ^ n * (((R : ℂ) * γ₂) ^ n)
              * (((R : ℂ) * γ₃) ^ n)
          = ((R : ℂ) * γ₁) ^ n
            * ((((R : ℂ) * γ₂) ^ n) * (((R : ℂ) * γ₃) ^ n)) := by
        ring
      rw [hassoc, h, hrrdef]
    have h1y : ((R : ℂ) * γ₁⁻¹) ^ n + ((R : ℂ) * γ₂⁻¹) ^ n
        + ((R : ℂ) * γ₃⁻¹) ^ n = y := hydef.symm
    have h2y : ((R : ℂ) * γ₁⁻¹) ^ n * (((R : ℂ) * γ₂⁻¹) ^ n)
          + ((R : ℂ) * γ₂⁻¹) ^ n * (((R : ℂ) * γ₃⁻¹) ^ n)
          + ((R : ℂ) * γ₃⁻¹) ^ n * (((R : ℂ) * γ₁⁻¹) ^ n)
        = rr * x := by
      have h :=
        pairs_identity (γ₁⁻¹) (γ₂⁻¹) (γ₃⁻¹) (R : ℂ) n hprod_inv
      simp only [inv_inv] at h
      rw [← hrrdef, ← hxdef] at h
      exact h
    have h3y : ((R : ℂ) * γ₁⁻¹) ^ n * (((R : ℂ) * γ₂⁻¹) ^ n)
          * (((R : ℂ) * γ₃⁻¹) ^ n) = rr ^ 3 := by
      have h :=
        triple_identity (γ₁⁻¹) (γ₂⁻¹) (γ₃⁻¹) (R : ℂ) n hprod_inv
      have hassoc : ((R : ℂ) * γ₁⁻¹) ^ n * (((R : ℂ) * γ₂⁻¹) ^ n)
              * (((R : ℂ) * γ₃⁻¹) ^ n)
          = ((R : ℂ) * γ₁⁻¹) ^ n
            * ((((R : ℂ) * γ₂⁻¹) ^ n) * (((R : ℂ) * γ₃⁻¹) ^ n)) := by
        ring
      rw [hassoc, h, hrrdef]
    have hPx : ∀ k : ℕ,
        newtonP ℂ x (rr * y) (rr ^ 3) k
          = ((R : ℂ) * γ₁) ^ (n * k) + ((R : ℂ) * γ₂) ^ (n * k)
            + ((R : ℂ) * γ₃) ^ (n * k) := by
      intro k
      have h := newtonP_eq_sum ℂ (((R : ℂ) * γ₁) ^ n)
        (((R : ℂ) * γ₂) ^ n) (((R : ℂ) * γ₃) ^ n) x (rr * y) (rr ^ 3)
        h1x h2x h3x k
      have e1 : ((((R : ℂ) * γ₁) ^ n) ^ k)
          = ((R : ℂ) * γ₁) ^ (n * k) := by
        rw [pow_mul]
      have e2 : ((((R : ℂ) * γ₂) ^ n) ^ k)
          = ((R : ℂ) * γ₂) ^ (n * k) := by
        rw [pow_mul]
      have e3 : ((((R : ℂ) * γ₃) ^ n) ^ k)
          = ((R : ℂ) * γ₃) ^ (n * k) := by
        rw [pow_mul]
      rw [e1, e2, e3] at h
      exact h
    have hPy : ∀ k : ℕ,
        newtonP ℂ y (rr * x) (rr ^ 3) k
          = ((R : ℂ) * γ₁⁻¹) ^ (n * k) + ((R : ℂ) * γ₂⁻¹) ^ (n * k)
            + ((R : ℂ) * γ₃⁻¹) ^ (n * k) := by
      intro k
      have h := newtonP_eq_sum ℂ (((R : ℂ) * γ₁⁻¹) ^ n)
        (((R : ℂ) * γ₂⁻¹) ^ n) (((R : ℂ) * γ₃⁻¹) ^ n) y (rr * x)
        (rr ^ 3) h1y h2y h3y k
      have e1 : ((((R : ℂ) * γ₁⁻¹) ^ n) ^ k)
          = ((R : ℂ) * γ₁⁻¹) ^ (n * k) := by
        rw [pow_mul]
      have e2 : ((((R : ℂ) * γ₂⁻¹) ^ n) ^ k)
          = ((R : ℂ) * γ₂⁻¹) ^ (n * k) := by
        rw [pow_mul]
      have e3 : ((((R : ℂ) * γ₃⁻¹) ^ n) ^ k)
          = ((R : ℂ) * γ₃⁻¹) ^ (n * k) := by
        rw [pow_mul]
      rw [e1, e2, e3] at h
      exact h
    have hdiff_eq : ∀ k : ℕ, 1 ≤ k →
        ((((R : ℂ) * γ₁⁻¹) ^ k + ((R : ℂ) * γ₂⁻¹) ^ k
            + ((R : ℂ) * γ₃⁻¹) ^ k)
          - (((R : ℂ) * γ₁) ^ k + ((R : ℂ) * γ₂) ^ k
            + ((R : ℂ) * γ₃) ^ k))
          = K * ((U k : ℤ) : ℂ) := by
      intro k hk
      have hdiff := diff_identity γ₁ γ₂ γ₃ (R : ℂ) k hprod
      have hU := hUeq k hk
      have hk' : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
      have hRpow : (R : ℂ) ^ k = (R : ℂ) ^ (k - 1) * (R : ℂ) := by
        conv_lhs => rw [hk']
        rw [pow_succ]
      calc ((((R : ℂ) * γ₁⁻¹) ^ k + ((R : ℂ) * γ₂⁻¹) ^ k
              + ((R : ℂ) * γ₃⁻¹) ^ k)
            - (((R : ℂ) * γ₁) ^ k + ((R : ℂ) * γ₂) ^ k
              + ((R : ℂ) * γ₃) ^ k))
          = (R : ℂ) ^ k * (((1 - γ₁ ^ k) * (1 - γ₂ ^ k))
            * (1 - γ₃ ^ k)) := hdiff
        _ = ((R : ℂ) ^ (k - 1) * (R : ℂ))
            * (((1 - γ₁ ^ k) * (1 - γ₂ ^ k)) * (1 - γ₃ ^ k)) := by
          rw [hRpow]
        _ = (R : ℂ) * (((R : ℂ) ^ (k - 1))
            * (((1 - γ₁ ^ k) * (1 - γ₂ ^ k)) * (1 - γ₃ ^ k))) := by
          ring
        _ = (R : ℂ) * (((U k : ℤ) : ℂ)
            * (((1 - γ₁) * (1 - γ₂)) * (1 - γ₃))) := by
          rw [← hU]
        _ = K * ((U k : ℤ) : ℂ) := by
          rw [hKdef, hδdef]
          ring
    have hnm_pos : 1 ≤ n * m := Nat.mul_pos hn hm
    have hYX : y - x = K * ((U n : ℤ) : ℂ) := by
      rw [hydef, hxdef]
      exact hdiff_eq n hn
    have hQ := newtonQ_diff ℂ x y rr m
    have hPxm := hPx m
    have hPym := hPy m
    have hdiff_nm : newtonP ℂ y (rr * x) (rr ^ 3) m
          - newtonP ℂ x (rr * y) (rr ^ 3) m
        = K * ((U (n * m) : ℤ) : ℂ) := by
      rw [hPym, hPxm]
      exact hdiff_eq (n * m) hnm_pos
    have hQm_int := newtonQ_integral x y rr hx hy hrr m
    have hcancel : ((U (n * m) : ℤ) : ℂ)
        = ((U n : ℤ) : ℂ) * newtonQ ℂ x y rr m := by
      have h1 : K * ((U (n * m) : ℤ) : ℂ)
          = K * (((U n : ℤ) : ℂ) * newtonQ ℂ x y rr m) := by
        calc K * ((U (n * m) : ℤ) : ℂ)
            = newtonP ℂ y (rr * x) (rr ^ 3) m
              - newtonP ℂ x (rr * y) (rr ^ 3) m := hdiff_nm.symm
          _ = (y - x) * newtonQ ℂ x y rr m := hQ
          _ = (K * ((U n : ℤ) : ℂ)) * newtonQ ℂ x y rr m := by
            rw [hYX]
          _ = K * (((U n : ℤ) : ℂ) * newtonQ ℂ x y rr m) := by
            ring
      exact mul_left_cancel₀ hK0 h1
    have hUdiv_int : U n ∣ U (n * m) :=
      int_dvd_of_complex_int (U n) (U (n * m))
        (newtonQ ℂ x y rr m) hQm_int hcancel
    have hUdiv_nat : (U n).natAbs ∣ (U (n * m)).natAbs :=
      Int.natAbs_dvd_natAbs.mpr hUdiv_int
    have hxyWn : x + y = ((W n : ℤ) : ℂ) := by
      rw [hxdef, hydef]
      exact sum_identity γ₁ γ₂ γ₃ (R : ℂ) n hprod (W n) (hWeq n)
    have hPPWnm : newtonP ℂ x (rr * y) (rr ^ 3) m
          + newtonP ℂ y (rr * x) (rr ^ 3) m
        = ((W (n * m) : ℤ) : ℂ) := by
      rw [hPxm, hPym]
      exact sum_identity γ₁ γ₂ γ₃ (R : ℂ) (n * m) hprod (W (n * m))
        (hWeq (n * m))
    set d : ℕ := cubicRecurrenceDiscriminant R U W n with hddef
    have hd_left : d ∣ (W n - 6 * R ^ n).natAbs := by
      rw [hddef]
      unfold cubicRecurrenceDiscriminant
      exact Nat.gcd_dvd_left _ _
    have hd_right : d ∣ (U n).natAbs := by
      rw [hddef]
      unfold cubicRecurrenceDiscriminant
      exact Nat.gcd_dvd_right _ _
    have hdvd_Un : (d : ℤ) ∣ U n := Int.ofNat_dvd_left.mpr hd_right
    have hdvd_W : (d : ℤ) ∣ W n - 6 * R ^ n :=
      Int.ofNat_dvd_left.mpr hd_left
    obtain ⟨t1, ht1⟩ := hdvd_Un
    obtain ⟨t2, ht2⟩ := hdvd_W
    have hu_int : IsIntegral ℤ (K * ((t1 : ℤ) : ℂ)) :=
      hKint.mul (isIntegral_intCast t1)
    have hv_int : IsIntegral ℤ ((t2 : ℤ) : ℂ) := isIntegral_intCast t2
    have hYX_d : y - x = ((d : ℕ) : ℂ) * (K * ((t1 : ℤ) : ℂ)) := by
      rw [hYX, ht1]
      push_cast
      ring
    have hXY_d : x + y - 6 * rr = ((d : ℕ) : ℂ) * ((t2 : ℤ) : ℂ) := by
      have h1 : x + y - 6 * rr = ((W n - 6 * R ^ n : ℤ) : ℂ) := by
        rw [hxyWn, hrrdef]
        push_cast
        ring
      rw [h1, ht2]
      push_cast
      ring
    obtain ⟨q, hq_int, hq_eq⟩ := W_aux x y rr hx hy hrr d
      (K * ((t1 : ℤ) : ℂ)) ((t2 : ℤ) : ℂ) hu_int hv_int hYX_d hXY_d m
    have hrrm : rr ^ m = ((R ^ (n * m) : ℤ) : ℂ) := by
      rw [hrrdef]
      push_cast
      rw [pow_mul]
    have hWnm_eq : ((W (n * m) - 6 * R ^ (n * m) : ℤ) : ℂ)
        = newtonP ℂ x (rr * y) (rr ^ 3) m
          + newtonP ℂ y (rr * x) (rr ^ 3) m
          - 6 * rr ^ m := by
      rw [hPPWnm, hrrm]
      push_cast
      ring
    have hdiv_W : ((W (n * m) - 6 * R ^ (n * m) : ℤ) : ℂ)
        = ((d : ℕ) : ℂ) * q := by
      rw [hWnm_eq]
      exact hq_eq
    have hdvd_Wnm : (d : ℤ) ∣ W (n * m) - 6 * R ^ (n * m) :=
      int_dvd_of_complex d _ q hq_int hdiv_W
    have hdvd_Wnm_nat : d ∣ (W (n * m) - 6 * R ^ (n * m)).natAbs :=
      Int.ofNat_dvd_left.mp hdvd_Wnm
    have hdvd_Unm_nat : d ∣ (U (n * m)).natAbs :=
      dvd_trans hd_right hUdiv_nat
    have hfinal : d ∣ cubicRecurrenceDiscriminant R U W (n * m) := by
      unfold cubicRecurrenceDiscriminant
      exact Nat.dvd_gcd hdvd_Wnm_nat hdvd_Unm_nat
    exact hfinal

end MetaMathlibExt
