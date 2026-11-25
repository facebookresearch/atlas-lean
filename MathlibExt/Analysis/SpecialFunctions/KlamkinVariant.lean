/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import MathlibExt.Analysis.SpecialFunctions.GaussHypergeometricSummationKlamkin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Variant of Klamkin's identity

This file proves Abel's variant of Klamkin's reciprocal-binomial identity by reducing it to a
Klamkin-specialized Gauss hypergeometric summation.
-/

private lemma klamkin_admissible (a b : ℝ)
    (h_ab : ∀ m : ℤ, a - b ≠ (m : ℝ)) :
    ∀ k : ℕ, a - b + 1 ≠ (k : ℝ) := by
  intro k hk
  apply h_ab ((k : ℤ) - 1)
  push_cast
  linarith

private lemma klamkin_pochhammer_ne (x : ℝ)
    (hx : ∀ j : ℕ, x + (j : ℝ) ≠ 0) (k : ℕ) :
    Polynomial.eval x (ascPochhammer ℝ k) ≠ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval]
    exact mul_ne_zero ih (hx k)

private lemma klamkin_b_add_ne (b : ℝ)
    (h_neg_b : ∀ m : ℕ, -b ≠ (m : ℝ)) (j : ℕ) :
    b + 1 + (j : ℝ) ≠ 0 := by
  intro hj
  apply h_neg_b (j + 1)
  push_cast
  linarith

private lemma klamkin_Gamma_add_nat (x : ℝ)
    (hx : ∀ j : ℕ, x + (j : ℝ) ≠ 0) (k : ℕ) :
    Real.Gamma (x + (k : ℝ)) =
      Real.Gamma x * Polynomial.eval x (ascPochhammer ℝ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show x + ((k + 1 : ℕ) : ℝ) = (x + (k : ℝ)) + 1 by push_cast; ring,
      Real.Gamma_add_one (hx k), ih, ascPochhammer_succ_eval]
    ring

private lemma klamkin_Gamma_sub_nat (x : ℝ)
    (hx : ∀ j : ℕ, x - (j : ℝ) - 1 ≠ 0) (k : ℕ) :
    (-1 : ℝ) ^ k * Real.Gamma (x - (k : ℝ)) =
      Real.Gamma x / Polynomial.eval (1 - x) (ascPochhammer ℝ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hq : 1 - x + (k : ℝ) ≠ 0 := by
      intro h
      apply hx k
      linarith
    have hGamma : Real.Gamma (x - (k : ℝ)) =
        (x - (k : ℝ) - 1) * Real.Gamma (x - ((k + 1 : ℕ) : ℝ)) := by
      have h := Real.Gamma_add_one (hx k)
      convert h using 1
      all_goals push_cast
      all_goals ring_nf
    calc
      (-1 : ℝ) ^ (k + 1) * Real.Gamma (x - ((k + 1 : ℕ) : ℝ)) =
          ((-1 : ℝ) ^ k * Real.Gamma (x - (k : ℝ))) /
            (1 - x + (k : ℝ)) := by
        rw [pow_succ, hGamma]
        field_simp
        ring
      _ = (Real.Gamma x / Polynomial.eval (1 - x) (ascPochhammer ℝ k)) /
          (1 - x + (k : ℝ)) := by rw [ih]
      _ = Real.Gamma x /
          (Polynomial.eval (1 - x) (ascPochhammer ℝ k) *
            (1 - x + (k : ℝ))) := by rw [div_div]
      _ = Real.Gamma x /
          Polynomial.eval (1 - x) (ascPochhammer ℝ (k + 1)) := by
        rw [ascPochhammer_succ_eval]

private lemma klamkin_coeff_eq_choose (a b : ℝ) (n k : ℕ) :
    ordinaryHypergeometricCoefficient (n : ℝ) (b + 1) (b - a) k =
      (Nat.choose (n + k - 1) k : ℝ) *
        Polynomial.eval (b + 1) (ascPochhammer ℝ k) /
          Polynomial.eval (b - a) (ascPochhammer ℝ k) := by
  have hpoch := congr_arg (fun m : ℕ => (m : ℝ))
    (Nat.ascFactorial_eq_factorial_mul_choose' n k)
  rw [Nat.cast_mul, Nat.cast_ascFactorial] at hpoch
  have hfactorial : (k.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  unfold ordinaryHypergeometricCoefficient
  rw [hpoch]
  field_simp

private lemma klamkin_summand_eq (a b : ℝ) (n : ℕ)
    (h_neg_b : ∀ m : ℕ, -b ≠ (m : ℝ))
    (h_ab : ∀ m : ℤ, a - b ≠ (m : ℝ)) (k : ℕ) :
    (-1 : ℝ) ^ k * (Nat.choose (n + k - 1) k : ℝ) *
        (Real.Gamma (a + 1) /
          (Real.Gamma (b + (k : ℝ) + 1) *
            Real.Gamma (a - (b + (k : ℝ)) + 1)))⁻¹ =
      (Real.Gamma (b + 1) * Real.Gamma (a - b + 1) / Real.Gamma (a + 1)) *
        ordinaryHypergeometricCoefficient (n : ℝ) (b + 1) (b - a) k := by
  have hGamma_b : Real.Gamma (b + (k : ℝ) + 1) =
      Real.Gamma (b + 1) *
        Polynomial.eval (b + 1) (ascPochhammer ℝ k) := by
    convert klamkin_Gamma_add_nat (b + 1)
      (klamkin_b_add_ne b h_neg_b) k using 1
    all_goals ring_nf
  have hsub_ne : ∀ j : ℕ, a - b + 1 - (j : ℝ) - 1 ≠ 0 := by
    intro j hj
    apply h_ab (j : ℤ)
    norm_num
    linarith
  have hGamma_ab : (-1 : ℝ) ^ k *
      Real.Gamma (a - (b + (k : ℝ)) + 1) =
        Real.Gamma (a - b + 1) /
          Polynomial.eval (b - a) (ascPochhammer ℝ k) := by
    convert klamkin_Gamma_sub_nat (a - b + 1) hsub_ne k using 1
    all_goals ring_nf
  rw [inv_div, hGamma_b, klamkin_coeff_eq_choose]
  calc
    (-1 : ℝ) ^ k * (Nat.choose (n + k - 1) k : ℝ) *
          ((Real.Gamma (b + 1) *
              Polynomial.eval (b + 1) (ascPochhammer ℝ k) *
            Real.Gamma (a - (b + (k : ℝ)) + 1)) /
              Real.Gamma (a + 1)) =
        (Nat.choose (n + k - 1) k : ℝ) *
          (Real.Gamma (b + 1) *
            Polynomial.eval (b + 1) (ascPochhammer ℝ k) /
              Real.Gamma (a + 1)) *
            ((-1 : ℝ) ^ k * Real.Gamma (a - (b + (k : ℝ)) + 1)) := by ring
    _ = (Nat.choose (n + k - 1) k : ℝ) *
          (Real.Gamma (b + 1) *
            Polynomial.eval (b + 1) (ascPochhammer ℝ k) /
              Real.Gamma (a + 1)) *
            (Real.Gamma (a - b + 1) /
              Polynomial.eval (b - a) (ascPochhammer ℝ k)) := by rw [hGamma_ab]
    _ = (Real.Gamma (b + 1) * Real.Gamma (a - b + 1) /
            Real.Gamma (a + 1)) *
          ((Nat.choose (n + k - 1) k : ℝ) *
            Polynomial.eval (b + 1) (ascPochhammer ℝ k) /
              Polynomial.eval (b - a) (ascPochhammer ℝ k)) := by ring

private lemma klamkin_Gamma_add_int_ne (x : ℝ)
    (hx : ∀ m : ℤ, x ≠ (m : ℝ)) (r : ℤ) :
    Real.Gamma (x + (r : ℝ)) ≠ 0 := by
  apply Real.Gamma_ne_zero
  intro m hm
  apply hx (-(m : ℤ) - r)
  push_cast
  linarith

private lemma klamkin_Gamma_a_add_nat_ne (a : ℝ)
    (h_neg_a : ∀ m : ℕ, -a ≠ (m : ℝ)) (r : ℕ) :
    Real.Gamma (a + (r : ℝ) + 1) ≠ 0 := by
  apply Real.Gamma_ne_zero
  intro m hm
  apply h_neg_a (r + 1 + m)
  push_cast
  linarith

private lemma klamkin_gamma_value (a b : ℝ) (n : ℕ)
    (h_neg_a : ∀ m : ℕ, -a ≠ (m : ℝ))
    (h_n_bound : (n : ℝ) < -a - 1)
    (h_ab : ∀ m : ℤ, a - b ≠ (m : ℝ)) :
    (Real.Gamma (b + 1) * Real.Gamma (a - b + 1) / Real.Gamma (a + 1)) *
        (Real.Gamma (-a - n - 1) * Real.Gamma (b - a) /
          (Real.Gamma (b - a - n) * Real.Gamma (-a - 1))) =
      (a + 1) / (a + (n : ℝ) + 1) *
        ((Real.Gamma (a + (n : ℝ) + 1) /
          (Real.Gamma (b + 1) * Real.Gamma (a + (n : ℝ) - b + 1)))⁻¹) := by
  have hab1_ne : ∀ j : ℕ, a - b + 1 + (j : ℝ) ≠ 0 := by
    intro j hj
    apply h_ab (-((j : ℤ) + 1))
    push_cast
    linarith
  have ha2_ne : ∀ j : ℕ, a + 2 + (j : ℝ) ≠ 0 := by
    intro j hj
    apply h_neg_a (j + 2)
    push_cast
    linarith
  have hp1 : Polynomial.eval (a - b + 1) (ascPochhammer ℝ n) ≠ 0 :=
    klamkin_pochhammer_ne (a - b + 1) hab1_ne n
  have hp2 : Polynomial.eval (a + 2) (ascPochhammer ℝ n) ≠ 0 :=
    klamkin_pochhammer_ne (a + 2) ha2_ne n
  have hneg_a : (-1 : ℝ) ^ n * Real.Gamma (-a - n - 1) =
      Real.Gamma (-a - 1) /
        Polynomial.eval (a + 2) (ascPochhammer ℝ n) := by
    have hsub : ∀ j : ℕ, -a - 1 - (j : ℝ) - 1 ≠ 0 := by
      intro j hj
      exact ha2_ne j (by linarith)
    convert klamkin_Gamma_sub_nat (-a - 1) hsub n using 1
    all_goals ring_nf
  have hneg_ab : (-1 : ℝ) ^ n * Real.Gamma (b - a - n) =
      Real.Gamma (b - a) /
        Polynomial.eval (a - b + 1) (ascPochhammer ℝ n) := by
    have hsub : ∀ j : ℕ, b - a - (j : ℝ) - 1 ≠ 0 := by
      intro j hj
      exact hab1_ne j (by linarith)
    convert klamkin_Gamma_sub_nat (b - a) hsub n using 1
    all_goals ring_nf
  have hadd_ab : Real.Gamma (a + (n : ℝ) - b + 1) =
      Real.Gamma (a - b + 1) *
        Polynomial.eval (a - b + 1) (ascPochhammer ℝ n) := by
    convert klamkin_Gamma_add_nat (a - b + 1) hab1_ne n using 1
    all_goals ring_nf
  have hadd_a2 : Real.Gamma (a + (n : ℝ) + 2) =
      Real.Gamma (a + 2) *
        Polynomial.eval (a + 2) (ascPochhammer ℝ n) := by
    convert klamkin_Gamma_add_nat (a + 2) ha2_ne n using 1
    all_goals ring_nf
  have h_ba : ∀ m : ℤ, b - a ≠ (m : ℝ) := by
    intro m hm
    apply h_ab (-m)
    push_cast
    linarith
  have hGamma_ba_n : Real.Gamma (b - a - n) ≠ 0 := by
    convert klamkin_Gamma_add_int_ne (b - a) h_ba (-(n : ℤ)) using 1
    all_goals push_cast
    all_goals ring_nf
  have hGamma_neg_a : Real.Gamma (-a - 1) ≠ 0 := by
    apply ne_of_gt (Real.Gamma_pos_of_pos ?_)
    have hn : (0 : ℝ) ≤ (n : ℕ) := Nat.cast_nonneg n
    linarith
  have hneg_a' : (-1 : ℝ) ^ n * Real.Gamma (-a - n - 1) *
      Polynomial.eval (a + 2) (ascPochhammer ℝ n) = Real.Gamma (-a - 1) :=
    (eq_div_iff hp2).mp hneg_a
  have hneg_ab' : (-1 : ℝ) ^ n * Real.Gamma (b - a - n) *
      Polynomial.eval (a - b + 1) (ascPochhammer ℝ n) = Real.Gamma (b - a) :=
    (eq_div_iff hp1).mp hneg_ab
  have hratio : Real.Gamma (-a - n - 1) * Real.Gamma (b - a) /
        (Real.Gamma (b - a - n) * Real.Gamma (-a - 1)) =
      Polynomial.eval (a - b + 1) (ascPochhammer ℝ n) /
        Polynomial.eval (a + 2) (ascPochhammer ℝ n) := by
    rw [div_eq_iff (mul_ne_zero hGamma_ba_n hGamma_neg_a)]
    field_simp [hp2]
    rw [← hneg_ab', ← hneg_a']
    ring
  have ha1 : a + 1 ≠ 0 := by
    intro ha
    apply h_neg_a 1
    norm_num
    linarith
  have han1 : a + (n : ℝ) + 1 ≠ 0 := by linarith
  have hden : (a + (n : ℝ) + 1) * Real.Gamma (a + (n : ℝ) + 1) =
      (a + 1) * Real.Gamma (a + 1) *
        Polynomial.eval (a + 2) (ascPochhammer ℝ n) := by
    calc
      (a + (n : ℝ) + 1) * Real.Gamma (a + (n : ℝ) + 1) =
          Real.Gamma (a + (n : ℝ) + 2) := by
        rw [show a + (n : ℝ) + 2 = (a + (n : ℝ) + 1) + 1 by ring,
          Real.Gamma_add_one han1]
      _ = Real.Gamma (a + 2) *
          Polynomial.eval (a + 2) (ascPochhammer ℝ n) := hadd_a2
      _ = (a + 1) * Real.Gamma (a + 1) *
          Polynomial.eval (a + 2) (ascPochhammer ℝ n) := by
        rw [show a + 2 = (a + 1) + 1 by ring, Real.Gamma_add_one ha1]
  have hGamma_a1 := klamkin_Gamma_a_add_nat_ne a h_neg_a 0
  have hGamma_an1 := klamkin_Gamma_a_add_nat_ne a h_neg_a n
  have hfrac : 1 / (Real.Gamma (a + 1) *
        Polynomial.eval (a + 2) (ascPochhammer ℝ n)) =
      (a + 1) /
        ((a + (n : ℝ) + 1) * Real.Gamma (a + (n : ℝ) + 1)) := by
    rw [hden]
    field_simp [ha1, hGamma_a1, hp2]
  rw [hratio]
  calc
    (Real.Gamma (b + 1) * Real.Gamma (a - b + 1) / Real.Gamma (a + 1)) *
          (Polynomial.eval (a - b + 1) (ascPochhammer ℝ n) /
            Polynomial.eval (a + 2) (ascPochhammer ℝ n)) =
        Real.Gamma (b + 1) * Real.Gamma (a - b + 1) *
          Polynomial.eval (a - b + 1) (ascPochhammer ℝ n) *
            (1 / (Real.Gamma (a + 1) *
              Polynomial.eval (a + 2) (ascPochhammer ℝ n))) := by ring
    _ = Real.Gamma (b + 1) * Real.Gamma (a - b + 1) *
          Polynomial.eval (a - b + 1) (ascPochhammer ℝ n) *
            ((a + 1) /
              ((a + (n : ℝ) + 1) * Real.Gamma (a + (n : ℝ) + 1))) := by
      rw [hfrac]
    _ = (a + 1) / (a + (n : ℝ) + 1) *
        ((Real.Gamma (a + (n : ℝ) + 1) /
          (Real.Gamma (b + 1) * Real.Gamma (a + (n : ℝ) - b + 1)))⁻¹) := by
      rw [hadd_ab, inv_div]
      field_simp [han1, hGamma_an1]

/--
**Abel's variant of Klamkin's identity.** For real numbers $c$ and $d$ write
$\binom{c}{d} = \Gamma(c+1) / (\Gamma(d+1) \, \Gamma(c-d+1))$; for natural numbers this is the
usual binomial coefficient. Let $a$ and $b$ be real numbers such that $-a$ and $-b$ are not in
$\{0, 1, 2, \dots\}$ and $a - b$ is not an integer, and let $n \ge 1$ be a natural number with
$n < -a - 1$. Then the series

$$\sum_{k \ge 0} (-1)^k \binom{n+k-1}{k} \binom{a}{b+k}^{-1}$$

converges unconditionally to $\frac{a+1}{a+n+1} \binom{a+n}{b}^{-1}$.

Abel assumes only $a - b + 1 \notin \mathbb{N}$; here $a - b$ must avoid every integer, since
otherwise some $\Gamma(a - b - k + 1)$ is evaluated at a pole of $\Gamma$.

Proof: Rewrite the summand as an ordinary hypergeometric coefficient and apply Abel's
specialization of Gauss's formula (Abramowitz-Stegun 15.1.20), then simplify by Gamma recurrence.

Proves `Wanted` entry `variant_Klamkin`.

Source: Ulrich Abel, "A Short Proof of the Binomial Identities of Frisch and
Klamkin," Journal of Integer Sequences 23 (2020), Article 20.7.1, Theorem
(label theorem-variant-Klamkin), equation (Identity-variant-Klamkin),
lines 210–218,
https://cs.uwaterloo.ca/journals/JIS/VOL23/Abel/abel12.tex
-/
public theorem variant_Klamkin (a b : ℝ) (n : ℕ)
    (h_neg_a : ∀ m : ℕ, -a ≠ (m : ℝ))
    (h_neg_b : ∀ m : ℕ, -b ≠ (m : ℝ))
    (h_n_pos : 1 ≤ n)
    (h_n_bound : (n : ℝ) < -a - 1)
    (h_ab : ∀ m : ℤ, a - b ≠ (m : ℝ)) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * (Nat.choose (n + k - 1) k : ℝ) *
      (Real.Gamma (a + 1) /
        (Real.Gamma (b + (k : ℝ) + 1) *
          Real.Gamma (a - (b + (k : ℝ)) + 1)))⁻¹)
      ((a + 1) / (a + (n : ℝ) + 1) *
        ((Real.Gamma (a + (n : ℝ) + 1) /
          (Real.Gamma (b + 1) * Real.Gamma (a + (n : ℝ) - b + 1)))⁻¹)) := by
  let K := Real.Gamma (b + 1) * Real.Gamma (a - b + 1) / Real.Gamma (a + 1)
  have hcoeff :=
    hasSum_ordinaryHypergeometricCoefficient_klamkin n a b h_neg_a h_neg_b h_n_pos
      (by linarith) (klamkin_admissible a b h_ab)
  have hscaled := hcoeff.mul_left K
  have hseries : HasSum (fun k : ℕ => (-1 : ℝ) ^ k *
      (Nat.choose (n + k - 1) k : ℝ) *
        (Real.Gamma (a + 1) /
          (Real.Gamma (b + (k : ℝ) + 1) *
            Real.Gamma (a - (b + (k : ℝ)) + 1)))⁻¹)
      (K * (Real.Gamma (-a - n - 1) * Real.Gamma (b - a) /
        (Real.Gamma (b - a - n) * Real.Gamma (-a - 1)))) := by
    exact HasSum.congr_fun hscaled fun k =>
      klamkin_summand_eq a b n h_neg_b h_ab k
  dsimp only [K] at hseries
  rw [klamkin_gamma_value a b n h_neg_a h_n_bound h_ab] at hseries
  exact hseries

end MetaMathlibExt
