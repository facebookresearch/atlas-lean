/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Int.Star
import MathlibExt.NumberTheory.BinetClosedForm
import MathlibExt.NumberTheory.Recurrences.HoradamGeneralizedCatalanIdentity

@[expose] public section

namespace MetaMathlibExt

private theorem seq_eq_of_rec_aux (U V : ℤ → ℝ) (p : ℝ)
    (hU : ∀ k : ℤ, U (k + 2) = p * U (k + 1) + U k)
    (hV : ∀ k : ℤ, V (k + 2) = p * V (k + 1) + V k)
    (h0 : U 0 = V 0) (h1 : U 1 = V 1) (n : ℤ) : U n = V n := by
  have key : ∀ k : ℤ, U k = V k ∧ U (k + 1) = V (k + 1) := by
    intro k
    induction k with
    | zero => simpa using ⟨h0, h1⟩
    | succ i ih =>
      refine ⟨ih.2, ?_⟩
      rw [show (i : ℤ) + 1 + 1 = i + 2 by ring, hU, hV, ih.1, ih.2]
    | pred i ih =>
      refine ⟨?_, by simpa using ih.1⟩
      have a := hU (-i - 1)
      have b := hV (-i - 1)
      rw [show -(i : ℤ) - 1 + 2 = -i + 1 by ring, show -(i : ℤ) - 1 + 1 = -i by ring] at a b
      rw [ih.1, ih.2] at a
      linarith
  exact (key n).1

/-- The `p`-Fibonacci sequence `0, 1, p, p ^ 2 + 1, …`. -/
private def pFibonacci {R : Type*} [CommRing R] (p : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | n + 2 => p * pFibonacci p (n + 1) + pFibonacci p n

/-- **Binet formula for generalized Fibonacci sequences.** Let $p$ be a real number and let
$(W_k)_{k \ge 0}$ be a real sequence with $W_{k+2} = p W_{k+1} + W_k$ for all $k \ge 0$. Put
$s = \sqrt{p^2 + 4}$, and let $\alpha = (p + s)/2$ and $\beta = (p - s)/2$, the roots of
$z^2 - pz - 1$. Then for every $n \ge 0$,
$W_n = \frac{W_1 - W_0 \beta}{s} \alpha^n + \frac{W_0 \alpha - W_1}{s} \beta^n$. -/
theorem generalizedFibonacci_binet (p : ℝ) (W : ℕ → ℝ)
    (hW : ∀ k, W (k + 2) = p * W (k + 1) + W k) (n : ℕ) :
    W n = (W 1 - W 0 * ((p - Real.sqrt (p ^ 2 + 4)) / 2)) / Real.sqrt (p ^ 2 + 4) *
        ((p + Real.sqrt (p ^ 2 + 4)) / 2) ^ n +
      (W 0 * ((p + Real.sqrt (p ^ 2 + 4)) / 2) - W 1) / Real.sqrt (p ^ 2 + 4) *
        ((p - Real.sqrt (p ^ 2 + 4)) / 2) ^ n := by
  have hs2 : Real.sqrt (p ^ 2 + 4) ^ 2 = p ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hs : Real.sqrt (p ^ 2 + 4) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [binet_closed_form_second_order W p (-1) ((p + Real.sqrt (p ^ 2 + 4)) / 2)
    ((p - Real.sqrt (p ^ 2 + 4)) / 2) (by linear_combination hs2 / 4)
    (by linear_combination hs2 / 4) (fun h => hs (by linarith)) (fun k => by rw [hW]; ring) n]
  rw [show (p + Real.sqrt (p ^ 2 + 4)) / 2 - (p - Real.sqrt (p ^ 2 + 4)) / 2 =
    Real.sqrt (p ^ 2 + 4) by ring]
  ring

/-- **Mixed identity for generalized Fibonacci sequences.** Let $p$ be a real number and let
$W, F : \mathbb{Z} \to \mathbb{R}$ satisfy $W_{k+2} = p W_{k+1} + W_k$ and
$F_{k+2} = p F_{k+1} + F_k$ for every integer $k$, with $F_0 = 0$ and $F_1 = 1$. Then for all
integers $m$ and $n$, $F_{m-2} W_{n-2} - F_{m-3} W_{n-1} = (-1)^{m-1} W_{n-m+1}$. -/
theorem generalizedFibonacci_mixed_identity (p : ℝ) (W F : ℤ → ℝ)
    (hWrec : ∀ k : ℤ, W (k + 2) = p * W (k + 1) + W k) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hFrec : ∀ k : ℤ, F (k + 2) = p * F (k + 1) + F k) (m n : ℤ) :
    F (m - 2) * W (n - 2) - F (m - 3) * W (n - 1) = (-1 : ℝ) ^ (m - 1) * W (n - m + 1) := by
  have hGrec : ∀ k : ℤ,
      (F ((k + 2) - 2) * W (n - 2) - F ((k + 2) - 3) * W (n - 1))
      = p * (F ((k + 1) - 2) * W (n - 2) - F ((k + 1) - 3) * W (n - 1))
        + (F (k - 2) * W (n - 2) - F (k - 3) * W (n - 1)) := by
    intro k
    have hFk : F k = p * F (k - 1) + F (k - 2) := by
      have h := hFrec (k - 2)
      have e0 : (k - 2) + 2 = k := by ring
      have e1 : (k - 2) + 1 = k - 1 := by ring
      rw [e0, e1] at h
      exact h
    have hFk1 : F (k - 1) = p * F (k - 2) + F (k - 3) := by
      have h := hFrec (k - 3)
      have e0 : (k - 3) + 2 = k - 1 := by ring
      have e1 : (k - 3) + 1 = k - 2 := by ring
      rw [e0, e1] at h
      exact h
    have e1 : (k + 2) - 2 = k := by ring
    have e2 : (k + 2) - 3 = k - 1 := by ring
    have e3 : (k + 1) - 2 = k - 1 := by ring
    have e4 : (k + 1) - 3 = k - 2 := by ring
    rw [e1, e2, e3, e4, hFk, hFk1]
    ring
  have hHrec : ∀ k : ℤ,
      ((-1 : ℝ) ^ ((k + 2) - 1) * W (n - (k + 2) + 1))
      = p * ((-1 : ℝ) ^ ((k + 1) - 1) * W (n - (k + 1) + 1))
        + ((-1 : ℝ) ^ (k - 1) * W (n - k + 1)) := by
    intro k
    have hW : W (n - k + 1) = p * W (n - k) + W (n - k - 1) := by
      have h := hWrec (n - k - 1)
      have e0 : (n - k - 1) + 2 = n - k + 1 := by ring
      have e1 : (n - k - 1) + 1 = n - k := by ring
      rw [e0, e1] at h
      exact h
    have hm1 : (k + 2 : ℤ) - 1 = (k - 1) + 2 := by ring
    have hm2 : (k + 1 : ℤ) - 1 = (k - 1) + 1 := by ring
    have eW1 : n - (k + 2 : ℤ) + 1 = n - k - 1 := by ring
    have eW2 : n - (k + 1 : ℤ) + 1 = n - k := by ring
    have hz1 : ((-1 : ℝ) ^ ((k + 2 : ℤ) - 1)) = (-1 : ℝ) ^ (k - 1) := by
      rw [hm1]
      have h2 : ((-1 : ℝ) ^ ((k - 1) + 2)) = (-1 : ℝ) ^ (k - 1) * ((-1 : ℝ) ^ (2 : ℤ)) := by
        rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      rw [h2]
      simp
    have hz2 : ((-1 : ℝ) ^ ((k + 1 : ℤ) - 1)) = -((-1 : ℝ) ^ (k - 1)) := by
      rw [hm2, zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      ring
    rw [eW1, eW2, hz1, hz2, hW]
    ring
  have hFm1 : F (-1) = 1 := by
    have h := hFrec (-1)
    have e0 : (-1 : ℤ) + 2 = 1 := by ring
    have e1 : (-1 : ℤ) + 1 = 0 := by ring
    rw [e0, e1, hF0, hF1] at h
    linarith
  have hFm2 : F (-2) = -p := by
    have h := hFrec (-2)
    have e0 : (-2 : ℤ) + 2 = 0 := by ring
    have e1 : (-2 : ℤ) + 1 = -1 := by ring
    rw [e0, e1, hF0, hFm1] at h
    linarith
  have hFm3 : F (-3) = 1 + p ^ 2 := by
    have h := hFrec (-3)
    have e0 : (-3 : ℤ) + 2 = -1 := by ring
    have e1 : (-3 : ℤ) + 1 = -2 := by ring
    rw [e0, e1, hFm1, hFm2] at h
    have hsq : p * (-p) = -p ^ 2 := by ring
    linarith [h]
  have hG0 : F ((0 : ℤ) - 2) * W (n - 2) - F ((0 : ℤ) - 3) * W (n - 1)
      = (-1 : ℝ) ^ ((0 : ℤ) - 1) * W (n - (0 : ℤ) + 1) := by
    have e1 : (0 : ℤ) - 2 = -2 := by ring
    have e2 : (0 : ℤ) - 3 = -3 := by ring
    have e3 : (0 : ℤ) - 1 = -1 := by ring
    have e4 : n - (0 : ℤ) + 1 = n + 1 := by ring
    rw [e1, e2, e3, e4, hFm2, hFm3]
    have hz : ((-1 : ℝ) ^ (-1 : ℤ)) = -1 := by simp
    rw [hz]
    have hWn1 : W (n + 1) = p * W n + W (n - 1) := by
      have h := hWrec (n - 1)
      have e0 : (n - 1) + 2 = n + 1 := by ring
      have e1' : (n - 1) + 1 = n := by ring
      rw [e0, e1'] at h
      exact h
    have hWn : W n = p * W (n - 1) + W (n - 2) := by
      have h := hWrec (n - 2)
      have e0 : (n - 2) + 2 = n := by ring
      have e1' : (n - 2) + 1 = n - 1 := by ring
      rw [e0, e1'] at h
      exact h
    rw [hWn1, hWn]
    ring
  have hG1 : F ((1 : ℤ) - 2) * W (n - 2) - F ((1 : ℤ) - 3) * W (n - 1)
      = (-1 : ℝ) ^ ((1 : ℤ) - 1) * W (n - (1 : ℤ) + 1) := by
    have e1 : (1 : ℤ) - 2 = -1 := by ring
    have e2 : (1 : ℤ) - 3 = -2 := by ring
    have e3 : (1 : ℤ) - 1 = 0 := by ring
    have e4 : n - (1 : ℤ) + 1 = n := by ring
    rw [e1, e2, e3, e4, hFm1, hFm2]
    simp only [one_mul, neg_mul, sub_neg_eq_add, zpow_ofNat, pow_zero]
    have hWn : W n = p * W (n - 1) + W (n - 2) := by
      have h := hWrec (n - 2)
      have e0 : (n - 2) + 2 = n := by ring
      have e1' : (n - 2) + 1 = n - 1 := by ring
      rw [e0, e1'] at h
      exact h
    linarith [hWn]
  have hGrec' : ∀ k : ℤ, (fun mm : ℤ => F (mm - 2) * W (n - 2) - F (mm - 3) * W (n - 1)) (k + 2)
      = p * (fun mm : ℤ => F (mm - 2) * W (n - 2) - F (mm - 3) * W (n - 1)) (k + 1)
        + (fun mm : ℤ => F (mm - 2) * W (n - 2) - F (mm - 3) * W (n - 1)) k := by
    intro k
    simpa using hGrec k
  have hHrec' : ∀ k : ℤ, (fun mm : ℤ => (-1 : ℝ) ^ (mm - 1) * W (n - mm + 1)) (k + 2)
      = p * (fun mm : ℤ => (-1 : ℝ) ^ (mm - 1) * W (n - mm + 1)) (k + 1)
        + (fun mm : ℤ => (-1 : ℝ) ^ (mm - 1) * W (n - mm + 1)) k := by
    intro k
    simpa using hHrec k
  have h0' : (fun mm : ℤ => F (mm - 2) * W (n - 2) - F (mm - 3) * W (n - 1)) 0
      = (fun mm : ℤ => (-1 : ℝ) ^ (mm - 1) * W (n - mm + 1)) 0 := by
    simpa using hG0
  have h1' : (fun mm : ℤ => F (mm - 2) * W (n - 2) - F (mm - 3) * W (n - 1)) 1
      = (fun mm : ℤ => (-1 : ℝ) ^ (mm - 1) * W (n - mm + 1)) 1 := by
    simpa using hG1
  exact seq_eq_of_rec_aux (fun mm : ℤ => F (mm - 2) * W (n - 2) - F (mm - 3) * W (n - 1))
    (fun mm : ℤ => (-1 : ℝ) ^ (mm - 1) * W (n - mm + 1)) p hGrec' hHrec' h0' h1' m

/-- **Cassini identity for generalized Fibonacci sequences.** Let $R$ be a commutative ring, let
$p \in R$, and let $(W_k)_{k \ge 0}$ be a sequence in $R$ with $W_{k+2} = p W_{k+1} + W_k$ for
all $k \ge 0$. Then for every $n \ge 0$,
$W_n W_{n+2} - W_{n+1}^2 = (-1)^n (W_0^2 + p W_0 W_1 - W_1^2)$. -/
theorem generalizedFibonacci_cassini {R : Type*} [CommRing R] (p : R) (W : ℕ → R)
    (hW : ∀ k, W (k + 2) = p * W (k + 1) + W k) (n : ℕ) :
    W n * W (n + 2) - W (n + 1) ^ 2 = (-1) ^ n * (W 0 ^ 2 + p * W 0 * W 1 - W 1 ^ 2) := by
  have hW' : ∀ k, W (k + 2) = p * W (k + 1) + 1 * W k := fun k => by rw [hW, one_mul]
  have h := horadam_generalized_catalan_identity p 1 W W (pFibonacci p) hW' hW'
    (fun k => by rw [one_mul]; rfl) rfl rfl n 1 1
  have h2 : W (1 + 1) = p * W 1 + W 0 := hW 0
  rw [h2, show pFibonacci p 1 = 1 from rfl, show n + 1 + 1 = n + 2 by ring] at h
  linear_combination -h

/-- **Ratio limit for generalized Fibonacci sequences.** Let $p > 0$ be a real number and let
$(W_k)_{k \ge 0}$ be a real sequence with $W_0 \ge 0$, $W_1 > 0$ and
$W_{k+2} = p W_{k+1} + W_k$ for all $k \ge 0$. Then $W_{k+1}/W_k$ tends to
$(p + \sqrt{p^2 + 4})/2$ as $k \to \infty$. -/
theorem generalizedFibonacci_tendsto_ratio (p : ℝ) (hp : 0 < p) (W : ℕ → ℝ) (hW0 : 0 ≤ W 0)
    (hW1 : 0 < W 1) (hW : ∀ k, W (k + 2) = p * W (k + 1) + W k) :
    Filter.Tendsto (fun k => W (k + 1) / W k) Filter.atTop
      (nhds ((p + Real.sqrt (p ^ 2 + 4)) / 2)) := by
  have hWBN := generalizedFibonacci_binet p W hW
  set s : ℝ := Real.sqrt (p ^ 2 + 4) with hsdef
  set α : ℝ := (p + s) / 2 with hαdef
  set β : ℝ := (p - s) / 2 with hβdef
  set Acoef : ℝ := (W 1 - W 0 * β) / s with hAdef
  set Bcoef : ℝ := (W 0 * α - W 1) / s with hBdef
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hplt : p < s := by
    rw [hsdef, Real.lt_sqrt hp.le]
    nlinarith
  have hα_pos : 0 < α := by simp only [hαdef]; linarith
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have hβ_neg : β < 0 := by simp only [hβdef]; linarith
  have hApos : 0 < Acoef := by
    simp only [hAdef]
    apply div_pos _ hs_pos
    nlinarith
  have hAne : Acoef ≠ 0 := ne_of_gt hApos
  have hr : |(β / α)| < 1 := by
    rw [abs_div, div_lt_one (abs_pos.mpr hα_ne), abs_of_neg hβ_neg, abs_of_pos hα_pos]
    simp only [hαdef, hβdef]
    linarith
  have hr0 : Filter.Tendsto (fun k : ℕ => (β / α) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  have hden : Filter.Tendsto (fun k : ℕ => Acoef + Bcoef * (β / α) ^ k) Filter.atTop
      (nhds Acoef) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hr0)
  have hnum : Filter.Tendsto (fun k : ℕ => Acoef + Bcoef * (β / α) ^ (k + 1)) Filter.atTop
      (nhds Acoef) :=
    hden.comp (Filter.tendsto_add_atTop_nat 1)
  have hInner := hnum.div hden hAne
  rw [div_self hAne] at hInner
  have hEq : ∀ k : ℕ, W (k + 1) / W k
      = α * ((Acoef + Bcoef * (β / α) ^ (k + 1)) / (Acoef + Bcoef * (β / α) ^ k)) := by
    intro k
    have hαk : α ^ k ≠ 0 := pow_ne_zero k hα_ne
    have eWk : W k = α ^ k * (Acoef + Bcoef * (β / α) ^ k) := by
      rw [hWBN k, div_pow β α]
      field_simp
    have eWk1 : W (k + 1) = α ^ (k + 1) * (Acoef + Bcoef * (β / α) ^ (k + 1)) := by
      rw [hWBN (k + 1), div_pow β α]
      field_simp
    rw [eWk, eWk1, pow_succ, mul_assoc, mul_div_mul_left _ _ hαk]
    ring
  have hLim := hInner.const_mul α
  rw [mul_one] at hLim
  exact hLim.congr fun k => (hEq k).symm

set_option linter.unusedVariables false in
/-- **Binet, Cassini, mixed identity and ratio limit for generalized Fibonacci sequences.**
Let $p \ge 1$, $a \ge 0$ and $b > 0$ be integers, and let $m \ge 0$ and $n \ge 0$ be integers.
Let $W, F : \mathbb{Z} \to \mathbb{R}$ satisfy $W_0 = a$, $W_1 = b$, $F_0 = 0$, $F_1 = 1$,
$W_{k+2} = p W_{k+1} + W_k$ and $F_{k+2} = p F_{k+1} + F_k$ for every integer $k$. Put
$s = \sqrt{p^2 + 4}$, $\alpha = (p + s)/2$ and $\beta = (p - s)/2$. Then
$W_n = \frac{b - a \beta}{s} \alpha^n + \frac{a \alpha - b}{s} \beta^n$,
$F_{m-2} W_{n-2} - F_{m-3} W_{n-1} = (-1)^{m-1} W_{n-m+1}$,
$W_n W_{n+2} - W_{n+1}^2 = (-1)^n (a^2 + p a b - b^2)$, and $W_{k+1}/W_k$ tends to $\alpha$ as
$k \to \infty$ through the natural numbers.

Here $a^2 + pab - b^2$ is the source's $\Delta$. The four parts also hold separately under weaker
hypotheses; in particular the mixed identity holds for all integers $m$ and $n$.

Source: Abdelhak Taane, Ihab-Eddine Djellas, and Mohammed Mekkaoui, "Total
Positivity of Toeplitz Matrices Involving Generalized Hyper-Fibonacci
Numbers," Journal of Integer Sequences 29 (2026), Article 26.2.5,
preliminary-results lemma, lines 192–200,
https://cs.uwaterloo.ca/journals/JIS/VOL29/Djellas/djellas7.tex
-/
theorem generalizedFibonacci_binet_cassini_and_ratio_limit (p a b : ℤ) (W F : ℤ → ℝ)
  (m n : ℤ) (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (hm : 0 ≤ m) (hn : 0 ≤ n) (hW0 : W 0 = (a : ℝ))
  (hW1 : W 1 = (b : ℝ)) (hWrec : ∀ k : ℤ, W (k + 2) = (p : ℝ) * W (k + 1) + W k) (hF0 : F 0 = 0)
  (hF1 : F 1 = 1) (hFrec : ∀ k : ℤ, F (k + 2) = (p : ℝ) * F (k + 1) + F k) :
  (W n =
  ((((b : ℝ) - (a : ℝ) * (((p : ℝ) - Real.sqrt ((p : ℝ) ^ 2 + 4)) / 2)) / Real.sqrt
  ((p : ℝ) ^ 2 + 4)) * ((((p : ℝ) + Real.sqrt ((p : ℝ) ^ 2 + 4)) / 2) ^ n) +
  (((a : ℝ) * (((p : ℝ) + Real.sqrt ((p : ℝ) ^ 2 + 4)) / 2) - (b : ℝ)) / Real.sqrt
  ((p : ℝ) ^ 2 + 4)) * ((((p : ℝ) - Real.sqrt ((p : ℝ) ^ 2 + 4)) / 2) ^ n)) ∧ F (m - 2) * W
  (n - 2) - F (m - 3) * W (n - 1) = (-1 : ℝ) ^ (m - 1) * W (n - m + 1) ∧ W n * W (n + 2) - W
  (n + 1) ^ 2 = (-1 : ℝ) ^ n * ((a : ℝ) ^ 2 + (p : ℝ) * (a : ℝ) * (b : ℝ) - (b : ℝ) ^ 2) ∧
  Filter.Tendsto (fun k : ℕ => W (↑k + 1) / W ↑k) Filter.atTop
  (nhds ((((p : ℝ) + Real.sqrt ((p : ℝ) ^ 2 + 4)) / 2)))) := by
  have hpR : (0 : ℝ) < p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hV : ∀ k : ℕ, (fun j : ℕ => W j) (k + 2) = (p : ℝ) * (fun j : ℕ => W j) (k + 1) +
      (fun j : ℕ => W j) k := fun k => by simpa using hWrec k
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  refine ⟨?_, generalizedFibonacci_mixed_identity _ W F hWrec hF0 hF1 hFrec m N, ?_, ?_⟩
  · simpa [hW0, hW1] using generalizedFibonacci_binet (p : ℝ) (fun j : ℕ => W j) hV N
  · simpa [hW0, hW1] using generalizedFibonacci_cassini (p : ℝ) (fun j : ℕ => W j) hV N
  · simpa using generalizedFibonacci_tendsto_ratio (p : ℝ) hpR (fun j : ℕ => W j)
      (by simpa [hW0] using ha)
      (by simpa [hW1] using hb) hV

end MetaMathlibExt
