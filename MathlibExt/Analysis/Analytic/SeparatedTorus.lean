/-
Copyright 2026 Anthropic, PBC

Licensed under the Apache License, Version 2.0.
Adapted from Fermat's Last Theorem in Lean 4:
P2M/Sol/
Source filename (concatenate the next two lines):
S_Polynomial_exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_
separated_recurrence.lean
and its matching Theorems/Thm_ wrapper, revision
6e837e75355538c7f80bab5b956861e86c4eacc2.
The original files identify no individual authors. See their NOTICE and
ATTRIBUTION.md.
-/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Separated recurrences with torus weights

A separated recurrence outside a finite square gives a single polynomial
numerator in the variables `X, Y, b₁, b₂`. The weight parameters may coincide
or vanish; only the positive convergence radius depends on them.
-/

noncomputable section
open Finset

namespace Polynomial.SeparatedTorus

variable (A : ℤ × ℤ → ℂ) (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ)

private def a (m k : ℤ) : ℂ := A (N₁ + m, N₁ + k)

private def e₁ (m k : ℤ) : ℂ :=
  ∑ p ∈ range (D₁.natDegree + 1), D₁.coeff p * a A N₁ (m - p) k

private def e₂ (m k : ℤ) : ℂ :=
  ∑ l ∈ range (D₂.natDegree + 1), D₂.coeff l * a A N₁ m (k - l)

private def e₁₂ (m k : ℤ) : ℂ :=
  ∑ p ∈ range (D₁.natDegree + 1), ∑ l ∈ range (D₂.natDegree + 1),
    D₁.coeff p * D₂.coeff l * a A N₁ (m - p) (k - l)

private theorem e₁₂_eq_sum_e₂ (m k : ℤ) :
    e₁₂ A N₁ D₁ D₂ m k =
      ∑ p ∈ range (D₁.natDegree + 1),
        D₁.coeff p * e₂ A N₁ D₂ (m - p) k := by
  simp only [e₁₂, e₂, mul_sum, mul_assoc]

private theorem e₁₂_eq_sum_e₁ (m k : ℤ) :
    e₁₂ A N₁ D₁ D₂ m k =
      ∑ l ∈ range (D₂.natDegree + 1),
        D₂.coeff l * e₁ A N₁ D₁ m (k - l) := by
  simp only [e₁₂, e₁, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => sum_congr rfl fun p _ => ?_
  ring

variable {A N₁ D₁ D₂} {M : ℕ}

private theorem eq_zero_of_conv_eq_zero (D : Polynomial ℂ) (hD : D.coeff 0 ≠ 0)
    (Φ : ℤ → ℂ)
    (hneg : ∀ m : ℤ, m < 0 → Φ m = 0)
    (hconv : ∀ m : ℤ, 0 ≤ m → ∑ p ∈ range (D.natDegree + 1), D.coeff p * Φ (m -
        p) = 0) :
    ∀ m : ℤ, Φ m = 0 := by
  have key : ∀ n : ℕ, Φ n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have h := hconv n (by positivity)
      rw [Finset.sum_range_succ'] at h
      have hrest : ∑ p ∈ range D.natDegree, D.coeff (p + 1) * Φ ((n : ℤ) - ((p +
          1 : ℕ) : ℤ)) = 0
          := by
        refine Finset.sum_eq_zero fun p _ => ?_
        have hz : Φ ((n : ℤ) - ((p + 1 : ℕ) : ℤ)) = 0 := by
          by_cases hlt : (n : ℤ) - ((p + 1 : ℕ) : ℤ) < 0
          · exact hneg _ hlt
          · obtain ⟨n', hn', hlt'⟩ : ∃ n' : ℕ, (n' : ℤ) = n - ((p + 1 : ℕ) : ℤ)
              ∧ n' < n :=
              ⟨n - (p + 1), by push_cast; omega, by omega⟩
            rw [← hn']
            exact ih n' hlt'
        rw [hz, mul_zero]
      rw [hrest, zero_add] at h
      simp only [Nat.cast_zero, sub_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hD
  intro m
  rcases lt_or_ge m 0 with hm | hm
  · exact hneg m hm
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    exact key n


private theorem e₂_eq_zero (hD₁ : D₁.coeff 0 ≠ 0)
    (hsupp : ∀ m k : ℤ, (m < 0 ∨ k < 0) → a A N₁ m k = 0)
    (hrec : ∀ m k : ℤ, 0 ≤ m → 0 ≤ k → ((M : ℤ) ≤ m ∨ (M : ℤ) ≤ k) → e₁₂ A N₁ D₁
        D₂ m k = 0)
    {k : ℤ} (hk : (M : ℤ) ≤ k) : ∀ m : ℤ, e₂ A N₁ D₂ m k = 0 := by
  refine eq_zero_of_conv_eq_zero D₁ hD₁ (fun m => e₂ A N₁ D₂ m k) (fun m hm =>
      ?_) (fun m hm =>
      ?_)
  · simp only [e₂]
    exact Finset.sum_eq_zero fun l _ => by rw [hsupp _ _ (Or.inl hm), mul_zero]
  · rw [← e₁₂_eq_sum_e₂]
    exact hrec m k hm ((Int.natCast_nonneg M).trans hk) (Or.inr hk)


private theorem e₁_eq_zero (hD₂ : D₂.coeff 0 ≠ 0)
    (hsupp : ∀ m k : ℤ, (m < 0 ∨ k < 0) → a A N₁ m k = 0)
    (hrec : ∀ m k : ℤ, 0 ≤ m → 0 ≤ k → ((M : ℤ) ≤ m ∨ (M : ℤ) ≤ k) → e₁₂ A N₁ D₁
        D₂ m k = 0)
    {m : ℤ} (hm : (M : ℤ) ≤ m) : ∀ k : ℤ, e₁ A N₁ D₁ m k = 0 := by
  refine eq_zero_of_conv_eq_zero D₂ hD₂ (fun k => e₁ A N₁ D₁ m k) (fun k hk =>
      ?_) (fun k hk =>
      ?_)
  · simp only [e₁]
    exact Finset.sum_eq_zero fun p _ => by rw [hsupp _ _ (Or.inr hk), mul_zero]
  · rw [← e₁₂_eq_sum_e₁]
    exact hrec m k ((Int.natCast_nonneg M).trans hm) hk (Or.inl hm)


private def q (A : ℤ × ℤ → ℂ) (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (i j k : ℕ) : ℂ :=
  ∑ p ∈ range (i + 1), ∑ r ∈ range (j + 1), ∑ l ∈ range (k + 1),
    D₁.coeff p * D₁.coeff r * D₂.coeff l * a A N₁ ((i : ℤ) + j - p - r) ((k : ℤ)
        - l)


private theorem sum_range_D₂_eq_e₂ (hsupp : ∀ m k : ℤ, (m < 0 ∨ k < 0) → a A N₁
    m k = 0) (x : ℤ)
    (k : ℕ) :
    ∑ l ∈ range (k + 1), D₂.coeff l * a A N₁ x ((k : ℤ) - l) =
      e₂ A N₁ D₂ x k := by
  have h1 : ∑ l ∈ range (k + 1), D₂.coeff l * a A N₁ x ((k : ℤ) - l) =
      ∑ l ∈ range (k + D₂.natDegree + 1),
        D₂.coeff l * a A N₁ x ((k : ℤ) - l) := by
    refine Finset.sum_subset (by gcongr; omega) fun l hl hl' => ?_
    have : (k : ℤ) - l < 0 := by simp only [mem_range] at hl hl'; omega
    rw [hsupp _ _ (Or.inr this), mul_zero]
  have h2 : e₂ A N₁ D₂ x k = ∑ l ∈ range (k + D₂.natDegree + 1), D₂.coeff l * a
      A N₁ x ((k : ℤ) -
      l) := by
    unfold e₂
    refine Finset.sum_subset (by gcongr; omega) fun l hl hl' => ?_
    have : D₂.natDegree < l := by simp only [mem_range] at hl hl'; omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt this, zero_mul]
  rw [h1, h2]


private theorem sum_range_D₁_eq (f : ℕ → ℂ) {i : ℕ} (hi : D₁.natDegree ≤ i) :
    ∑ p ∈ range (i + 1), D₁.coeff p * f p = ∑ p ∈ range (D₁.natDegree + 1),
        D₁.coeff p * f p := by
  symm
  refine Finset.sum_subset (by gcongr) fun p hp hp' => ?_
  have : D₁.natDegree < p := by simp only [mem_range] at hp hp'; omega
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt this, zero_mul]


private theorem q_eq_zero (hD₁ : D₁.coeff 0 ≠ 0) (hD₂ : D₂.coeff 0 ≠ 0)
    (hsupp : ∀ m k : ℤ, (m < 0 ∨ k < 0) → a A N₁ m k = 0)
    (hrec : ∀ m k : ℤ, 0 ≤ m → 0 ≤ k → ((M : ℤ) ≤ m ∨ (M : ℤ) ≤ k) → e₁₂ A N₁ D₁
        D₂ m k = 0)
    {i j k : ℕ} (h : max M D₁.natDegree ≤ i ∨ max M D₁.natDegree ≤ j ∨ M ≤ k) :
    q A N₁ D₁ D₂ i j k = 0 := by
  have hq : q A N₁ D₁ D₂ i j k =
      ∑ p ∈ range (i + 1), ∑ r ∈ range (j + 1), D₁.coeff p * D₁.coeff r * e₂ A
          N₁ D₂ ((i : ℤ) + j
          - p - r) k := by
    unfold q
    refine sum_congr rfl fun p _ => sum_congr rfl fun r _ => ?_
    rw [← sum_range_D₂_eq_e₂ hsupp, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    ring
  rcases h with hi | hj | hk
  · have hiM : M ≤ i := (le_max_left _ _).trans hi
    have hid : D₁.natDegree ≤ i := (le_max_right _ _).trans hi
    rw [hq, sum_comm]
    refine Finset.sum_eq_zero fun r hr => ?_
    have hr' : r ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hr)
    have : ∑ p ∈ range (i + 1), D₁.coeff p * D₁.coeff r * e₂ A N₁ D₂ ((i : ℤ) +
        j - p - r) k =
        D₁.coeff r * e₁₂ A N₁ D₁ D₂ ((i : ℤ) + j - r) k := by
      calc ∑ p ∈ range (i + 1), D₁.coeff p * D₁.coeff r * e₂ A N₁ D₂ ((i : ℤ) +
          j - p - r) k
          = ∑ p ∈ range (i + 1), D₁.coeff p * (D₁.coeff r * e₂ A N₁ D₂ ((i : ℤ)
              + j - r - p) k) :=
              by
            refine sum_congr rfl fun p _ => ?_
            rw [show (i : ℤ) + j - p - r = (i : ℤ) + j - r - p by ring]
            ring
        _ = ∑ p ∈ range (D₁.natDegree + 1), D₁.coeff p * (D₁.coeff r * e₂ A N₁
            D₂ ((i : ℤ) + j - r
            - p) k) :=
            sum_range_D₁_eq _ hid
        _ = D₁.coeff r * e₁₂ A N₁ D₁ D₂ ((i : ℤ) + j - r) k := by
            rw [e₁₂_eq_sum_e₂, mul_sum]
            refine sum_congr rfl fun p _ => ?_
            ring
    rw [this, e₁₂_eq_sum_e₁]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun l _ => ?_)
    rw [e₁_eq_zero hD₂ hsupp hrec (by omega), mul_zero]
  · have hjM : M ≤ j := (le_max_left _ _).trans hj
    have hjd : D₁.natDegree ≤ j := (le_max_right _ _).trans hj
    rw [hq]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' : p ≤ i := Nat.lt_succ_iff.mp (mem_range.mp hp)
    have : ∑ r ∈ range (j + 1), D₁.coeff p * D₁.coeff r * e₂ A N₁ D₂ ((i : ℤ) +
        j - p - r) k =
        D₁.coeff p * e₁₂ A N₁ D₁ D₂ ((i : ℤ) + j - p) k := by
      calc ∑ r ∈ range (j + 1), D₁.coeff p * D₁.coeff r * e₂ A N₁ D₂ ((i : ℤ) +
          j - p - r) k
          = ∑ r ∈ range (j + 1), D₁.coeff r * (D₁.coeff p * e₂ A N₁ D₂ ((i : ℤ)
              + j - p - r) k) :=
              by
            refine sum_congr rfl fun r _ => ?_
            ring
        _ = ∑ r ∈ range (D₁.natDegree + 1), D₁.coeff r * (D₁.coeff p * e₂ A N₁
            D₂ ((i : ℤ) + j - p
            - r) k) :=
            sum_range_D₁_eq _ hjd
        _ = D₁.coeff p * e₁₂ A N₁ D₁ D₂ ((i : ℤ) + j - p) k := by
            rw [e₁₂_eq_sum_e₂, mul_sum]
            refine sum_congr rfl fun r _ => ?_
            ring
    rw [this, e₁₂_eq_sum_e₁]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun l _ => ?_)
    rw [e₁_eq_zero hD₂ hsupp hrec (by omega), mul_zero]
  · rw [hq]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun r _ => ?_
    rw [e₂_eq_zero hD₁ hsupp hrec (by exact_mod_cast hk), mul_zero]


private theorem e₁₂_eq_add_sum_erase (m k : ℤ) :
    e₁₂ A N₁ D₁ D₂ m k = D₁.coeff 0 * D₂.coeff 0 * a A N₁ m k +
      ∑ x ∈ (range (D₁.natDegree + 1) ×ˢ range (D₂.natDegree + 1)).erase (0, 0),
        D₁.coeff x.1 * D₂.coeff x.2 * a A N₁ (m - x.1) (k - x.2) := by
  unfold e₁₂
  rw [← Finset.sum_product']
  rw [← Finset.add_sum_erase (a := ((0 : ℕ), (0 : ℕ))) _ _ (by simp)]
  simp

private theorem growth (hD₁ : D₁.coeff 0 ≠ 0) (hD₂ : D₂.coeff 0 ≠ 0)
    (hsupp : ∀ m k : ℤ, (m < 0 ∨ k < 0) → a A N₁ m k = 0)
    (hrec : ∀ m k : ℤ, 0 ≤ m → 0 ≤ k → ((M : ℤ) ≤ m ∨ (M : ℤ) ≤ k) → e₁₂ A N₁ D₁
        D₂ m k = 0) :
    ∃ K C : ℝ, 0 ≤ K ∧ 1 ≤ C ∧ ∀ m k : ℕ, ‖a A N₁ m k‖ ≤ K * C ^ (m + k) := by
  set s : Finset (ℕ × ℕ) := (range (D₁.natDegree + 1) ×ˢ range (D₂.natDegree +
      1)).erase (0, 0)
      with hs
  set S : ℝ := ∑ x ∈ s, ‖D₁.coeff x.1 * D₂.coeff x.2‖ with hS
  set c₀ : ℝ := ‖D₁.coeff 0 * D₂.coeff 0‖ with hc₀
  have hc₀pos : 0 < c₀ := norm_pos_iff.mpr (mul_ne_zero hD₁ hD₂)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set K : ℝ := ∑ m ∈ range M, ∑ k ∈ range M, ‖a A N₁ m k‖ with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      norm_nonneg _
  set C : ℝ := max 1 (S / c₀) with hC
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCS : S / c₀ ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  refine ⟨K, C, hK0, hC1, ?_⟩
  suffices h : ∀ n : ℕ, ∀ m k : ℕ, m + k = n → ‖a A N₁ m k‖ ≤ K * C ^ n by
    intro m k; exact h (m + k) m k rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m k hmk
    by_cases hsmall : m < M ∧ k < M
    · have h1 : ‖a A N₁ m k‖ ≤ K := by
        rw [hK]
        have h1a : ‖a A N₁ (m : ℤ) (k : ℤ)‖ ≤ ∑ k' ∈ range M, ‖a A N₁ (m : ℤ)
            ((k' : ℕ) : ℤ)‖ :=
          Finset.single_le_sum (f := fun k' : ℕ => ‖a A N₁ (m : ℤ) ((k' : ℕ) :
              ℤ)‖)
            (fun _ _ => norm_nonneg _) (mem_range.mpr hsmall.2)
        have h1b : ∑ k' ∈ range M, ‖a A N₁ (m : ℤ) ((k' : ℕ) : ℤ)‖ ≤
            ∑ m' ∈ range M, ∑ k' ∈ range M, ‖a A N₁ ((m' : ℕ) : ℤ) ((k' : ℕ) :
                ℤ)‖ :=
          Finset.single_le_sum (f := fun m' : ℕ => ∑ k' ∈ range M, ‖a A N₁ ((m'
              : ℕ) : ℤ) ((k' :
              ℕ) : ℤ)‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
                (mem_range.mpr hsmall.1)
        exact h1a.trans h1b
      exact h1.trans (le_mul_of_one_le_right hK0 (one_le_pow₀ hC1))
    · have hMor : (M : ℤ) ≤ m ∨ (M : ℤ) ≤ k := by
        rcases not_and_or.mp hsmall with h | h
        · exact Or.inl (by exact_mod_cast not_lt.mp h)
        · exact Or.inr (by exact_mod_cast not_lt.mp h)
      have h0 := hrec m k (by positivity) (by positivity) hMor
      rw [e₁₂_eq_add_sum_erase] at h0
      have heq : D₁.coeff 0 * D₂.coeff 0 * a A N₁ m k =
          -∑ x ∈ s, D₁.coeff x.1 * D₂.coeff x.2 * a A N₁ ((m : ℤ) - x.1) ((k :
              ℤ) - x.2) :=
        eq_neg_of_add_eq_zero_left h0
      have hterm : ∀ x ∈ s, ‖a A N₁ ((m : ℤ) - x.1) ((k : ℤ) - x.2)‖ ≤ K * C ^
          (n - 1) := by
        intro x hx
        have hx0 : x ≠ (0, 0) := (Finset.mem_erase.mp hx).1
        by_cases hneg : (m : ℤ) - x.1 < 0 ∨ (k : ℤ) - x.2 < 0
        · rw [hsupp _ _ hneg, norm_zero]; positivity
        · push Not at hneg
          obtain ⟨h1, h2⟩ := hneg
          have hx1 : x.1 ≤ m := by omega
          have hx2 : x.2 ≤ k := by omega
          have hsum : 1 ≤ x.1 + x.2 := by
            rcases x with ⟨p, l⟩
            simp only [ne_eq, Prod.mk.injEq, not_and_or] at hx0
            simp only; omega
          have hlt : (m - x.1) + (k - x.2) < n := by omega
          have hle : (m - x.1) + (k - x.2) ≤ n - 1 := by omega
          have := ih _ hlt (m - x.1) (k - x.2) rfl
          rw [show ((m : ℤ) - x.1) = ((m - x.1 : ℕ) : ℤ) by omega,
            show ((k : ℤ) - x.2) = ((k - x.2 : ℕ) : ℤ) by omega]
          exact this.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC1
              hle) hK0)
      have hbound : c₀ * ‖a A N₁ m k‖ ≤ S * (K * C ^ (n - 1)) := by
        have : c₀ * ‖a A N₁ m k‖ = ‖∑ x ∈ s, D₁.coeff x.1 * D₂.coeff x.2 * a A
            N₁ ((m : ℤ) - x.1)
            ((k : ℤ) - x.2)‖ := by
          rw [hc₀, ← norm_mul, heq, norm_neg]
        rw [this, hS, Finset.sum_mul]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hterm x hx) (norm_nonneg _)
      have hbound' : ‖a A N₁ m k‖ ≤ C * (K * C ^ (n - 1)) := by
        have : ‖a A N₁ m k‖ ≤ S / c₀ * (K * C ^ (n - 1)) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hc₀pos, mul_comm]
          exact hbound
        exact this.trans (mul_le_mul_of_nonneg_right hCS (by positivity))
      rcases Nat.eq_zero_or_pos n with hn | hn
      · have hm0 : m = 0 := by omega
        have hk0 : k = 0 := by omega
        have hz : ∑ x ∈ s, D₁.coeff x.1 * D₂.coeff x.2 * a A N₁ ((m : ℤ) - x.1)
            ((k : ℤ) - x.2) =
            0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hx0 : x ≠ (0, 0) := (Finset.mem_erase.mp hx).1
          have : (m : ℤ) - x.1 < 0 ∨ (k : ℤ) - x.2 < 0 := by
            rcases x with ⟨p, l⟩
            simp only [ne_eq, Prod.mk.injEq, not_and_or] at hx0
            simp only [hm0, hk0, Nat.cast_zero, zero_sub, neg_lt_zero,
                Nat.cast_pos]
            omega
          rw [hsupp _ _ this, mul_zero]
        rw [hz, neg_zero] at heq
        have : a A N₁ m k = 0 := (mul_eq_zero.mp heq).resolve_left (mul_ne_zero
            hD₁ hD₂)
        rw [this, norm_zero]; positivity
      · have hpow : C ^ n = C ^ (n - 1) * C := by
          rw [← pow_succ, Nat.sub_add_cancel hn]
        calc ‖a A N₁ m k‖ ≤ C * (K * C ^ (n - 1)) := hbound'
          _ = K * C ^ n := by rw [hpow]; ring

private def h (b₁ b₂ : ℂ) (m : ℕ) : ℂ := ∑ i ∈ range (m + 1), b₁ ^ i * b₂ ^ (m -
    i)

private theorem norm_h_le (b₁ b₂ : ℂ) (m : ℕ) :
    ‖h b₁ b₂ m‖ ≤ (m + 1) * (max 1 (max ‖b₁‖ ‖b₂‖)) ^ m := by
  set β := max 1 (max ‖b₁‖ ‖b₂‖) with hβ
  have hβ1 : 1 ≤ β := le_max_left _ _
  have hb₁ : ‖b₁‖ ≤ β := (le_max_left _ _).trans (le_max_right _ _)
  have hb₂ : ‖b₂‖ ≤ β := (le_max_right _ _).trans (le_max_right _ _)
  unfold h
  refine (norm_sum_le _ _).trans ?_
  have : ∀ i ∈ range (m + 1), ‖b₁ ^ i * b₂ ^ (m - i)‖ ≤ β ^ m := by
    intro i hi
    have him : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖b₁‖ ^ i * ‖b₂‖ ^ (m - i) ≤ β ^ i * β ^ (m - i) := by
          gcongr
      _ = β ^ m := by rw [← pow_add, Nat.add_sub_cancel' him]
  refine (Finset.sum_le_sum this).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring_nf
  rfl

private theorem summable_norm_box (K C : ℝ) (hK : 0 ≤ K) (hC : 1 ≤ C)
    (hgrowth : ∀ m k : ℕ, ‖a A N₁ m k‖ ≤ K * C ^ (m + k)) (b₁ b₂ X Y : ℂ)
    (hX : ‖X‖ < 1 / (2 * C * max 1 (max ‖b₁‖ ‖b₂‖))) (hY : ‖Y‖ < 1 / (2 * C *
        max 1 (max ‖b₁‖
        ‖b₂‖))) :
    Summable (fun mk : ℕ × ℕ => ‖a A N₁ mk.1 mk.2 * h b₁ b₂ mk.1 * X ^ mk.1 * Y
        ^ mk.2‖) := by
  set β := max 1 (max ‖b₁‖ ‖b₂‖) with hβ
  have hβ1 : 1 ≤ β := le_max_left _ _
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos hβ1
  set ρ₁ : ℝ := C * β * ‖X‖ with hρ₁
  set ρ₂ : ℝ := C * ‖Y‖ with hρ₂
  have hρ₁0 : 0 ≤ ρ₁ := by positivity
  have hρ₂0 : 0 ≤ ρ₂ := by positivity
  have hden : 0 < 2 * C * β := by positivity
  have hρ₁1 : ρ₁ < 1 := by
    have := (lt_div_iff₀ hden).mp hX
    rw [hρ₁]; nlinarith
  have hρ₂1 : ρ₂ < 1 := by
    have h1 := (lt_div_iff₀ hden).mp hY
    rw [hρ₂]; nlinarith [norm_nonneg Y]
  have hs₁ : Summable (fun m : ℕ => ((m : ℝ) + 1) * ρ₁ ^ m) := by
    have h1 : Summable (fun m : ℕ => ((m : ℝ) ^ 1 : ℝ) * ρ₁ ^ m) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by
        rw [Real.norm_eq_abs, abs_of_nonneg hρ₁0]
        exact hρ₁1)
    have h2 : Summable (fun m : ℕ => ρ₁ ^ m) := summable_geometric_of_lt_one
        hρ₁0 hρ₁1
    simpa [pow_one, add_mul] using h1.add h2
  have hs₂ : Summable (fun k : ℕ => ρ₂ ^ k) := summable_geometric_of_lt_one hρ₂0
      hρ₂1
  have hprod : Summable (fun mk : ℕ × ℕ => (K * (((mk.1 : ℝ) + 1) * ρ₁ ^ mk.1))
      * ρ₂ ^ mk.2) := by
    have := (hs₁.mul_left K).mul_of_nonneg hs₂ (fun m => by positivity) (fun k
        => by positivity)
    exact this
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun mk => ?_) hprod
  obtain ⟨m, k⟩ := mk
  simp only
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
  calc ‖a A N₁ m k‖ * ‖h b₁ b₂ m‖ * ‖X‖ ^ m * ‖Y‖ ^ k
      ≤ (K * C ^ (m + k)) * ((m + 1) * β ^ m) * ‖X‖ ^ m * ‖Y‖ ^ k := by
        gcongr
        · exact hgrowth m k
        · exact norm_h_le b₁ b₂ m
    _ = K * ((m + 1) * ρ₁ ^ m) * ρ₂ ^ k := by
        rw [hρ₁, hρ₂, pow_add, mul_pow, mul_pow, mul_pow]; ring

private theorem tsum_mul_monomial_eq_tsum_shift
    (u : ℕ → ℕ → ℂ) (X Y : ℂ) (s t : ℕ) :
    (∑' mk : ℕ × ℕ, u mk.1 mk.2 * X ^ mk.1 * Y ^ mk.2) * (X ^ s * Y ^ t) =
      ∑' mk : ℕ × ℕ, (if s ≤ mk.1 ∧ t ≤ mk.2 then u (mk.1 - s) (mk.2 - t) * X ^
          mk.1 * Y ^ mk.2
          else 0) := by
  rw [← tsum_mul_right]
  have hinj : Function.Injective (fun mk : ℕ × ℕ => (mk.1 + s, mk.2 + t)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (by omega) (by omega)
  rw [← hinj.tsum_eq (f := fun mk : ℕ × ℕ =>
      (if s ≤ mk.1 ∧ t ≤ mk.2 then u (mk.1 - s) (mk.2 - t) * X ^ mk.1 * Y ^ mk.2
          else 0))]
  · refine tsum_congr fun mk => ?_
    simp only [le_add_iff_nonneg_left, zero_le, and_self, ite_true,
        Nat.add_sub_cancel, pow_add]
    ring
  · intro mk hmk
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall,
        exists_prop] at hmk
    obtain ⟨⟨h1, h2⟩, _⟩ := hmk
    exact ⟨(mk.1 - s, mk.2 - t), by simp only [Nat.sub_add_cancel h1,
        Nat.sub_add_cancel h2]⟩

private theorem summable_shift (u : ℕ → ℕ → ℂ) (X Y : ℂ) (s t : ℕ)
    (hs : Summable (fun mk : ℕ × ℕ => u mk.1 mk.2 * X ^ mk.1 * Y ^ mk.2)) :
    Summable (fun mk : ℕ × ℕ =>
      (if s ≤ mk.1 ∧ t ≤ mk.2 then u (mk.1 - s) (mk.2 - t) * X ^ mk.1 * Y ^ mk.2
          else 0)) := by
  have hinj : Function.Injective (fun mk : ℕ × ℕ => (mk.1 + s, mk.2 + t)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (by omega) (by omega)
  refine (hinj.summable_iff (f := fun mk : ℕ × ℕ =>
      (if s ≤ mk.1 ∧ t ≤ mk.2 then u (mk.1 - s) (mk.2 - t) * X ^ mk.1 * Y ^ mk.2
          else 0)) ?_).mp
          ?_
  · intro mk hmk
    simp only [Set.mem_range, not_exists] at hmk
    by_cases h : s ≤ mk.1 ∧ t ≤ mk.2
    · exact absurd (hmk (mk.1 - s, mk.2 - t)) (by simp only [Nat.sub_add_cancel
        h.1,
        Nat.sub_add_cancel h.2, not_true_eq_false, not_false_eq_true])
    · simp only [ite_eq_right h]
  · have : (fun mk : ℕ × ℕ => (if s ≤ mk.1 ∧ t ≤ mk.2 then u (mk.1 - s) (mk.2 -
      t) * X ^ mk.1 * Y
      ^ mk.2 else 0)) ∘
        (fun mk : ℕ × ℕ => (mk.1 + s, mk.2 + t)) = fun mk : ℕ × ℕ => (u mk.1
            mk.2 * X ^ mk.1 * Y ^
            mk.2) * (X ^ s * Y ^ t) := by
      funext mk
      simp only [Function.comp_apply, le_add_iff_nonneg_left, zero_le, and_self,
          ite_true,
          Nat.add_sub_cancel, pow_add]
      ring
    rw [this]
    exact hs.mul_right _

private theorem pow_mul_pow_mul_h (b₁ b₂ : ℂ) (p r n : ℕ) :
    b₁ ^ p * b₂ ^ r * h b₁ b₂ n =
      ∑ i ∈ range (p + r + n + 1), (if p ≤ i ∧ i ≤ p + n then b₁ ^ i * b₂ ^ (p +
          r + n - i) else
          0) := by
  unfold h
  rw [Finset.mul_sum]
  have : ∑ i' ∈ range (n + 1), b₁ ^ p * b₂ ^ r * (b₁ ^ i' * b₂ ^ (n - i')) =
      ∑ i' ∈ range (n + 1), b₁ ^ (p + i') * b₂ ^ (p + r + n - (p + i')) := by
    refine sum_congr rfl fun i' hi' => ?_
    have : i' ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi')
    rw [show p + r + n - (p + i') = r + (n - i') by omega, pow_add, pow_add]
    ring
  rw [this]
  symm
  rw [← Finset.sum_filter]
  have hwin : (range (p + r + n + 1)).filter (fun i => p ≤ i ∧ i ≤ p + n) =
      (range (n + 1)).map
      (addLeftEmbedding p) := by
    ext i
    simp only [mem_filter, mem_range, mem_map, addLeftEmbedding_apply]
    constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨i - p, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨by omega, by omega, by omega⟩
  rw [hwin, Finset.sum_map]
  rfl

private theorem sum_range_extend (f : ℕ → ℂ) {n N : ℕ} (h : n ≤ N) (hf : ∀ j, n
    ≤ j → f j = 0) :
    ∑ j ∈ range n, f j = ∑ j ∈ range N, f j :=
  Finset.sum_subset (range_subset_range.mpr h) fun j _ hj => hf j (by simpa
      using hj)

private def S (b₁ b₂ : ℂ) (m k p r l i : ℕ) : ℂ :=
  if p ≤ i ∧ i + r ≤ m ∧ l ≤ k then
    D₁.coeff p * D₁.coeff r * D₂.coeff l * a A N₁ ((m : ℤ) - p - r) ((k : ℤ) -
        l) * b₁ ^ i * b₂ ^
        (m - i)
  else 0

private theorem S_eq_zero_of (b₁ b₂ : ℂ) (m k p r l i : ℕ)
    (h : D₁.natDegree < p ∨ D₁.natDegree < r ∨ D₂.natDegree < l ∨ i < p ∨ m < i
        + r ∨ k < l) :
    S (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ m k p r l i = 0 := by
  unfold S
  rcases h with h | h | h | h | h | h
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]; simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]; simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]; simp
  · rw [ite_eq_right (by omega)]
  · rw [ite_eq_right (by omega)]
  · rw [ite_eq_right (by omega)]

private def c (b₁ b₂ : ℂ) (m k : ℕ) : ℂ :=
  ∑ p ∈ range (D₁.natDegree + 1), ∑ r ∈ range (D₁.natDegree + 1), ∑ l ∈ range
      (D₂.natDegree + 1),
    (if p + r ≤ m ∧ l ≤ k then
      D₁.coeff p * D₁.coeff r * D₂.coeff l * b₁ ^ p * b₂ ^ r *
        (a A N₁ ((m : ℤ) - p - r) ((k : ℤ) - l) * h b₁ b₂ (m - p - r)) else 0)

private theorem c_term_eq_sum_S (b₁ b₂ : ℂ) (m k p r l : ℕ) :
    (if p + r ≤ m ∧ l ≤ k then
      D₁.coeff p * D₁.coeff r * D₂.coeff l * b₁ ^ p * b₂ ^ r *
        (a A N₁ ((m : ℤ) - p - r) ((k : ℤ) - l) * h b₁ b₂ (m - p - r)) else 0) =
      ∑ i ∈ range (m + 1), S (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ m k
          p r l i := by
  by_cases hc : p + r ≤ m ∧ l ≤ k
  · rw [ite_eq_left hc]
    have hw := pow_mul_pow_mul_h b₁ b₂ p r (m - p - r)
    have hm : p + r + (m - p - r) = m := by omega
    rw [hm] at hw
    calc D₁.coeff p * D₁.coeff r * D₂.coeff l * b₁ ^ p * b₂ ^ r *
          (a A N₁ ((m : ℤ) - p - r) ((k : ℤ) - l) * h b₁ b₂ (m - p - r))
        = D₁.coeff p * D₁.coeff r * D₂.coeff l * a A N₁ ((m : ℤ) - p - r) ((k :
            ℤ) - l) *
            (b₁ ^ p * b₂ ^ r * h b₁ b₂ (m - p - r)) := by ring
      _ = ∑ i ∈ range (m + 1), D₁.coeff p * D₁.coeff r * D₂.coeff l * a A N₁ ((m
          : ℤ) - p - r) ((k
          : ℤ) - l) *
            (if p ≤ i ∧ i ≤ p + (m - p - r) then b₁ ^ i * b₂ ^ (m - i) else 0)
                := by
          rw [hw, Finset.mul_sum]
      _ = ∑ i ∈ range (m + 1), S (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂
          m k p r l i := by
          refine sum_congr rfl fun i _ => ?_
          unfold S
          by_cases hi : p ≤ i ∧ i + r ≤ m
          · rw [ite_eq_left (by omega), ite_eq_left ⟨hi.1, hi.2, hc.2⟩]; ring
          · rw [ite_eq_right (by omega), ite_eq_right (by tauto)]; ring
  · rw [ite_eq_right hc]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    unfold S
    rw [ite_eq_right]
    omega

private theorem c_eq_sum_q (b₁ b₂ : ℂ) (m k : ℕ) :
    c (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ m k =
      ∑ i ∈ range (m + 1), q A N₁ D₁ D₂ i (m - i) k * b₁ ^ i * b₂ ^ (m - i) :=
          by
  set B := m + D₁.natDegree + 1 with hB
  set B₂ := k + D₂.natDegree + 1 with hB₂
  set NF : ℕ → ℂ := fun i => ∑ p ∈ range B, ∑ r ∈ range B, ∑ l ∈ range B₂,
      S (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ m k p r l i with hNF
  have L : c (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ m k = ∑ i ∈ range
      (m + 1), NF i := by
    have step1 : c (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ m k =
        ∑ p ∈ range (D₁.natDegree + 1), ∑ r ∈ range (D₁.natDegree + 1), ∑ l ∈
            range (D₂.natDegree
            + 1),
          ∑ i ∈ range (m + 1), S (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂
              m k p r l i := by
      unfold c
      exact sum_congr rfl fun p _ => sum_congr rfl fun r _ => sum_congr rfl fun
          l _ =>
          c_term_eq_sum_S b₁ b₂ m k p r l
    rw [step1]
    rw [sum_range_extend _ (show D₁.natDegree + 1 ≤ B by omega) (fun p hp =>
      Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun l _ =>
          Finset.sum_eq_zero fun i _ =>
        S_eq_zero_of b₁ b₂ m k p r l i (Or.inl (by omega)))]
    have e2 : ∀ p, (∑ r ∈ range (D₁.natDegree + 1), ∑ l ∈ range (D₂.natDegree +
        1), ∑ i ∈ range (m
        + 1),
        S (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ m k p r l i) =
        ∑ r ∈ range B, ∑ l ∈ range B₂, ∑ i ∈ range (m + 1),
          S (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ m k p r l i := by
      intro p
      rw [sum_range_extend _ (show D₁.natDegree + 1 ≤ B by omega) (fun r hr =>
        Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun i _ =>
          S_eq_zero_of b₁ b₂ m k p r l i (Or.inr (Or.inl (by omega))))]
      refine sum_congr rfl fun r _ => ?_
      exact sum_range_extend _ (show D₂.natDegree + 1 ≤ B₂ by omega) (fun l hl
          =>
        Finset.sum_eq_zero fun i _ => S_eq_zero_of b₁ b₂ m k p r l i (Or.inr
            (Or.inr (Or.inl (by
            omega)))))
    simp only [e2, hNF]
    calc ∑ p ∈ range B, ∑ r ∈ range B, ∑ l ∈ range B₂, ∑ i ∈ range (m + 1),
            S (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ m k p r l i
        = ∑ p ∈ range B, ∑ r ∈ range B, ∑ i ∈ range (m + 1), ∑ l ∈ range B₂,
            S (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ m k p r l i :=
          sum_congr rfl fun p _ => sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ p ∈ range B, ∑ i ∈ range (m + 1), ∑ r ∈ range B, ∑ l ∈ range B₂,
            S (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ m k p r l i :=
          sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ i ∈ range (m + 1), ∑ p ∈ range B, ∑ r ∈ range B, ∑ l ∈ range B₂,
            S (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ m k p r l i :=
                Finset.sum_comm
  have R : ∀ i ∈ range (m + 1), q A N₁ D₁ D₂ i (m - i) k * b₁ ^ i * b₂ ^ (m - i)
      = NF i := by
    intro i hi
    have him : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have step : q A N₁ D₁ D₂ i (m - i) k * b₁ ^ i * b₂ ^ (m - i) =
        ∑ p ∈ range (i + 1), ∑ r ∈ range (m - i + 1), ∑ l ∈ range (k + 1),
          S (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ m k p r l i := by
      unfold q
      rw [Finset.sum_mul, Finset.sum_mul]
      refine sum_congr rfl fun p hp => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine sum_congr rfl fun r hr => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine sum_congr rfl fun l hl => ?_
      have hp' : p ≤ i := Nat.lt_succ_iff.mp (mem_range.mp hp)
      have hr' : r ≤ m - i := Nat.lt_succ_iff.mp (mem_range.mp hr)
      have hl' : l ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hl)
      unfold S
      rw [ite_eq_left ⟨hp', by omega, hl'⟩]
      have : (i : ℤ) + ((m - i : ℕ) : ℤ) - p - r = (m : ℤ) - p - r := by omega
      rw [this]
    rw [step, hNF]
    rw [sum_range_extend _ (show i + 1 ≤ B by omega) (fun p hp =>
      Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun l _ =>
        S_eq_zero_of b₁ b₂ m k p r l i (Or.inr (Or.inr (Or.inr (Or.inl (by
            omega))))))]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_range_extend _ (show m - i + 1 ≤ B by omega) (fun r hr =>
      Finset.sum_eq_zero fun l _ =>
        S_eq_zero_of b₁ b₂ m k p r l i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            (by omega)))))))]
    refine sum_congr rfl fun r _ => ?_
    exact sum_range_extend _ (show k + 1 ≤ B₂ by omega) (fun l hl =>
      S_eq_zero_of b₁ b₂ m k p r l i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
          omega)))))))
  rw [L]
  exact (sum_congr rfl R).symm

private theorem eval_prod_eq_sum (D₁ D₂ : Polynomial ℂ) (b₁ b₂ X Y : ℂ) :
    D₁.eval (b₁ * X) * D₁.eval (b₂ * X) * D₂.eval Y =
      ∑ p ∈ range (D₁.natDegree + 1), ∑ r ∈ range (D₁.natDegree + 1), ∑ l ∈
          range (D₂.natDegree +
          1),
        (D₁.coeff p * D₁.coeff r * D₂.coeff l * b₁ ^ p * b₂ ^ r) * (X ^ (p + r)
            * Y ^ l) := by
  simp only [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  refine sum_congr rfl fun p _ => ?_
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun r _ => sum_congr rfl fun l _ => ?_
  rw [mul_pow, mul_pow, pow_add]; ring

end Polynomial.SeparatedTorus

open Polynomial.SeparatedTorus

/-- A separated recurrence has one polynomial numerator for every pair of
complex weight parameters, including equal and zero parameters. The finite
coefficient formula fixes that numerator before the parameters are chosen.
Only the positive radius may depend on them. -/
public theorem Polynomial.exists_torusWeight_sum
    (A : ℤ × ℤ → ℂ) (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ)
    (hD₁ : D₁.eval 0 ≠ 0) (hD₂ : D₂.eval 0 ≠ 0)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0)
    (hrec : ∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
      ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree +
          1),
        D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l
            : ℤ)) = 0) :
    ∃ P : MvPolynomial (Fin 4) ℂ,
      P = (∑ m ∈ range (2 * max M D₁.natDegree), ∑ k ∈ range M,
        ∑ i ∈ range (m + 1),
          MvPolynomial.C (∑ p ∈ range (i + 1), ∑ t ∈ range (m - i + 1),
            ∑ l ∈ range (k + 1),
              D₁.coeff p * D₁.coeff t * D₂.coeff l *
                A (N₁ + ((i : ℤ) + (m - i : ℕ) - p - t),
                  N₁ + ((k : ℤ) - l))) *
            MvPolynomial.X 0 ^ m * MvPolynomial.X 1 ^ k *
            MvPolynomial.X 2 ^ i * MvPolynomial.X 3 ^ (m - i)) ∧
      ∀ b₁ b₂ : ℂ, ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ =>
        ‖A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) *
          (∑ i ∈ Finset.range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) * X ^ m.1 * Y
              ^ m.2‖) ∧
      (∑' m : ℕ × ℕ,
          A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) *
            (∑ i ∈ Finset.range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) * X ^ m.1 *
                Y ^ m.2) *
        (D₁.eval (b₁ * X) * D₁.eval (b₂ * X) * D₂.eval Y) =
        MvPolynomial.eval (![X, Y, b₁, b₂] : Fin 4 → ℂ) P := by
  classical
  have hD₁' : D₁.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
  have hD₂' : D₂.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
  have hsupp' : ∀ m k : ℤ, (m < 0 ∨ k < 0) → a A N₁ m k = 0 := by
    intro m k hmk
    unfold a
    exact hsupp _ (by rcases hmk with h | h <;> [left; right] <;> simp only <;>
        omega)
  have hrec' : ∀ m k : ℤ, 0 ≤ m → 0 ≤ k → ((M : ℤ) ≤ m ∨ (M : ℤ) ≤ k) → e₁₂ A N₁
      D₁ D₂ m k = 0 :=
      by
    intro m k hm hk hM
    obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le hm
    obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have hM' : M ≤ m' ∨ M ≤ k' := by rcases hM with h | h <;> [left; right] <;>
        exact_mod_cast h
    rw [← hrec m' k' hM']
    unfold e₁₂ a
    refine sum_congr rfl fun p _ => sum_congr rfl fun l _ => ?_
    rw [show N₁ + ((m' : ℕ) : ℤ) - (p : ℤ) = N₁ + (((m' : ℕ) : ℤ) - p) by ring,
      show N₁ + ((k' : ℕ) : ℤ) - (l : ℤ) = N₁ + (((k' : ℕ) : ℤ) - l) by ring]
  obtain ⟨K, C, hK, hC, hgr⟩ := growth hD₁' hD₂' hsupp' hrec'
  set M' : ℕ := max M D₁.natDegree with hM'
  refine ⟨∑ m ∈ range (2 * M'), ∑ k ∈ range M, ∑ i ∈ range (m + 1),
      MvPolynomial.C (q A N₁ D₁ D₂ i (m - i) k) * MvPolynomial.X 0 ^ m *
          MvPolynomial.X 1 ^ k *
        MvPolynomial.X 2 ^ i * MvPolynomial.X 3 ^ (m - i), rfl, ?_⟩
  intro b₁ b₂
  have hβ : 0 < max 1 (max ‖b₁‖ ‖b₂‖) := lt_of_lt_of_le one_pos (le_max_left _
      _)
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  refine ⟨1 / (2 * C * max 1 (max ‖b₁‖ ‖b₂‖)), by positivity, ?_⟩
  intro X Y hX hY
  have hsum := summable_norm_box K C hK hC hgr b₁ b₂ X Y hX hY
  refine ⟨hsum, ?_⟩
  have hs : Summable (fun mk : ℕ × ℕ => (a A N₁ mk.1 mk.2 * h b₁ b₂ mk.1) * X ^
      mk.1 * Y ^ mk.2)
      :=
    hsum.of_norm
  set u : ℕ → ℕ → ℂ := fun m k => a A N₁ m k * h b₁ b₂ m with hu
  have hs' : Summable (fun mk : ℕ × ℕ => u mk.1 mk.2 * X ^ mk.1 * Y ^ mk.2) :=
      hs
  have e0 : (∑' mk : ℕ × ℕ, A (N₁ + (mk.1 : ℤ), N₁ + (mk.2 : ℤ)) *
        (∑ i ∈ range (mk.1 + 1), b₁ ^ i * b₂ ^ (mk.1 - i)) * X ^ mk.1 * Y ^
            mk.2) =
      ∑' mk : ℕ × ℕ, u mk.1 mk.2 * X ^ mk.1 * Y ^ mk.2 := by
    refine tsum_congr fun mk => ?_
    simp only [hu, a, h]
  rw [e0, eval_prod_eq_sum]
  rw [Finset.mul_sum]
  have e1 : ∀ p r l : ℕ,
      (∑' mk : ℕ × ℕ, u mk.1 mk.2 * X ^ mk.1 * Y ^ mk.2) *
        ((D₁.coeff p * D₁.coeff r * D₂.coeff l * b₁ ^ p * b₂ ^ r) * (X ^ (p + r)
            * Y ^ l)) =
      ∑' mk : ℕ × ℕ, (D₁.coeff p * D₁.coeff r * D₂.coeff l * b₁ ^ p * b₂ ^ r) *
        (if p + r ≤ mk.1 ∧ l ≤ mk.2 then u (mk.1 - (p + r)) (mk.2 - l) * X ^
            mk.1 * Y ^ mk.2 else
            0) := by
    intro p r l
    rw [tsum_mul_left, ← tsum_mul_monomial_eq_tsum_shift u X Y (p + r) l]
    ring
  have hsumshift : ∀ p r l : ℕ, Summable (fun mk : ℕ × ℕ => (D₁.coeff p *
      D₁.coeff r * D₂.coeff l
      * b₁ ^ p * b₂ ^ r) *
        (if p + r ≤ mk.1 ∧ l ≤ mk.2 then u (mk.1 - (p + r)) (mk.2 - l) * X ^
            mk.1 * Y ^ mk.2 else
            0)) :=
    fun p r l => (summable_shift u X Y (p + r) l hs').mul_left _
  have e2 : ∑ p ∈ range (D₁.natDegree + 1), (∑' mk : ℕ × ℕ, u mk.1 mk.2 * X ^
      mk.1 * Y ^ mk.2) *
        ∑ r ∈ range (D₁.natDegree + 1), ∑ l ∈ range (D₂.natDegree + 1),
          (D₁.coeff p * D₁.coeff r * D₂.coeff l * b₁ ^ p * b₂ ^ r) * (X ^ (p +
              r) * Y ^ l) =
      ∑' mk : ℕ × ℕ, c (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ mk.1 mk.2
          * X ^ mk.1 * Y ^
          mk.2 := by
    have : ∀ p ∈ range (D₁.natDegree + 1), (∑' mk : ℕ × ℕ, u mk.1 mk.2 * X ^
        mk.1 * Y ^ mk.2) *
        ∑ r ∈ range (D₁.natDegree + 1), ∑ l ∈ range (D₂.natDegree + 1),
          (D₁.coeff p * D₁.coeff r * D₂.coeff l * b₁ ^ p * b₂ ^ r) * (X ^ (p +
              r) * Y ^ l) =
        ∑' mk : ℕ × ℕ, ∑ r ∈ range (D₁.natDegree + 1), ∑ l ∈ range (D₂.natDegree
            + 1),
          (D₁.coeff p * D₁.coeff r * D₂.coeff l * b₁ ^ p * b₂ ^ r) *
            (if p + r ≤ mk.1 ∧ l ≤ mk.2 then u (mk.1 - (p + r)) (mk.2 - l) * X ^
                mk.1 * Y ^ mk.2
                else 0) := by
      intro p _
      rw [Finset.mul_sum, Summable.tsum_finsetSum (fun r _ => summable_sum fun l
          _ => hsumshift p
          r l)]
      refine sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum, Summable.tsum_finsetSum (fun l _ => hsumshift p r l)]
      exact sum_congr rfl fun l _ => e1 p r l
    rw [sum_congr rfl this, ← Summable.tsum_finsetSum (fun p _ => summable_sum
        fun r _ =>
        summable_sum fun l _ => hsumshift p r l)]
    refine tsum_congr fun mk => ?_
    unfold c
    rw [Finset.sum_mul, Finset.sum_mul]
    refine sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine sum_congr rfl fun r _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine sum_congr rfl fun l _ => ?_
    by_cases hc : p + r ≤ mk.1 ∧ l ≤ mk.2
    · rw [ite_eq_left hc, ite_eq_left hc, hu]
      simp only [Nat.sub_sub]
      rw [show ((mk.1 : ℤ) - p - r) = ((mk.1 - (p + r) : ℕ) : ℤ) by omega,
        show ((mk.2 : ℤ) - l) = ((mk.2 - l : ℕ) : ℤ) by omega]
      ring
    · rw [ite_eq_right hc, ite_eq_right hc]; ring
  rw [e2]
  have e3 : ∀ mk : ℕ × ℕ, c (A := A) (N₁ := N₁) (D₁ := D₁) (D₂ := D₂) b₁ b₂ mk.1
      mk.2 * X ^ mk.1 *
      Y ^ mk.2 =
      (∑ i ∈ range (mk.1 + 1), q A N₁ D₁ D₂ i (mk.1 - i) mk.2 * b₁ ^ i * b₂ ^
          (mk.1 - i)) * X ^
          mk.1 * Y ^ mk.2 :=
    fun mk => by rw [c_eq_sum_q]
  simp only [e3]
  have hvan : ∀ mk : ℕ × ℕ, mk ∉ range (2 * M') ×ˢ range M →
      (∑ i ∈ range (mk.1 + 1), q A N₁ D₁ D₂ i (mk.1 - i) mk.2 * b₁ ^ i * b₂ ^
          (mk.1 - i)) * X ^
          mk.1 * Y ^ mk.2 = 0 := by
    intro mk hmk
    rw [Finset.mem_product, mem_range, mem_range, not_and_or, not_lt,
      not_lt] at hmk
    have : ∑ i ∈ range (mk.1 + 1), q A N₁ D₁ D₂ i (mk.1 - i) mk.2 * b₁ ^ i * b₂
        ^ (mk.1 - i) = 0
        := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have him : i ≤ mk.1 := Nat.lt_succ_iff.mp (mem_range.mp hi)
      rw [q_eq_zero hD₁' hD₂' hsupp' hrec' (M := M) ?_, zero_mul, zero_mul]
      rcases hmk with h | h
      · by_cases hi' : M' ≤ i
        · exact Or.inl hi'
        · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr h)
    rw [this, zero_mul, zero_mul]
  rw [tsum_eq_sum (s := range (2 * M') ×ˢ range M) hvan, Finset.sum_product]
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_pow,
    MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine sum_congr rfl fun m _ => sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine sum_congr rfl fun i _ => ?_
  simp only [Fin.succ_zero_eq_one, Matrix.cons_val_one,
    show ((3 : Fin 4)) = Fin.succ (Fin.succ (Fin.succ 0)) from rfl, show ((2 :
        Fin 4)) = Fin.succ
        (Fin.succ 0) from rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  ring
