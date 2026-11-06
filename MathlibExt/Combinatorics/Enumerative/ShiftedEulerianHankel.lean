/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
import MathlibExt.Combinatorics.Enumerative.HeilermannWeightedMotzkinDeterminant
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit
import MathlibExt.NumberTheory.HankelTransform
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

/-- Level-step weights of the Eulerian production matrix. -/
private def euAlpha (x : ℝ) (k : ℕ) : ℝ := (k + 1) * (x + 1)

/-- Down-step weights of the Eulerian production matrix. -/
private def euBeta (x : ℝ) (k : ℕ) : ℝ := k * (k + 1) * x

/-- Closed-form coefficients of the Eulerian moment triangle:
`m ! * C (m + 1) (k + 1) * S (n + 1) (m + 1)`. -/
private def euC (n k m : ℕ) : ℕ :=
  Nat.factorial m * (m + 1).choose (k + 1) * Nat.stirlingSecond (n + 1) (m + 1)

/-- Unnormalized Eulerian triangle rows as polynomials in `x - 1`. -/
private def euS (x : ℝ) (n k : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), (euC n k m : ℝ) * (x - 1) ^ (n - m)

/-- Normalized Eulerian moment triangle fed to the weighted-Motzkin lemma. -/
private noncomputable def euM (x : ℝ) (n k : ℕ) : ℝ :=
  euS x n k / (Nat.factorial k : ℝ)

/-- Hockey-stick identity. -/
private theorem hockey_stick (N r : ℕ) :
    ∑ i ∈ Finset.range (N + 1), i.choose r = (N + 1).choose (r + 1) := by
  induction N with
  | zero =>
    change ∑ i ∈ Finset.range 1, i.choose r = (1 : ℕ).choose (r + 1)
    rw [Finset.sum_range_one]
    cases r with
    | zero => rfl
    | succ j =>
      rw [Nat.choose_eq_zero_of_lt (by omega : 0 < j + 1),
        Nat.choose_eq_zero_of_lt (by omega : 1 < j + 1 + 1)]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ (N + 1) r]
    ring

/-- Hockey-stick convolution. -/
private theorem hockey_conv (N r s : ℕ) :
    ∑ i ∈ Finset.range (N + 1), i.choose r * (N - i).choose s
      = (N + 1).choose (r + s + 1) := by
  induction N generalizing s with
  | zero =>
    have h1 : (0 : ℕ) + 1 = 1 := rfl
    rw [h1, Finset.sum_range_one]
    simp only [Nat.sub_zero]
    cases r with
    | zero =>
      cases s with
      | zero => simp
      | succ s =>
        have e1 : Nat.choose 0 (s + 1) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        have e2 : Nat.choose 1 (0 + (s + 1) + 1) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        rw [e1, e2, mul_zero]
    | succ r =>
      have e1 : Nat.choose 0 (r + 1) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      have e2 : Nat.choose 1 (r + 1 + s + 1) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      rw [e1, e2, zero_mul]
  | succ N ih =>
    cases s with
    | zero =>
      simp only [Nat.choose_zero_right, mul_one]
      simpa using hockey_stick (N + 1) r
    | succ j =>
      rw [Finset.sum_range_succ]
      have hlast : (N + 1 - (N + 1)).choose (j + 1) = 0 := by
        rw [Nat.sub_self]
        exact Nat.choose_eq_zero_of_lt (by omega)
      rw [hlast, mul_zero, add_zero]
      have hpas : ∀ i ∈ Finset.range (N + 1),
          (N + 1 - i).choose (j + 1)
            = (N - i).choose (j + 1) + (N - i).choose j := by
        intro i hi
        have hiN : i ≤ N := by
          have := Finset.mem_range.mp hi
          omega
        have hsub : N + 1 - i = (N - i) + 1 := by omega
        rw [hsub, Nat.choose_succ_succ]
        ring
      have hsum : ∑ i ∈ Finset.range (N + 1), i.choose r * (N + 1 - i).choose (j + 1)
          = ∑ i ∈ Finset.range (N + 1),
              i.choose r * ((N - i).choose (j + 1) + (N - i).choose j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hpas i hi]
      rw [hsum]
      simp only [mul_add, Finset.sum_add_distrib]
      rw [ih (j + 1), ih j]
      have e2 : r + (j + 1) + 1 = (r + j + 1) + 1 := by omega
      rw [e2, Nat.choose_succ_succ (N + 1) (r + j + 1)]
      ring

private theorem seh_choose_weight (N r : ℕ) :
    (r : ℝ) * (N.choose r : ℝ) + (r + 1 : ℕ) * (N.choose (r + 1) : ℝ) =
      (N : ℝ) * (N.choose r : ℝ) := by
  by_cases hr : r ≤ N
  · have h := Nat.choose_succ_right_eq N r
    have hR : (N.choose (r + 1) : ℝ) * (r + 1 : ℕ) =
        (N.choose r : ℝ) * (N - r : ℕ) := by
      exact_mod_cast h
    push_cast [Nat.cast_sub hr] at hR ⊢
    linear_combination hR
  · have h0 : N.choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h1 : N.choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0, h1]

private theorem seh_choose_weight_two (m k : ℕ) :
    (k : ℝ) * (m.choose k : ℝ) +
        2 * (k + 1 : ℕ) * (m.choose (k + 1) : ℝ) +
        (k + 2 : ℕ) * (m.choose (k + 2) : ℝ) =
      (m : ℝ) * ((m + 1).choose (k + 1) : ℝ) := by
  have h0 := seh_choose_weight m k
  have h1 := seh_choose_weight m (k + 1)
  rw [Nat.choose_succ_succ]
  norm_num [Nat.cast_add] at h0 h1 ⊢
  linear_combination h0 + h1

private theorem seh_euC_succ_zero (n k : ℕ) :
    (euC (n + 1) k 0 : ℝ) =
      (k + 1 : ℕ) * (euC n k 0 : ℝ) +
        (k + 2 : ℕ) * (euC n (k + 1) 0 : ℝ) := by
  have hc := seh_choose_weight 1 (k + 1)
  unfold euC
  rw [Nat.stirlingSecond_succ_succ]
  simp only [Nat.factorial_zero, one_mul, Nat.stirlingSecond_succ_zero, add_zero]
  norm_num [Nat.cast_add] at hc ⊢
  linear_combination -(Nat.stirlingSecond (n + 1) 1 : ℝ) * hc

private theorem seh_euC_pred (n k m : ℕ) :
    (k : ℝ) * (euC n (k - 1) m : ℝ) =
      (k : ℝ) * (Nat.factorial m : ℝ) * ((m + 1).choose k : ℝ) *
        (Nat.stirlingSecond (n + 1) (m + 1) : ℝ) := by
  cases k <;> norm_num [euC, Nat.cast_add, Nat.cast_mul]
  ring

private theorem seh_euC_succ_succ (n k m : ℕ) :
    (euC (n + 1) k (m + 1) : ℝ) =
      (k + 1 : ℕ) * (euC n k (m + 1) : ℝ) +
        (k + 2 : ℕ) * (euC n (k + 1) (m + 1) : ℝ) +
        (k : ℝ) * (euC n (k - 1) m : ℝ) +
        2 * (k + 1 : ℕ) * (euC n k m : ℝ) +
        (k + 2 : ℕ) * (euC n (k + 1) m : ℝ) := by
  have hs := seh_choose_weight (m + 2) (k + 1)
  have hp := seh_choose_weight_two (m + 1) k
  rw [seh_euC_pred]
  unfold euC
  rw [Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
  simp only [show m + 1 + 1 = m + 2 by omega,
    show k + 1 + 1 = k + 2 by omega] at hs hp ⊢
  norm_num [Nat.cast_add, Nat.cast_mul] at hs hp ⊢
  ring_nf at hs hp ⊢
  linear_combination
    -(((m : ℝ) + 1) * (Nat.factorial m : ℝ) *
      (Nat.stirlingSecond (1 + n) (2 + m) : ℝ)) * hs -
    ((Nat.factorial m : ℝ) * (Nat.stirlingSecond (1 + n) (1 + m) : ℝ)) * hp

private theorem seh_euC_above (n k : ℕ) : euC n k (n + 1) = 0 := by
  unfold euC
  have hs : Nat.stirlingSecond (n + 1) (n + 1 + 1) = 0 :=
    Nat.stirlingSecond_eq_zero_of_lt (by omega)
  rw [hs, mul_zero]

private theorem seh_sum_step (n : ℕ) (y : ℝ) (A B : ℕ → ℝ)
    (hA : A (n + 1) = 0) :
    A 0 * y ^ (n + 1) +
        ∑ m ∈ Finset.range (n + 1), (A (m + 1) + B m) * y ^ (n - m) =
      y * ∑ m ∈ Finset.range (n + 1), A m * y ^ (n - m) +
        ∑ m ∈ Finset.range (n + 1), B m * y ^ (n - m) := by
  have hshift : A 0 * y ^ (n + 1) +
        ∑ m ∈ Finset.range (n + 1), A (m + 1) * y ^ (n - m) =
      y * ∑ m ∈ Finset.range (n + 1), A m * y ^ (n - m) := by
    rw [Finset.sum_range_succ, hA, zero_mul, add_zero]
    rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
    have hsum :
        (∑ m ∈ Finset.range n, A (m + 1) * y ^ (n - m)) =
          ∑ m ∈ Finset.range n, y * (A (m + 1) * y ^ (n - (m + 1))) := by
      apply Finset.sum_congr rfl
      intro m hm
      have he : n - m = (n - (m + 1)) + 1 := by
        have := Finset.mem_range.mp hm
        omega
      rw [he, pow_succ]
      ring
    rw [hsum, pow_succ]
    simp only [Nat.sub_zero]
    ring
  have hsplit :
      (∑ m ∈ Finset.range (n + 1), (A (m + 1) + B m) * y ^ (n - m)) =
        (∑ m ∈ Finset.range (n + 1), A (m + 1) * y ^ (n - m)) +
          ∑ m ∈ Finset.range (n + 1), B m * y ^ (n - m) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hsplit, ← add_assoc, hshift]

private theorem seh_euS_succ (x : ℝ) (n k : ℕ) :
    euS x (n + 1) k =
      (k : ℝ) * euS x n (k - 1) +
        (k + 1 : ℕ) * (x + 1) * euS x n k +
        (k + 2 : ℕ) * x * euS x n (k + 1) := by
  let A : ℕ → ℝ := fun m =>
    (k + 1 : ℕ) * (euC n k m : ℝ) +
      (k + 2 : ℕ) * (euC n (k + 1) m : ℝ)
  let B : ℕ → ℝ := fun m =>
    (k : ℝ) * (euC n (k - 1) m : ℝ) +
      2 * (k + 1 : ℕ) * (euC n k m : ℝ) +
      (k + 2 : ℕ) * (euC n (k + 1) m : ℝ)
  have hA : A (n + 1) = 0 := by
    simp [A, seh_euC_above]
  have hsum := seh_sum_step n (x - 1) A B hA
  have hdecomp : euS x (n + 1) k =
      A 0 * (x - 1) ^ (n + 1) +
        ∑ m ∈ Finset.range (n + 1), (A (m + 1) + B m) * (x - 1) ^ (n - m) := by
    rw [euS, show n + 1 + 1 = n + 2 by omega, Finset.sum_range_succ']
    simp only [Nat.sub_zero]
    rw [seh_euC_succ_zero]
    change (∑ m ∈ Finset.range (n + 1),
        (euC (n + 1) k (m + 1) : ℝ) * (x - 1) ^ (n + 1 - (m + 1))) +
          A 0 * (x - 1) ^ (n + 1) = _
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [seh_euC_succ_succ]
    have he : n + 1 - (m + 1) = n - m := by
      have := Finset.mem_range.mp hm
      omega
    rw [he]
    dsimp only [A, B]
    ring
  have hAsum :
      (∑ m ∈ Finset.range (n + 1), A m * (x - 1) ^ (n - m)) =
        (k + 1 : ℕ) * euS x n k + (k + 2 : ℕ) * euS x n (k + 1) := by
    unfold A euS
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hBsum :
      (∑ m ∈ Finset.range (n + 1), B m * (x - 1) ^ (n - m)) =
        (k : ℝ) * euS x n (k - 1) +
          2 * (k + 1 : ℕ) * euS x n k +
          (k + 2 : ℕ) * euS x n (k + 1) := by
    unfold B euS
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hdecomp, hsum, hAsum, hBsum]
  ring

private theorem seh_euM_zero_zero (x : ℝ) : euM x 0 0 = 1 := by
  norm_num [euM, euS, euC, Nat.stirlingSecond_self]

private theorem seh_euM_zero_succ (x : ℝ) (j : ℕ) : euM x 0 (j + 1) = 0 := by
  have hc : Nat.choose 1 (j + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [euM, euS, euC, hc]

private theorem seh_euM_base (x : ℝ) (n : ℕ) :
    euM x (n + 1) 0 =
      euAlpha x 0 * euM x n 0 + euBeta x 1 * euM x n 1 := by
  rw [euM, seh_euS_succ]
  norm_num [euM, euAlpha, euBeta]

private theorem seh_euM_step (x : ℝ) (n j : ℕ) :
    euM x (n + 1) (j + 1) =
      euM x n j + euAlpha x (j + 1) * euM x n (j + 1) +
        euBeta x (j + 2) * euM x n (j + 2) := by
  rw [euM, seh_euS_succ]
  simp only [euM, euAlpha, euBeta]
  simp only [Nat.add_sub_cancel, Nat.factorial_succ]
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  field_simp [Nat.factorial_succ, hf]
  push_cast
  ring_nf

private theorem seh_hankel_transform_product (x : ℝ) (n : ℕ) :
    hankelTransform (fun m => euM x m 0) n =
      ∏ j ∈ Finset.range n, euBeta x (j + 1) ^ (n - j) := by
  simpa using
    hankelTransform_eq_prod_of_weightedMotzkin
      (alpha := euAlpha x) (beta := euBeta x) (M := euM x) (mu0 := (1 : ℝ))
      (seh_euM_zero_zero x) (seh_euM_zero_succ x)
      (seh_euM_base x) (seh_euM_step x) n

private theorem seh_alt_pow_eq_factorial_stirling (N K : ℕ) :
    (∑ j ∈ Finset.range (K + 1),
        (-1 : ℝ) ^ j * (K.choose j : ℝ) * (((K - j : ℕ) : ℝ) ^ N)) =
      (Nat.factorial K : ℝ) * (Nat.stirlingSecond N K : ℝ) := by
  rw [mul_comm, stirlingSecond_mul_factorial_eq_sum]
  rw [← Finset.sum_range_reflect
    (fun j => (-1 : ℝ) ^ (K - j) * (K.choose j : ℝ) * (j : ℝ) ^ N) (K + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ K := by
    simp only [Finset.mem_range] at hj
    omega
  rw [show K + 1 - 1 - j = K - j by omega,
    show K - (K - j) = j by omega, Nat.choose_symm hjle]

private theorem seh_triangle_swap (q : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ s ∈ Finset.range (q + 1), ∑ j ∈ Finset.range (q - s + 1), f s j) =
      ∑ i ∈ Finset.range (q + 1), ∑ s ∈ Finset.range (i + 1), f s (i - s) := by
  calc
    _ = ∑ p ∈ (Finset.range (q + 1)).sigma
          (fun s => Finset.range (q - s + 1)), f p.1 p.2 :=
      Finset.sum_sigma' _ _ _
    _ = ∑ p ∈ (Finset.range (q + 1)).sigma
          (fun i => Finset.range (i + 1)), f p.2 (p.1 - p.2) := by
      refine Finset.sum_bij'
        (fun p _ => ⟨p.1 + p.2, p.1⟩)
        (fun p _ => ⟨p.2, p.1 - p.2⟩) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨s, j⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
        have hs : s ≤ q := by omega
        have hsub := Nat.sub_add_cancel hs
        omega
      · rintro ⟨i, s⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
        have hi : i ≤ q := by omega
        have hsub := Nat.sub_le_sub_right hi s
        omega
      · rintro ⟨s, j⟩ hp
        apply Sigma.ext
        · rfl
        · simp
      · rintro ⟨i, s⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp
        have hs : s ≤ i := by omega
        apply Sigma.ext
        · exact Nat.add_sub_of_le hs
        · simp
      · rintro ⟨s, j⟩ hp
        simp
    _ = _ := (Finset.sum_sigma' (Finset.range (q + 1))
      (fun i => Finset.range (i + 1)) (fun i s => f s (i - s))).symm

private theorem seh_hockey_shift (q k i : ℕ) (hi : i ≤ q) :
    (∑ s ∈ Finset.range (i + 1),
        (k + s).choose k * (q - s).choose (i - s)) =
      (q + k + 1).choose i := by
  have h := hockey_conv (q + k) k (q - i)
  rw [show q + k + 1 = k + (q + 1) by omega, Finset.sum_range_add] at h
  have hzero :
      (∑ u ∈ Finset.range k, u.choose k * (q + k - u).choose (q - i)) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hu), zero_mul]
  rw [hzero, zero_add] at h
  have htail :
      (∑ s ∈ Finset.range (q + 1),
          (k + s).choose k * (q - s).choose (q - i)) =
        (q + k + 1).choose (k + (q - i) + 1) := by
    calc
      _ = ∑ s ∈ Finset.range (q + 1),
          (k + s).choose k * (q + k - (k + s)).choose (q - i) := by
            apply Finset.sum_congr rfl
            intro s hs
            congr 2
            omega
      _ = (k + (q + 1)).choose (k + (q - i) + 1) := h
      _ = _ := by
        rw [show k + (q + 1) = q + k + 1 by omega]
  have hsubset : Finset.range (i + 1) ⊆ Finset.range (q + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have htrunc :
      (∑ s ∈ Finset.range (i + 1),
          (k + s).choose k * (q - s).choose (q - i)) =
        ∑ s ∈ Finset.range (q + 1),
          (k + s).choose k * (q - s).choose (q - i) := by
    apply Finset.sum_subset hsubset
    intro s hs hsi
    have hsle : s ≤ q := by
      have := Finset.mem_range.mp hs
      omega
    have his0 : i + 1 ≤ s := by
      simpa only [Finset.mem_range, not_lt] using hsi
    have his : i < s := by omega
    have hchoose : (q - s).choose (q - i) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    rw [hchoose, mul_zero]
  calc
    (∑ s ∈ Finset.range (i + 1),
        (k + s).choose k * (q - s).choose (i - s)) =
        ∑ s ∈ Finset.range (i + 1),
          (k + s).choose k * (q - s).choose (q - i) := by
            apply Finset.sum_congr rfl
            intro s hs
            have hsi : s ≤ i := by
              have := Finset.mem_range.mp hs
              omega
            have hsymm := Nat.choose_symm (show i - s ≤ q - s by omega)
            have he : q - s - (i - s) = q - i := by omega
            rw [he] at hsymm
            rw [hsymm]
    _ = (q + k + 1).choose (k + (q - i) + 1) := htrunc.trans htail
    _ = (q + k + 1).choose i := by
      have hsymm := Nat.choose_symm (show i ≤ q + k + 1 by omega)
      have he : q + k + 1 - i = k + (q - i) + 1 := by omega
      rwa [he] at hsymm

private theorem seh_double_sum_collapse (q k N : ℕ) :
    (∑ s ∈ Finset.range (q + 1), ∑ j ∈ Finset.range (q - s + 1),
        (-1 : ℝ) ^ j * ((q - s).choose j : ℝ) *
          (((q - s - j : ℕ) : ℝ) ^ N) * ((k + s).choose k : ℝ) *
          (-1 : ℝ) ^ s) =
      ∑ i ∈ Finset.range (q + 1),
        (-1 : ℝ) ^ i * ((q + k + 1).choose i : ℝ) *
          (((q - i : ℕ) : ℝ) ^ N) := by
  rw [seh_triangle_swap]
  apply Finset.sum_congr rfl
  intro i hi
  have hiq : i ≤ q := by
    have := Finset.mem_range.mp hi
    omega
  calc
    (∑ s ∈ Finset.range (i + 1),
        (-1 : ℝ) ^ (i - s) * ((q - s).choose (i - s) : ℝ) *
          (((q - s - (i - s) : ℕ) : ℝ) ^ N) * ((k + s).choose k : ℝ) *
          (-1 : ℝ) ^ s) =
        (-1 : ℝ) ^ i * (((q - i : ℕ) : ℝ) ^ N) *
          ∑ s ∈ Finset.range (i + 1),
            ((k + s).choose k : ℝ) * ((q - s).choose (i - s) : ℝ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s hs
              have hsi : s ≤ i := by
                have := Finset.mem_range.mp hs
                omega
              have hsign : (-1 : ℝ) ^ (i - s) * (-1 : ℝ) ^ s = (-1 : ℝ) ^ i := by
                rw [← pow_add]
                congr 1
                omega
              have hsub : q - s - (i - s) = q - i := by omega
              rw [hsub]
              calc
                _ = ((-1 : ℝ) ^ (i - s) * (-1 : ℝ) ^ s) *
                    ((q - s).choose (i - s) : ℝ) * (((q - i : ℕ) : ℝ) ^ N) *
                    ((k + s).choose k : ℝ) := by ring
                _ = _ := by rw [hsign]; ring
    _ = (-1 : ℝ) ^ i * ((q + k + 1).choose i : ℝ) *
        (((q - i : ℕ) : ℝ) ^ N) := by
          rw [show (∑ s ∈ Finset.range (i + 1),
              ((k + s).choose k : ℝ) * ((q - s).choose (i - s) : ℝ)) =
              ((q + k + 1).choose i : ℝ) by
            exact_mod_cast seh_hockey_shift q k i hiq]
          ring

private theorem seh_stirling_coeff_core (q k : ℕ) :
    (∑ r ∈ Finset.range (q + 1),
        (Nat.factorial r : ℝ) * (Nat.stirlingSecond (q + k) r : ℝ) *
          ((q + k - r).choose k : ℝ) * (-1 : ℝ) ^ (q + k - r - k)) =
      ∑ i ∈ Finset.range (q + 1),
        (-1 : ℝ) ^ i * ((q + k + 1).choose i : ℝ) *
          (((q - i : ℕ) : ℝ) ^ (q + k)) := by
  calc
    _ = ∑ r ∈ Finset.range (q + 1),
        (∑ j ∈ Finset.range (r + 1),
          (-1 : ℝ) ^ j * (r.choose j : ℝ) *
            (((r - j : ℕ) : ℝ) ^ (q + k))) *
          ((q + k - r).choose k : ℝ) * (-1 : ℝ) ^ (q + k - r - k) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [seh_alt_pow_eq_factorial_stirling]
    _ = ∑ s ∈ Finset.range (q + 1), ∑ j ∈ Finset.range (q - s + 1),
        (-1 : ℝ) ^ j * ((q - s).choose j : ℝ) *
          (((q - s - j : ℕ) : ℝ) ^ (q + k)) * ((k + s).choose k : ℝ) *
          (-1 : ℝ) ^ s := by
            rw [← Finset.sum_range_reflect (fun r =>
              (∑ j ∈ Finset.range (r + 1),
                (-1 : ℝ) ^ j * (r.choose j : ℝ) *
                  (((r - j : ℕ) : ℝ) ^ (q + k))) *
                ((q + k - r).choose k : ℝ) *
                (-1 : ℝ) ^ (q + k - r - k)) (q + 1)]
            apply Finset.sum_congr rfl
            intro s hs
            have hsle : s ≤ q := by
              have := Finset.mem_range.mp hs
              omega
            have h0 : q + 1 - 1 - s = q - s := by omega
            have h1 : q + k - (q - s) = k + s := by omega
            have h2 : k + s - k = s := by omega
            rw [h0, h1, h2, Finset.sum_mul, Finset.sum_mul]
    _ = _ := seh_double_sum_collapse q k (q + k)

private theorem seh_stirling_coeff_eq_alt (N k : ℕ) (hk : k ≤ N) :
    (∑ r ∈ Finset.range (N + 1),
        (Nat.factorial r : ℝ) * (Nat.stirlingSecond N r : ℝ) *
          ((N - r).choose k : ℝ) * (-1 : ℝ) ^ (N - r - k)) =
      ∑ i ∈ Finset.range (N - k + 1),
        (-1 : ℝ) ^ i * ((N + 1).choose i : ℝ) *
          (((N - k - i : ℕ) : ℝ) ^ N) := by
  have hsubset : Finset.range (N - k + 1) ⊆ Finset.range (N + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have htrunc :
      (∑ r ∈ Finset.range (N - k + 1),
          (Nat.factorial r : ℝ) * (Nat.stirlingSecond N r : ℝ) *
            ((N - r).choose k : ℝ) * (-1 : ℝ) ^ (N - r - k)) =
        ∑ r ∈ Finset.range (N + 1),
          (Nat.factorial r : ℝ) * (Nat.stirlingSecond N r : ℝ) *
            ((N - r).choose k : ℝ) * (-1 : ℝ) ^ (N - r - k) := by
    apply Finset.sum_subset hsubset
    intro r hr hsmall
    have hrle : r ≤ N := by
      have := Finset.mem_range.mp hr
      omega
    have hrgt : N - k < r := by
      have : N - k + 1 ≤ r := by
        simpa only [Finset.mem_range, not_lt] using hsmall
      omega
    have hchoose : (N - r).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hchoose, Nat.cast_zero, mul_zero, zero_mul]
  rw [← htrunc]
  simpa only [Nat.sub_add_cancel hk] using seh_stirling_coeff_core (N - k) k

private theorem seh_binomial_basis_expand (N : ℕ) (x : ℝ) (a : ℕ → ℝ) :
    (∑ r ∈ Finset.range (N + 1), a r * (x - 1) ^ (N - r)) =
      ∑ k ∈ Finset.range (N + 1),
        (∑ r ∈ Finset.range (N + 1),
          a r * ((N - r).choose k : ℝ) * (-1 : ℝ) ^ (N - r - k)) * x ^ k := by
  calc
    _ = ∑ r ∈ Finset.range (N + 1), a r * (x + (-1 : ℝ)) ^ (N - r) := by
      rfl
    _ = ∑ r ∈ Finset.range (N + 1), a r *
        ∑ k ∈ Finset.range (N - r + 1),
          x ^ k * (-1 : ℝ) ^ (N - r - k) * ((N - r).choose k : ℝ) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [add_pow]
    _ = ∑ r ∈ Finset.range (N + 1), a r *
        ∑ k ∈ Finset.range (N + 1),
          x ^ k * (-1 : ℝ) ^ (N - r - k) * ((N - r).choose k : ℝ) := by
            apply Finset.sum_congr rfl
            intro r hr
            congr 1
            have hle : N - r + 1 ≤ N + 1 :=
              Nat.add_le_add_right (Nat.sub_le N r) 1
            apply Finset.sum_subset (Finset.range_subset_range.mpr hle)
            intro k hk hsmall
            have hkgt : N - r < k := by
              have : N - r + 1 ≤ k := by
                simpa only [Finset.mem_range, not_lt] using hsmall
              omega
            rw [Nat.choose_eq_zero_of_lt hkgt, Nat.cast_zero, mul_zero]
    _ = ∑ r ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        a r * (x ^ k * (-1 : ℝ) ^ (N - r - k) * ((N - r).choose k : ℝ)) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N + 1),
        a r * (x ^ k * (-1 : ℝ) ^ (N - r - k) * ((N - r).choose k : ℝ)) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      ring

private theorem seh_euS_zero_as_stirling (n : ℕ) (x : ℝ) :
    euS x n 0 =
      ∑ r ∈ Finset.range (n + 2),
        (Nat.factorial r : ℝ) * (Nat.stirlingSecond (n + 1) r : ℝ) *
          (x - 1) ^ (n + 1 - r) := by
  rw [euS]
  conv_rhs =>
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero,
    zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  have hmle : m ≤ n := by
    have := Finset.mem_range.mp hm
    omega
  have hexp : n + 1 - (m + 1) = n - m := by omega
  rw [hexp]
  unfold euC
  rw [Nat.choose_one_right, Nat.factorial_succ]
  push_cast
  ring

private theorem seh_euM_zero_eq_P (x : ℝ) (n : ℕ) (W : ℕ → ℕ → ℝ)
    (P : ℕ → ℝ → ℝ)
    (hW : ∀ (m k : ℕ),
      W m k =
        ∑ i ∈ Finset.range (m - k + 1),
          (-1 : ℝ) ^ i * ((((m + 1).choose i : ℕ) : ℝ)) *
            (((((m - k - i : ℕ) : ℝ))) ^ m))
    (hP : ∀ (m : ℕ) (X : ℝ),
      P m X = ∑ k ∈ Finset.range (m + 1), W m k * X ^ k) :
    euM x n 0 = P (n + 1) x := by
  calc
    euM x n 0 = euS x n 0 := by norm_num [euM]
    _ = ∑ r ∈ Finset.range (n + 2),
        (Nat.factorial r : ℝ) * (Nat.stirlingSecond (n + 1) r : ℝ) *
          (x - 1) ^ (n + 1 - r) := seh_euS_zero_as_stirling n x
    _ = ∑ k ∈ Finset.range (n + 2),
        (∑ r ∈ Finset.range (n + 2),
          (Nat.factorial r : ℝ) * (Nat.stirlingSecond (n + 1) r : ℝ) *
            (((n + 1 - r).choose k : ℕ) : ℝ) *
            (-1 : ℝ) ^ (n + 1 - r - k)) * x ^ k := by
              simpa only [show n + 1 + 1 = n + 2 by omega] using
                seh_binomial_basis_expand (n + 1) x
                  (fun r => (Nat.factorial r : ℝ) *
                    (Nat.stirlingSecond (n + 1) r : ℝ))
    _ = ∑ k ∈ Finset.range (n + 2), W (n + 1) k * x ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkle : k ≤ n + 1 := by
        have := Finset.mem_range.mp hk
        omega
      rw [seh_stirling_coeff_eq_alt (n + 1) k hkle, hW]
    _ = P (n + 1) x := by
      rw [hP]

private theorem seh_hankel_product (n : ℕ) (x : ℝ) (W : ℕ → ℕ → ℝ)
    (P : ℕ → ℝ → ℝ)
    (hW : ∀ (m k : ℕ),
      W m k =
        ∑ i ∈ Finset.range (m - k + 1),
          (-1 : ℝ) ^ i * ((((m + 1).choose i : ℕ) : ℝ)) *
            (((((m - k - i : ℕ) : ℝ))) ^ m))
    (hP : ∀ (m : ℕ) (X : ℝ),
      P m X = ∑ k ∈ Finset.range (m + 1), W m k * X ^ k) :
    Matrix.det (Matrix.of fun (i j : Fin (n + 1)) => P (i.val + j.val + 1) x) =
      ∏ j ∈ Finset.range n, euBeta x (j + 1) ^ (n - j) := by
  calc
    Matrix.det (Matrix.of fun (i j : Fin (n + 1)) => P (i.val + j.val + 1) x) =
        hankelTransform (fun m => euM x m 0) n := by
          unfold hankelTransform
          congr 1
          funext i j
          simp only [Matrix.of_apply]
          exact (seh_euM_zero_eq_P x (i.val + j.val) W P hW hP).symm
    _ = ∏ j ∈ Finset.range n, euBeta x (j + 1) ^ (n - j) :=
      seh_hankel_transform_product x n

private theorem seh_beta_factor (x : ℝ) (j : ℕ) :
    euBeta x (j + 1) = (2 * x) * (((j + 2).choose 2 : ℕ) : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (j + 1) 1
  simp only [Nat.choose_one_right] at h
  have hR : ((j + 2 : ℕ) : ℝ) * (j + 1 : ℕ) =
      (((j + 2).choose 2 : ℕ) : ℝ) * 2 := by
    exact_mod_cast h
  unfold euBeta
  norm_num [Nat.cast_add] at hR ⊢
  linear_combination x * hR

private theorem seh_sum_sub_range (n : ℕ) :
    (∑ j ∈ Finset.range n, (n - j)) = (n + 1).choose 2 := by
  calc
    (∑ j ∈ Finset.range n, (n - j)) =
        ∑ j ∈ Finset.range n, (j + 1) := by
          rw [← Finset.sum_range_reflect (fun j => n - j) n]
          apply Finset.sum_congr rfl
          intro j hj
          have := Finset.mem_range.mp hj
          omega
    _ = ∑ j ∈ Finset.range (n + 1), j := by
      rw [Finset.sum_add_distrib, Finset.sum_range_succ]
      simp
    _ = (n + 1).choose 2 := by
      rw [Finset.sum_range_id, Nat.choose_two_right]

private theorem seh_choose_product_shift : ∀ n : ℕ,
    (∏ j ∈ Finset.range n, ((((j + 2).choose 2 : ℕ) : ℝ)) ^ (n - j)) =
      ∏ k ∈ Finset.range n,
        ((((k + 3).choose 2 : ℕ) : ℝ)) ^ (n - (k + 1))
  | 0 => by simp
  | n + 1 => by
      rw [Finset.prod_range_succ', Finset.prod_range_succ]
      norm_num

private theorem seh_beta_product (n : ℕ) (x : ℝ) :
    (∏ j ∈ Finset.range n, euBeta x (j + 1) ^ (n - j)) =
      (2 * x) ^ ((n + 1).choose 2) *
        ∏ k ∈ Finset.range n,
          (((((k + 3).choose 2 : ℕ) : ℝ)) ^ (n - (k + 1))) := by
  simp_rw [seh_beta_factor, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, seh_sum_sub_range,
    seh_choose_product_shift]

/--
**Hankel determinants of the shifted Eulerian polynomials.** Let $n \in \mathbb{N}$ and
$x \in \mathbb{R}$. For natural numbers $k \le m$ let
$W_{m,k} = \sum_{i=0}^{m-k} (-1)^i \binom{m+1}{i} (m-k-i)^m$, with $0^0 = 1$, and let
$P_m(X) = \sum_{k=0}^{m} W_{m,k} X^k$ be the corresponding Eulerian polynomial. Then the
$(n+1) \times (n+1)$ Hankel determinant of the shifted sequence $P_1(x), P_2(x), \dots$ is
$$\det\bigl(P_{i+j+1}(x)\bigr)_{0 \le i, j \le n} =
(2x)^{\binom{n+1}{2}} \prod_{k=0}^{n-1} \binom{k+3}{2}^{n-k-1}.$$

Proves `Wanted` entry `hankel_transform_shifted_eulerian_polynomials`.
Proof: The closed Eulerian coefficients identify a weighted-Motzkin Stieltjes table with
Jacobi weights `euAlpha` and `euBeta`; its determinant follows by the Heilermann-Flajolet LDU
route used by Barry and discussed by Krattenthaler.

Source: Paul Barry, "Eulerian Polynomials as Moments, via Exponential Riordan Arrays,"
Journal of Integer Sequences 14 (2011), Article 11.9.5, corollary lines 312–315,
<https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry7/barry172.tex>.
Eulerian closed form `W_{n,k}` at lines 93–94.
-/
public theorem hankel_transform_shifted_eulerian_polynomials :
  ∀ (n : ℕ) (x : ℝ) (W : ℕ → ℕ → ℝ) (P : ℕ → ℝ → ℝ),
    (∀ (m k : ℕ),
      W m k =
        ∑ i ∈ Finset.range (m - k + 1),
          (-1 : ℝ) ^ i * ((((m + 1).choose i : ℕ) : ℝ)) *
            (((((m - k - i : ℕ) : ℝ))) ^ m)) →
    (∀ (m : ℕ) (X : ℝ),
      P m X = ∑ k ∈ Finset.range (m + 1), W m k * X ^ k) →
    Matrix.det (Matrix.of fun (i j : Fin (n + 1)) => P (i.val + j.val + 1) x) =
      (2 * x) ^ ((n + 1).choose 2) *
        ∏ k ∈ Finset.range n,
          (((((k + 3).choose 2 : ℕ) : ℝ)) ^ (n - (k + 1))) := by
  intro n x W P hW hP
  calc
    Matrix.det (Matrix.of fun (i j : Fin (n + 1)) => P (i.val + j.val + 1) x) =
        ∏ j ∈ Finset.range n, euBeta x (j + 1) ^ (n - j) :=
      seh_hankel_product n x W P hW hP
    _ = _ := seh_beta_product n x

end MetaMathlibExt
end
