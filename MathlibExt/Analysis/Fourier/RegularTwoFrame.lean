/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Measurability.Init
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Regular real frame from half-circle directions

For `j∈Fin n`, the two real frame entries are `F_n(0,j)=cos(πj/n)/√n` and
`F_n(1,j)=sin(πj/n)/√n`. For `n≥2`, the row Gram matrix is `(1/2)I₂`. For `n>0`, each column has
squared Euclidean norm `1/n`.

The case `n=0` is the empty-column frame. These are the half-circle equal-norm tight-frame
formulas in arXiv 2608.08836, equations (21)–(23).
-/

@[expose] public section

namespace Real

open Finset

/-- **Real two-row frame of equally spaced half-circle directions.** For `n∈ℕ`,
`regularTwoFrame n` has entries `cos(πj/n)/√n` in row zero and `sin(πj/n)/√n` in row one,
for `j∈Fin n`. The empty-column case `n=0` is included. -/
public noncomputable def regularTwoFrame (n : ℕ) : Fin 2 → Fin n → ℝ :=
  fun r j =>
    if r.val = 0 then
      Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) / Real.sqrt (n : ℝ)
    else
      Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) / Real.sqrt (n : ℝ)

private lemma map_valEmbedding_univ_eq_range (n : ℕ) :
    Finset.map Fin.valEmbedding (Finset.univ : Finset (Fin n)) = Finset.range n := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_map] at hx
    obtain ⟨j, _, rfl⟩ := hx
    rw [Finset.mem_range]
    exact j.is_lt
  · intro hx
    rw [Finset.mem_range] at hx
    rw [Finset.mem_map]
    exact ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩

private lemma sum_fin_val_eq_sum_range (n : ℕ) (f : ℕ → ℝ) :
    ∑ j : Fin n, f j.val = ∑ i ∈ Finset.range n, f i := by
  calc
    ∑ j : Fin n, f j.val
        = ∑ j ∈ Finset.univ, f (Fin.val j) := rfl
    _ = ∑ j ∈ Finset.univ, f (Fin.valEmbedding j) := rfl
    _ = ∑ x ∈ Finset.map Fin.valEmbedding Finset.univ, f x := by
        rw [Finset.sum_map]
    _ = ∑ x ∈ Finset.range n, f x := by
        rw [map_valEmbedding_univ_eq_range]

private lemma pi_div_n_pos'_aux {n : ℕ} (hn : 0 < n) :
    0 < Real.pi / (n : ℝ) :=
  div_pos Real.pi_pos (Nat.cast_pos.mpr hn)

private lemma pi_div_n_lt_pi_aux {n : ℕ} (hn : 2 ≤ n) :
    Real.pi / (n : ℝ) < Real.pi := by
  have h1 : (1 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact div_lt_self Real.pi_pos h1

private lemma sin_pi_div_n_pos_aux {n : ℕ} (hn : 2 ≤ n) :
    0 < Real.sin (Real.pi / (n : ℝ)) := by
  have hn0 : 0 < n := by omega
  exact Real.sin_pos_of_pos_of_lt_pi
    (pi_div_n_pos'_aux hn0) (pi_div_n_lt_pi_aux hn)

private lemma sin_pi_div_n_ne_zero_aux {n : ℕ} (hn : 2 ≤ n) :
    Real.sin (Real.pi / (n : ℝ)) ≠ 0 :=
  ne_of_gt (sin_pi_div_n_pos_aux hn)

private lemma sum_range_cos_two_pi_div_n_eq_zero_aux {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * (i : ℝ) / (n : ℝ)) = 0 := by
  set a : ℝ := 2 * Real.pi / (n : ℝ) with ha_def
  have ha_half : a / 2 = Real.pi / (n : ℝ) := by
    rw [ha_def]
    have : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      exact_mod_cast (Nat.ne_zero_of_lt this)
    field_simp
  have h_sin_half_ne : Real.sin (a / 2) ≠ 0 := by
    rw [ha_half]
    exact sin_pi_div_n_ne_zero_aux hn
  have h_n_mul_a_half : (n : ℝ) * a / 2 = Real.pi := by
    rw [ha_def]
    have : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      exact_mod_cast (Nat.ne_zero_of_lt this)
    field_simp
  have h_sin_n_half : Real.sin ((n : ℝ) * a / 2) = 0 := by
    rw [h_n_mul_a_half, Real.sin_pi]
  have h_mul : Real.sin (a / 2) *
      ∑ i ∈ Finset.range n, Real.cos (a * (i : ℝ)) =
      Real.sin ((n : ℝ) * a / 2) *
        Real.cos (((n : ℝ) - 1) * a / 2) := by
    simpa using Real.sin_mul_sum_cos n a 0
  have h_cos_arg : ∀ i : ℕ,
      Real.cos (a * (i : ℝ)) = Real.cos (2 * Real.pi * (i : ℝ) / (n : ℝ)) := by
    intro i
    congr 1
    rw [ha_def]
    ring
  have h_sum_eq : ∑ i ∈ Finset.range n, Real.cos (a * (i : ℝ)) =
      ∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * (i : ℝ) / (n : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact h_cos_arg i
  rw [h_sum_eq] at h_mul
  rw [h_sin_n_half, zero_mul] at h_mul
  exact (mul_eq_zero.mp h_mul).resolve_left h_sin_half_ne

private lemma sum_range_sin_two_pi_div_n_eq_zero_aux {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * (i : ℝ) / (n : ℝ)) = 0 := by
  set a : ℝ := 2 * Real.pi / (n : ℝ) with ha_def
  have ha_half : a / 2 = Real.pi / (n : ℝ) := by
    rw [ha_def]
    have : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      exact_mod_cast (Nat.ne_zero_of_lt this)
    field_simp
  have h_sin_half_ne : Real.sin (a / 2) ≠ 0 := by
    rw [ha_half]
    exact sin_pi_div_n_ne_zero_aux hn
  have h_n_mul_a_half : (n : ℝ) * a / 2 = Real.pi := by
    rw [ha_def]
    have : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      exact_mod_cast (Nat.ne_zero_of_lt this)
    field_simp
  have h_sin_n_half : Real.sin ((n : ℝ) * a / 2) = 0 := by
    rw [h_n_mul_a_half, Real.sin_pi]
  have h_mul : Real.sin (a / 2) *
      ∑ i ∈ Finset.range n, Real.sin (a * (i : ℝ)) =
      Real.sin ((n : ℝ) * a / 2) *
        Real.sin (((n : ℝ) - 1) * a / 2) := by
    simpa using Real.sin_mul_sum_sin n a 0
  have h_sin_arg : ∀ i : ℕ,
      Real.sin (a * (i : ℝ)) = Real.sin (2 * Real.pi * (i : ℝ) / (n : ℝ)) := by
    intro i
    congr 1
    rw [ha_def]
    ring
  have h_sum_eq : ∑ i ∈ Finset.range n, Real.sin (a * (i : ℝ)) =
      ∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * (i : ℝ) / (n : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact h_sin_arg i
  rw [h_sum_eq] at h_mul
  rw [h_sin_n_half, zero_mul] at h_mul
  exact (mul_eq_zero.mp h_mul).resolve_left h_sin_half_ne

private lemma sum_fin_cos_two_pi_div_n_eq_zero_aux {n : ℕ} (hn : 2 ≤ n) :
    ∑ j : Fin n, Real.cos (2 * Real.pi * (j.val : ℝ) / (n : ℝ)) = 0 := by
  have h := sum_fin_val_eq_sum_range n
      (fun i => Real.cos (2 * Real.pi * (i : ℝ) / (n : ℝ)))
  rw [h]
  exact sum_range_cos_two_pi_div_n_eq_zero_aux hn

private lemma sum_fin_sin_two_pi_div_n_eq_zero_aux {n : ℕ} (hn : 2 ≤ n) :
    ∑ j : Fin n, Real.sin (2 * Real.pi * (j.val : ℝ) / (n : ℝ)) = 0 := by
  have h := sum_fin_val_eq_sum_range n
      (fun i => Real.sin (2 * Real.pi * (i : ℝ) / (n : ℝ)))
  rw [h]
  exact sum_range_sin_two_pi_div_n_eq_zero_aux hn

private lemma cos_sq_eq'' (x : ℝ) :
    Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := by
  have h := Real.two_mul_cos_mul_cos x x
  have h0 : Real.cos (x - x) = 1 := by rw [sub_self, Real.cos_zero]
  have h2 : x + x = 2 * x := by ring
  rw [h0, h2] at h
  have : Real.cos x ^ 2 = Real.cos x * Real.cos x := by ring
  linarith

private lemma sin_sq_eq'' (x : ℝ) :
    Real.sin x ^ 2 = (1 - Real.cos (2 * x)) / 2 := by
  have h := Real.two_mul_sin_mul_sin x x
  have h0 : Real.cos (x - x) = 1 := by rw [sub_self, Real.cos_zero]
  have h2 : x + x = 2 * x := by ring
  rw [h0, h2] at h
  have : Real.sin x ^ 2 = Real.sin x * Real.sin x := by ring
  linarith

private lemma cos_mul_sin_eq'' (x : ℝ) :
    Real.cos x * Real.sin x = Real.sin (2 * x) / 2 := by
  have h := Real.two_mul_sin_mul_cos x x
  have h0 : Real.sin (x - x) = 0 := by rw [sub_self, Real.sin_zero]
  have h2 : x + x = 2 * x := by ring
  rw [h0, h2] at h
  linarith

private lemma sqrt_nat_mul_self_eq (n : ℕ) :
    Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
  Real.mul_self_sqrt (Nat.cast_nonneg n)

private lemma sqrt_nat_sq_eq (n : ℕ) :
    Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := by
  rw [sq, sqrt_nat_mul_self_eq]

private lemma reg_frame_mul_eq_div_n_aux (n : ℕ)
    (r s : Fin 2) (j : Fin n) :
    regularTwoFrame n r j * regularTwoFrame n s j =
      (if r.val = 0 then
        if s.val = 0 then Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) *
          Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ))
        else Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) *
          Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ))
      else
        if s.val = 0 then Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) *
          Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ))
        else Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) *
          Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ))) / (n : ℝ) := by
  have h_mul := sqrt_nat_mul_self_eq n
  unfold regularTwoFrame
  by_cases hr : r.val = 0 <;> by_cases hs : s.val = 0
  · simp only [hr, hs, ite_true]
    rw [div_mul_div_comm, h_mul]
  · simp only [hr, hs, ite_true, ite_false]
    rw [div_mul_div_comm, h_mul]
  · simp only [hr, hs, ite_false, ite_true]
    rw [div_mul_div_comm, h_mul]
  · simp only [hr, hs, ite_false]
    rw [div_mul_div_comm, h_mul]

private lemma sum_cos_sq_eq_aux (n : ℕ) (hn : 2 ≤ n) :
    ∑ j : Fin n, Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 = (n : ℝ) / 2 := by
  have h0 : ∑ j : Fin n, Real.cos (2 * Real.pi * (j.val : ℝ) / (n : ℝ)) = 0 :=
    sum_fin_cos_two_pi_div_n_eq_zero_aux hn
  have h1 : ∀ j : Fin n,
      Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 =
        (1 + Real.cos (2 * Real.pi * (j.val : ℝ) / (n : ℝ))) / 2 := by
    intro j
    have h := cos_sq_eq'' (Real.pi * (j.val : ℝ) / (n : ℝ))
    have h2 : 2 * (Real.pi * (j.val : ℝ) / (n : ℝ)) =
        2 * Real.pi * (j.val : ℝ) / (n : ℝ) := by ring
    rw [h2] at h
    exact h
  calc
    ∑ j : Fin n, Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2
        = ∑ j : Fin n,
          (1 + Real.cos (2 * Real.pi * (j.val : ℝ) / (n : ℝ))) / 2 := by
          apply Finset.sum_congr rfl
          intro j _
          exact h1 j
    _ = (∑ j : Fin n,
          (1 + Real.cos (2 * Real.pi * (j.val : ℝ) / (n : ℝ)))) / 2 := by
          rw [Finset.sum_div]
    _ = ((∑ j : Fin n, (1 : ℝ)) +
          ∑ j : Fin n, Real.cos (2 * Real.pi * (j.val : ℝ) / (n : ℝ))) / 2 := by
          rw [Finset.sum_add_distrib]
    _ = ((n : ℝ) + 0) / 2 := by
          have h_one : ∑ _j : Fin n, (1 : ℝ) = (n : ℝ) := by
            calc
              ∑ _j : Fin n, (1 : ℝ)
                  = (Finset.univ : Finset (Fin n)).card • (1 : ℝ) := by
                    rw [Finset.sum_const]
              _ = (n : ℝ) := by
                    rw [Finset.card_univ, Fintype.card_fin,
                      nsmul_eq_mul, mul_one]
          rw [h_one, h0]
    _ = (n : ℝ) / 2 := by ring

private lemma sum_sin_sq_eq_aux (n : ℕ) (hn : 2 ≤ n) :
    ∑ j : Fin n, Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 = (n : ℝ) / 2 := by
  have h0 : ∑ j : Fin n, Real.cos (2 * Real.pi * (j.val : ℝ) / (n : ℝ)) = 0 :=
    sum_fin_cos_two_pi_div_n_eq_zero_aux hn
  have h1 : ∀ j : Fin n,
      Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 =
        (1 - Real.cos (2 * Real.pi * (j.val : ℝ) / (n : ℝ))) / 2 := by
    intro j
    have h := sin_sq_eq'' (Real.pi * (j.val : ℝ) / (n : ℝ))
    have h2 : 2 * (Real.pi * (j.val : ℝ) / (n : ℝ)) =
        2 * Real.pi * (j.val : ℝ) / (n : ℝ) := by ring
    rw [h2] at h
    exact h
  calc
    ∑ j : Fin n, Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2
        = ∑ j : Fin n,
          (1 - Real.cos (2 * Real.pi * (j.val : ℝ) / (n : ℝ))) / 2 := by
          apply Finset.sum_congr rfl
          intro j _
          exact h1 j
    _ = (∑ j : Fin n,
          (1 - Real.cos (2 * Real.pi * (j.val : ℝ) / (n : ℝ)))) / 2 := by
          rw [Finset.sum_div]
    _ = ((∑ j : Fin n, (1 : ℝ)) -
          ∑ j : Fin n, Real.cos (2 * Real.pi * (j.val : ℝ) / (n : ℝ))) / 2 := by
          rw [Finset.sum_sub_distrib]
    _ = ((n : ℝ) - 0) / 2 := by
          have h_one : ∑ _j : Fin n, (1 : ℝ) = (n : ℝ) := by
            calc
              ∑ _j : Fin n, (1 : ℝ)
                  = (Finset.univ : Finset (Fin n)).card • (1 : ℝ) := by
                    rw [Finset.sum_const]
              _ = (n : ℝ) := by
                    rw [Finset.card_univ, Fintype.card_fin,
                      nsmul_eq_mul, mul_one]
          rw [h_one, h0]
    _ = (n : ℝ) / 2 := by ring

private lemma sum_cos_mul_sin_eq_aux (n : ℕ) (hn : 2 ≤ n) :
    ∑ j : Fin n, Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) *
      Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) = 0 := by
  have h0 : ∑ j : Fin n, Real.sin (2 * Real.pi * (j.val : ℝ) / (n : ℝ)) = 0 :=
    sum_fin_sin_two_pi_div_n_eq_zero_aux hn
  have h1 : ∀ j : Fin n,
      Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) *
        Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) =
        Real.sin (2 * Real.pi * (j.val : ℝ) / (n : ℝ)) / 2 := by
    intro j
    have h := cos_mul_sin_eq'' (Real.pi * (j.val : ℝ) / (n : ℝ))
    have h2 : 2 * (Real.pi * (j.val : ℝ) / (n : ℝ)) =
        2 * Real.pi * (j.val : ℝ) / (n : ℝ) := by ring
    rw [h2] at h
    exact h
  calc
    ∑ j : Fin n, Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) *
        Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ))
        = ∑ j : Fin n, Real.sin (2 * Real.pi * (j.val : ℝ) / (n : ℝ)) / 2 := by
          apply Finset.sum_congr rfl
          intro j _
          exact h1 j
    _ = (∑ j : Fin n, Real.sin (2 * Real.pi * (j.val : ℝ) / (n : ℝ))) / 2 := by
          rw [Finset.sum_div]
    _ = 0 / 2 := by rw [h0]
    _ = 0 := by ring

private lemma sum_sin_mul_cos_eq_aux (n : ℕ) (hn : 2 ≤ n) :
    ∑ j : Fin n, Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) *
      Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) = 0 := by
  calc
    ∑ j : Fin n, Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) *
        Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ))
        = ∑ j : Fin n, Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) *
          Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = 0 := sum_cos_mul_sin_eq_aux n hn

private lemma reg_two_frame_zero_aux (n : ℕ) (j : Fin n) :
    regularTwoFrame n 0 j =
      Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) / Real.sqrt (n : ℝ) := by
  unfold regularTwoFrame
  simp

private lemma reg_two_frame_one_aux (n : ℕ) (j : Fin n) :
    regularTwoFrame n 1 j =
      Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) / Real.sqrt (n : ℝ) := by
  unfold regularTwoFrame
  have : (1 : Fin 2).val = 1 := rfl
  rw [this]
  simp

/-- **Half-identity Gram matrix of the regular real two-frame.** For `n≥2` and rows `r,s∈Fin
2`, `Σ_j< n F_n(r,j)F_n(s,j)=1/2` when `r=s` and zero otherwise, where
`F_n=regularTwoFrame n`. -/
public theorem regularTwoFrame_gram (n : ℕ) (hn : 2 ≤ n) (r s : Fin 2) :
    (∑ j : Fin n, regularTwoFrame n r j * regularTwoFrame n s j) =
      if r = s then 1 / 2 else 0 := by
  have hn0 : 0 < n := by omega
  by_cases hrs : r = s
  · subst hrs
    simp only [ite_true]
    fin_cases r
    · have h_mul : ∀ j : Fin n,
          regularTwoFrame n 0 j * regularTwoFrame n 0 j =
            Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 / (n : ℝ) := by
        intro j
        have h := reg_frame_mul_eq_div_n_aux n 0 0 j
        simp only [Fin.val_zero] at h
        have h_cos : Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) *
            Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) =
            Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 := by ring
        rw [h_cos] at h
        exact h
      calc
        ∑ j : Fin n, regularTwoFrame n 0 j * regularTwoFrame n 0 j
            = ∑ j : Fin n,
              Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 / (n : ℝ) := by
              apply Finset.sum_congr rfl
              intro j _
              exact h_mul j
        _ = (∑ j : Fin n, Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2) /
            (n : ℝ) := by
              rw [Finset.sum_div]
        _ = ((n : ℝ) / 2) / (n : ℝ) := by rw [sum_cos_sq_eq_aux n hn]
        _ = 1 / 2 := by field_simp
    · have h_mul : ∀ j : Fin n,
          regularTwoFrame n 1 j * regularTwoFrame n 1 j =
            Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 / (n : ℝ) := by
        intro j
        have h := reg_frame_mul_eq_div_n_aux n 1 1 j
        simp only [Fin.val_one] at h
        have h_sin : Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) *
            Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) =
            Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 := by ring
        rw [h_sin] at h
        exact h
      calc
        ∑ j : Fin n, regularTwoFrame n 1 j * regularTwoFrame n 1 j
            = ∑ j : Fin n,
              Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 / (n : ℝ) := by
              apply Finset.sum_congr rfl
              intro j _
              exact h_mul j
        _ = (∑ j : Fin n, Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2) /
            (n : ℝ) := by
              rw [Finset.sum_div]
        _ = ((n : ℝ) / 2) / (n : ℝ) := by rw [sum_sin_sq_eq_aux n hn]
        _ = 1 / 2 := by field_simp
  · rw [ite_eq_right hrs]
    fin_cases r <;> fin_cases s
    · exact absurd rfl hrs
    · have h_mul : ∀ j : Fin n,
          regularTwoFrame n 0 j * regularTwoFrame n 1 j =
            Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) *
              Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) / (n : ℝ) := by
        intro j
        have h := reg_frame_mul_eq_div_n_aux n 0 1 j
        simp only [Fin.val_zero, Fin.val_one] at h
        exact h
      calc
        ∑ j : Fin n, regularTwoFrame n 0 j * regularTwoFrame n 1 j
            = ∑ j : Fin n, Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) *
              Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) / (n : ℝ) := by
                apply Finset.sum_congr rfl
                intro j _
                exact h_mul j
        _ = (∑ j : Fin n, Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) *
              Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ))) / (n : ℝ) := by
                rw [Finset.sum_div]
        _ = 0 / (n : ℝ) := by rw [sum_cos_mul_sin_eq_aux n hn]
        _ = 0 := by simp
    · have h_mul : ∀ j : Fin n,
          regularTwoFrame n 1 j * regularTwoFrame n 0 j =
            Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) *
              Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) / (n : ℝ) := by
        intro j
        have h := reg_frame_mul_eq_div_n_aux n 1 0 j
        simp only [Fin.val_zero, Fin.val_one] at h
        exact h
      calc
        ∑ j : Fin n, regularTwoFrame n 1 j * regularTwoFrame n 0 j
            = ∑ j : Fin n, Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) *
              Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) / (n : ℝ) := by
                apply Finset.sum_congr rfl
                intro j _
                exact h_mul j
        _ = (∑ j : Fin n, Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) *
              Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ))) / (n : ℝ) := by
                rw [Finset.sum_div]
        _ = 0 / (n : ℝ) := by rw [sum_sin_mul_cos_eq_aux n hn]
        _ = 0 := by simp
    · exact absurd rfl hrs

/-- **Reciprocal column squared norm of the regular real two-frame.** For `n>0`, each column
`j∈Fin n` satisfies `Σ_r∈Fin 2 (regularTwoFrame n r j)²=1/n`. -/
public theorem regularTwoFrame_row_norm (n : ℕ) (hn : 0 < n) (j : Fin n) :
    (∑ r : Fin 2, (regularTwoFrame n r j) ^ 2) = 1 / (n : ℝ) := by
  have _hn0 : 0 < n := hn
  rw [Fin.sum_univ_two]
  rw [reg_two_frame_zero_aux, reg_two_frame_one_aux]
  have h_cos_div : (Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) /
      Real.sqrt (n : ℝ)) ^ 2 =
      Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 /
        (Real.sqrt (n : ℝ) ^ 2) := by
    rw [div_pow]
  have h_sin_div : (Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) /
      Real.sqrt (n : ℝ)) ^ 2 =
      Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 /
        (Real.sqrt (n : ℝ) ^ 2) := by
    rw [div_pow]
  rw [h_cos_div, h_sin_div, sqrt_nat_sq_eq]
  rw [← add_div]
  have h_add : Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 +
      Real.sin (Real.pi * (j.val : ℝ) / (n : ℝ)) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  rw [h_add]

end Real
