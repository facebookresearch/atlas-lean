/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Fib.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace MetaMathlibExt

private theorem fib_neg_eq (t : ℤ) : Int.fib (-t) = (-1 : ℤ) ^ ((t + 1).natAbs) * Int.fib t := by
  rw [Int.fib_neg]
  by_cases ht : Even t
  · have hodd : Odd (t + 1) := ht.add_odd odd_one
    have h1 : Odd ((t + 1).natAbs) := hodd.natAbs
    rw [h1.neg_one_pow]
    simp [ht]
  · have heven : Even (t + 1) := by
      rw [Int.even_add_one]
      exact ht
    have h1 : Even ((t + 1).natAbs) := Int.natAbs_even.mpr heven
    rw [h1.neg_one_pow]
    simp [ht]

private theorem neg_one_pow_natAbs_sq (e : ℤ) :
    ((-1 : ℤ) ^ (e.natAbs)) * ((-1 : ℤ) ^ (e.natAbs)) = 1 := by
  rw [← pow_add]
  exact (Even.add_self _).neg_one_pow

private theorem neg_one_natAbs_add (a b : ℤ) :
    (-1 : ℤ) ^ ((a + b).natAbs) = (-1 : ℤ) ^ (a.natAbs) * (-1 : ℤ) ^ (b.natAbs) := by
  rw [← pow_add]
  apply neg_one_pow_congr
  rw [Int.natAbs_even, Int.even_add, Nat.even_add, Int.natAbs_even, Int.natAbs_even]

private theorem neg_one_natAbs_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ((-1 : ℤ) ^ ((f i).natAbs)) = (-1 : ℤ) ^ ((∑ i ∈ s, f i).natAbs) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.sum_insert has, ih]
    exact (neg_one_natAbs_add (f a) (∑ i ∈ s, f i)).symm

private theorem E_step (m n : ℤ) :
    (Int.fib m * Int.fib ((n + 2) - 1) - Int.fib (m - 1) * Int.fib (n + 2)) =
      (Int.fib m * Int.fib (n - 1) - Int.fib (m - 1) * Int.fib n) +
      (Int.fib m * Int.fib ((n + 1) - 1) - Int.fib (m - 1) * Int.fib (n + 1)) := by
  have h1 : Int.fib (n + 2) = Int.fib n + Int.fib (n + 1) := by
    have := Int.fib_add_two n
    linarith
  have hcong : ((n - 1 : ℤ) + 1) = (n + 1 - 1) := by ring
  have h2 : Int.fib ((n + 2) - 1) = Int.fib (n - 1) + Int.fib (n + 1 - 1) := by
    have h : (n + 2 : ℤ) - 1 = (n - 1) + 2 := by ring
    rw [h, Int.fib_add_two, hcong]
  linear_combination Int.fib m * h2 - Int.fib (m - 1) * h1

private theorem E_base0 (m : ℤ) :
    Int.fib m * Int.fib ((0 : ℤ) - 1) - Int.fib (m - 1) * Int.fib 0 =
      (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib ((0 : ℤ) - m) := by
  have h01 : ((0 : ℤ) - 1) = -1 := by ring
  have h0m : ((0 : ℤ) - m) = -m := by ring
  rw [h01, h0m, Int.fib_neg_one, Int.fib_zero, mul_zero, sub_zero, mul_one]
  conv_rhs => rw [fib_neg_eq m]
  have hsq := neg_one_pow_natAbs_sq (m + 1)
  have hassoc : (-1 : ℤ) ^ ((m + 1).natAbs) * ((-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib m) =
      ((-1 : ℤ) ^ ((m + 1).natAbs) * (-1 : ℤ) ^ ((m + 1).natAbs)) * Int.fib m := by
    ring
  rw [hassoc, hsq, one_mul]

private theorem E_base1 (m : ℤ) :
    Int.fib m * Int.fib ((1 : ℤ) - 1) - Int.fib (m - 1) * Int.fib 1 =
      (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib ((1 : ℤ) - m) := by
  have h11 : ((1 : ℤ) - 1) = 0 := by ring
  rw [h11, Int.fib_zero, mul_zero, zero_sub, Int.fib_one, mul_one]
  have h1m : ((1 : ℤ) - m) = -(m - 1) := by ring
  rw [h1m, fib_neg_eq (m - 1)]
  have hBm : ((m - 1 + 1 : ℤ)).natAbs = m.natAbs := by
    congr 1
    ring
  rw [hBm]
  have hpar : Even (((m + 1 : ℤ)).natAbs) ↔ ¬ Even (m.natAbs) := by
    rw [Int.natAbs_even, Int.natAbs_even, Int.even_add_one]
  by_cases hA : Even (((m + 1 : ℤ)).natAbs)
  · have hB : Odd (m.natAbs) := Nat.not_even_iff_odd.mp (hpar.mp hA)
    rw [hA.neg_one_pow, hB.neg_one_pow]
    simp
  · have hB : Even (m.natAbs) := by
      by_contra hcon
      exact hA (hpar.mpr hcon)
    have hAodd : Odd (((m + 1 : ℤ)).natAbs) := Nat.not_even_iff_odd.mp hA
    rw [hAodd.neg_one_pow, hB.neg_one_pow]
    simp

private theorem RHS_step (m n : ℤ) :
    (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib ((n + 2) - m) =
      (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib (n - m) +
      (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib ((n + 1) - m) := by
  have h1 : ((n + 2 : ℤ) - m) = (n - m) + 2 := by ring
  have h2 : ((n + 1 : ℤ) - m) = (n - m) + 1 := by ring
  rw [h1, h2]
  have hf := Int.fib_add_two (n - m)
  have h3 : Int.fib ((n - m) + 2) = Int.fib (n - m) + Int.fib ((n - m) + 1) := by
    linarith
  rw [h3, mul_add]

private theorem fib_E (m n : ℤ) :
    Int.fib m * Int.fib (n - 1) - Int.fib (m - 1) * Int.fib n =
      (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib (n - m) := by
  have step : ∀ t : ℤ, (Int.fib m * Int.fib ((t + 2) - 1) - Int.fib (m - 1) * Int.fib (t + 2) -
      (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib ((t + 2) - m)) =
      (Int.fib m * Int.fib (t - 1) - Int.fib (m - 1) * Int.fib t -
        (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib (t - m)) +
      (Int.fib m * Int.fib ((t + 1) - 1) - Int.fib (m - 1) * Int.fib (t + 1) -
        (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib ((t + 1) - m)) := by
    intro t
    have hE := E_step m t
    have hR := RHS_step m t
    linarith
  have pos2 : ∀ t : ℕ,
      (Int.fib m * Int.fib (((t : ℤ)) - 1) - Int.fib (m - 1) * Int.fib t -
        (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib (t - m)) = 0 ∧
      (Int.fib m * Int.fib ((((t + 1 : ℕ) : ℤ)) - 1) - Int.fib (m - 1) * Int.fib ((t + 1 : ℕ) : ℤ) -
        (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib ((((t + 1 : ℕ) : ℤ)) - m)) = 0 := by
    intro t
    induction t with
    | zero =>
      have c0 : (((0 : ℕ) : ℤ)) = (0 : ℤ) := by simp
      have c1 : ((((0 + 1 : ℕ)) : ℤ)) = (1 : ℤ) := by simp
      rw [c0]
      constructor
      · have h := E_base0 m
        linarith
      · rw [c1]
        have h := E_base1 m
        linarith
    | succ t ih =>
      constructor
      · exact ih.2
      · have hs := E_step m ((t : ℤ))
        have hr := RHS_step m ((t : ℤ))
        have e1 : ((((t + 1 + 1 : ℕ)) : ℤ)) = ((t : ℤ)) + 2 := by push_cast; ring
        have e2 : ((((t + 1 : ℕ)) : ℤ)) = ((t : ℤ)) + 1 := by push_cast; ring
        rw [e1]
        rw [e2] at ih
        linarith [ih.1, ih.2, hs, hr]
  have pos : ∀ t : ℕ, (Int.fib m * Int.fib (((t : ℤ)) - 1) - Int.fib (m - 1) * Int.fib t -
      (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib (t - m)) = 0 := fun t => (pos2 t).1
  have neg2 : ∀ t : ℕ,
      (Int.fib m * Int.fib (((-(t : ℤ))) - 1) - Int.fib (m - 1) * Int.fib (-(t : ℤ)) -
        (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib ((-(t : ℤ)) - m)) = 0 ∧
      (Int.fib m * Int.fib (((-(((t + 1 : ℕ)) : ℤ))) - 1) -
        Int.fib (m - 1) * Int.fib (-(((t + 1 : ℕ)) : ℤ)) -
        (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib (((-(((t + 1 : ℕ)) : ℤ))) - m)) = 0 := by
    intro t
    induction t with
    | zero =>
      have c0 : ((-(0 : ℕ) : ℤ)) = (0 : ℤ) := by simp
      have c1 : ((-(((0 + 1 : ℕ)) : ℤ))) = (-1 : ℤ) := by simp
      rw [c0]
      constructor
      · have h := E_base0 m
        linarith
      · rw [c1]
        have h1 := pos 1
        have h0 := pos 0
        have hs := step (-1 : ℤ)
        have e1 : ((-1 : ℤ) + 2) = (1 : ℤ) := by ring
        have e2 : ((-1 : ℤ) + 1) = (0 : ℤ) := by ring
        rw [e1] at hs
        rw [e2] at hs
        simp only [Nat.cast_one, Nat.cast_zero] at h1 h0
        linarith
    | succ t ih =>
      constructor
      · exact ih.2
      · have hs := step (-(((t : ℤ)) + 2))
        have eA : (-(((t : ℤ)) + 2)) + 2 = -((t : ℤ)) := by ring
        have eB : (-(((t : ℤ)) + 2)) + 1 = -((((t + 1 : ℕ)) : ℤ)) := by push_cast; ring
        have eC : ((((t + 1 + 1 : ℕ)) : ℤ)) = ((t : ℤ)) + 2 := by push_cast; ring
        rw [eA, eB] at hs
        rw [eC]
        have eD : (-((((t + 1 : ℕ)) : ℤ))) = -(((t : ℤ)) + 1) := by push_cast; ring
        rw [eD] at ih hs
        linarith [ih.1, ih.2, hs]
  have neg : ∀ t : ℕ,
      (Int.fib m * Int.fib (((-(t : ℤ))) - 1) - Int.fib (m - 1) * Int.fib (-(t : ℤ)) -
        (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib ((-(t : ℤ)) - m)) = 0 := fun t => (neg2 t).1
  obtain ⟨t, rfl | rfl⟩ := n.eq_nat_or_neg
  · have h := pos t
    linarith
  · have h := neg t
    linarith

private theorem fib_D (m n k : ℤ) :
    Int.fib m * Int.fib (n + k) - Int.fib n * Int.fib (m + k) =
      (-1 : ℤ) ^ ((m + 1).natAbs) * (Int.fib k * Int.fib (n - m)) := by
  have hE : Int.fib m * Int.fib (n - 1) - Int.fib n * Int.fib (m - 1) =
      (-1 : ℤ) ^ ((m + 1).natAbs) * Int.fib (n - m) := by
    have h := fib_E m n
    linarith
  have h1 := Int.fib_add n k
  have h2 := Int.fib_add m k
  have hD : Int.fib m * Int.fib (n + k) - Int.fib n * Int.fib (m + k) =
      Int.fib k * (Int.fib m * Int.fib (n - 1) - Int.fib n * Int.fib (m - 1)) := by
    linear_combination Int.fib m * h1 - Int.fib n * h2
  rw [hD, hE]
  ring

private theorem card_pairs (r : ℕ) :
    ∑ i : Fin (r + 1), (Finset.Ioi i).card = Nat.choose (r + 1) 2 := by
  have h0 := Fin.sum_univ_eq_sum_range (fun t => r - t) (r + 1)
  have h1 : ∑ i : Fin (r + 1), (Finset.Ioi i).card = ∑ t ∈ Finset.range (r + 1), (r - t) := by
    rw [← h0]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.card_Ioi]
    omega
  rw [h1]
  have h2 : ∑ t ∈ Finset.range (r + 1), (r - t) = ∑ t ∈ Finset.range (r + 1), t := by
    have h := Finset.sum_range_reflect (fun t => t) (r + 1)
    simpa using h
  rw [h2, Finset.sum_range_id, Nat.choose_two_right]

private theorem wsum_range (r : ℕ) :
    ∑ t ∈ Finset.range (r + 1), t * (r - t) = Nat.choose (r + 1) 3 := by
  induction r with
  | zero => decide
  | succ r ih =>
    have hsplit : ∑ t ∈ Finset.range (r + 2), t * (r + 1 - t) =
        ∑ t ∈ Finset.range (r + 1), t * (r + 1 - t) := by
      rw [Finset.sum_range_succ]
      simp
    rw [hsplit]
    have hdecomp : ∑ t ∈ Finset.range (r + 1), t * (r + 1 - t) =
        (∑ t ∈ Finset.range (r + 1), t * (r - t)) +
        (∑ t ∈ Finset.range (r + 1), t) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      have htr : t ≤ r := by
        have := Finset.mem_range.mp ht
        omega
      have h1 : r + 1 - t = (r - t) + 1 := by omega
      rw [h1, Nat.mul_add, Nat.mul_one]
    rw [hdecomp, ih]
    have hpascal : Nat.choose (r + 2) 3 = Nat.choose (r + 1) 3 + Nat.choose (r + 1) 2 := by
      have h := Nat.choose_succ_succ (r + 1) 2
      rw [show (r + 1).succ = r + 2 from rfl, show Nat.succ 2 = 3 from rfl] at h
      have h2 : Nat.choose (r + 1) 2 + Nat.choose (r + 1) 3 =
          Nat.choose (r + 1) 3 + Nat.choose (r + 1) 2 := add_comm _ _
      rw [h2] at h
      exact h
    have hcard : ∑ t ∈ Finset.range (r + 1), t = Nat.choose (r + 1) 2 := by
      rw [Finset.sum_range_id, Nat.choose_two_right]
    rw [hcard]
    have hr2 : r + 1 + 1 = r + 2 := by ring
    rw [hr2]
    linarith [hpascal]

private theorem wsum_fin (r : ℕ) :
    ∑ i : Fin (r + 1), (i.val * (Finset.Ioi i).card) = Nat.choose (r + 1) 3 := by
  have h0 := Fin.sum_univ_eq_sum_range (fun t => t * (r - t)) (r + 1)
  have h1 : ∑ i : Fin (r + 1), (i.val * (Finset.Ioi i).card) =
      ∑ t ∈ Finset.range (r + 1), t * (r - t) := by
    rw [← h0]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.card_Ioi, Nat.add_sub_cancel]
  rw [h1]
  exact wsum_range r

private theorem pair_diff_prod_range (r : ℕ) (f : ℕ → ℤ) :
    ∏ t ∈ Finset.range (r + 1), ∏ u ∈ Finset.Ioc t r, f (u - t) =
      ∏ ℓ ∈ Finset.Icc 1 r, f ℓ ^ (r + 1 - ℓ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have houter : ∏ t ∈ Finset.range (r + 2), ∏ u ∈ Finset.Ioc t (r + 1), f (u - t) =
        ∏ t ∈ Finset.range (r + 1), ∏ u ∈ Finset.Ioc t (r + 1), f (u - t) := by
      rw [Finset.prod_range_succ]
      simp
    rw [houter]
    have hinner : ∀ t ∈ Finset.range (r + 1), ∏ u ∈ Finset.Ioc t (r + 1), f (u - t) =
        (∏ u ∈ Finset.Ioc t r, f (u - t)) * f ((r + 1) - t) := by
      intro t ht
      have htr : t ≤ r := by
        have := Finset.mem_range.mp ht
        omega
      have hIoc : Finset.Ioc t (r + 1) = insert (r + 1) (Finset.Ioc t r) := by
        ext u
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      rw [hIoc]
      rw [Finset.prod_insert]
      · ring
      · simp only [Finset.mem_Ioc]
        omega
    rw [Finset.prod_congr rfl hinner, Finset.prod_mul_distrib]
    rw [ih]
    have hnew : ∏ t ∈ Finset.range (r + 1), f ((r + 1) - t) =
        ∏ ℓ ∈ Finset.Icc 1 (r + 1), f ℓ := by
      have hrefl : ∏ t ∈ Finset.range (r + 1), f ((r + 1) - t) =
          ∏ t ∈ Finset.range (r + 1), f (t + 1) := by
        have h := Finset.prod_range_reflect (fun t => f (t + 1)) (r + 1)
        rw [← h]
        apply Finset.prod_congr rfl
        intro t ht
        have htr : t ≤ r := by
          have := Finset.mem_range.mp ht
          omega
        congr 1
        omega
      rw [hrefl]
      have himg : (Finset.range (r + 1)).image (fun t => t + 1) = Finset.Icc 1 (r + 1) := by
        ext x
        simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
        constructor
        · rintro ⟨t, ht, rfl⟩
          omega
        · intro h
          exact ⟨x - 1, by omega, by omega⟩
      rw [← himg]
      rw [Finset.prod_image]
      intro a _ b _ h
      have hab : a + 1 = b + 1 := h
      omega
    rw [hnew]
    have hrhs : ∏ ℓ ∈ Finset.Icc 1 (r + 1), f ℓ ^ (r + 1 + 1 - ℓ) =
        (∏ ℓ ∈ Finset.Icc 1 r, f ℓ ^ (r + 1 - ℓ)) * (∏ ℓ ∈ Finset.Icc 1 (r + 1), f ℓ) := by
      have hexp : ∀ ℓ ∈ Finset.Icc 1 (r + 1), f ℓ ^ (r + 1 + 1 - ℓ) =
          (f ℓ ^ (r + 1 - ℓ)) * f ℓ := by
        intro ℓ hℓ
        have hℓr : ℓ ≤ r + 1 := (Finset.mem_Icc.mp hℓ).2
        have he : r + 1 + 1 - ℓ = (r + 1 - ℓ) + 1 := by omega
        rw [he, pow_succ]
      rw [Finset.prod_congr rfl hexp, Finset.prod_mul_distrib]
      congr 1
      have htop : ∏ ℓ ∈ Finset.Icc 1 (r + 1), f ℓ ^ (r + 1 - ℓ) =
          ∏ ℓ ∈ Finset.Icc 1 r, f ℓ ^ (r + 1 - ℓ) := by
        have hsplit :=
          Finset.prod_Icc_succ_top (show 1 ≤ r + 1 by omega) (fun ℓ => f ℓ ^ (r + 1 - ℓ))
        rw [hsplit]
        simp
      exact htop
    have hr2 : r + 1 + 1 = r + 2 := by ring
    rw [hr2]
    linarith [hrhs]

private theorem pair_diff_prod_fin (r : ℕ) (f : ℕ → ℤ) :
    ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i, f (j.val - i.val) =
      ∏ ℓ ∈ Finset.Icc 1 r, f ℓ ^ (r + 1 - ℓ) := by
  have h0 := Fin.prod_univ_eq_prod_range
    (fun t => ∏ u ∈ Finset.Ioc t r, f (u - t)) (r + 1)
  have h1 : ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i, f (j.val - i.val) =
      ∏ t ∈ Finset.range (r + 1), ∏ u ∈ Finset.Ioc t r, f (u - t) := by
    rw [← h0]
    apply Finset.prod_congr rfl
    intro i _
    have hmap : (Finset.Ioi i).map Fin.valEmbedding = Finset.Ioo (i.val) (r + 1) := by
      exact Fin.map_valEmbedding_Ioi i
    have hIoo : Finset.Ioo (i.val) (r + 1) = Finset.Ioc (i.val) r := by
      ext u
      simp only [Finset.mem_Ioo, Finset.mem_Ioc]
      omega
    have hinner : ∏ j ∈ Finset.Ioi i, f (j.val - i.val) =
        ∏ u ∈ Finset.Ioo (i.val) (r + 1), f (u - i.val) := by
      rw [← hmap]
      rw [Finset.prod_map]
      apply Finset.prod_congr rfl
      intro j _
      simp
    rw [hinner, hIoo]
  rw [h1]
  exact pair_diff_prod_range r f

/--
**Alfred's determinant of consecutive Fibonacci powers.** Let $F_n$ denote the Fibonacci numbers
extended to all integers $n$ by $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$, so that
$F_{-n} = (-1)^{n+1} F_n$. For every natural number $r$ and all integers $s$ and $k$, the
$(r+1) \times (r+1)$ integer matrix whose entry in row $i$ and column $j$, for
$0 \le i, j \le r$, is $F_{s+ik}^{\,r-j} \, F_{s+(i+1)k}^{\,j}$ has determinant
$(-1)^{|e|} \, F_k^{\binom{r+1}{2}} \prod_{\ell=1}^{r} F_{k\ell}^{\,r+1-\ell}$, where
$e = (s+1)\binom{r+1}{2} + k\binom{r+1}{3}$.

This is a slight variation of a result of Brother U. Alfred, "Some determinants involving
powers of Fibonacci numbers," Fibonacci Quarterly 2 (1964), 81–92.

Proves `Wanted` entry `alfred_consecutive_fibonacci_powers_determinant`.

Source: Aram Tangboonduangjit and Thotsaporn Thanatipanonda,
"Determinants Containing Powers of Generalized Fibonacci Numbers,"
Journal of Integer Sequences 19 (2016), Article 16.7.1, Corollary
(label Alfred), lines 406–418,
https://cs.uwaterloo.ca/journals/JIS/VOL19/Tangboonduangjit/aram5.tex
-/
theorem alfred_consecutive_fibonacci_powers_determinant
    (r : ℕ) (s k : ℤ) :
    Matrix.det (fun (i j : Fin (r + 1)) =>
      Int.fib (s + (i.val : ℤ) * k) ^ (r - j.val) *
        Int.fib (s + ((i.val : ℤ) + 1) * k) ^ j.val) =
      (-1 : ℤ) ^ (((s + 1) * (Nat.choose (r + 1) 2 : ℤ) +
        k * (Nat.choose (r + 1) 3 : ℤ)).natAbs) *
        (Int.fib k ^ Nat.choose (r + 1) 2 *
          Finset.prod (Finset.Icc 1 r)
            (fun ℓ => Int.fib (k * (ℓ : ℤ)) ^ (r + 1 - ℓ))) := by
  have hmat : (fun (i j : Fin (r + 1)) =>
      Int.fib (s + (i.val : ℤ) * k) ^ (r - j.val) *
        Int.fib (s + ((i.val : ℤ) + 1) * k) ^ j.val) =
    Matrix.projVandermonde
      (fun i => Int.fib (s + ((i.val : ℤ) + 1) * k))
      (fun i => Int.fib (s + (i.val : ℤ) * k)) := by
    ext i j
    simp [Matrix.projVandermonde, Matrix.rectVandermonde]
    ring
  rw [hmat, Matrix.det_projVandermonde]
  have hfactor : ∀ i : Fin (r + 1), ∀ j ∈ Finset.Ioi i,
      (Int.fib (s + ((j.val : ℤ) + 1) * k) * Int.fib (s + (i.val : ℤ) * k) -
        Int.fib (s + ((i.val : ℤ) + 1) * k) * Int.fib (s + (j.val : ℤ) * k)) =
      (-1 : ℤ) ^ (((s + (i.val : ℤ) * k) + 1).natAbs) *
        (Int.fib k * Int.fib (((j.val : ℤ) - (i.val : ℤ)) * k)) := by
    intro i j _
    have hcomm : Int.fib (s + ((j.val : ℤ) + 1) * k) * Int.fib (s + (i.val : ℤ) * k) -
        Int.fib (s + ((i.val : ℤ) + 1) * k) * Int.fib (s + (j.val : ℤ) * k) =
        Int.fib (s + (i.val : ℤ) * k) * Int.fib (s + ((j.val : ℤ) + 1) * k) -
        Int.fib (s + (j.val : ℤ) * k) * Int.fib (s + ((i.val : ℤ) + 1) * k) := by
      ring
    rw [hcomm]
    have h := fib_D (s + (i.val : ℤ) * k) (s + (j.val : ℤ) * k) k
    have hmk : (s + (i.val : ℤ) * k) + k = s + ((i.val : ℤ) + 1) * k := by ring
    have hnk : (s + (j.val : ℤ) * k) + k = s + ((j.val : ℤ) + 1) * k := by ring
    have hnm : (s + (j.val : ℤ) * k) - (s + (i.val : ℤ) * k) =
        ((j.val : ℤ) - (i.val : ℤ)) * k := by ring
    rw [hmk, hnk, hnm] at h
    linarith
  have hrewrite : (∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
      (Int.fib (s + ((j.val : ℤ) + 1) * k) * Int.fib (s + (i.val : ℤ) * k) -
        Int.fib (s + ((i.val : ℤ) + 1) * k) * Int.fib (s + (j.val : ℤ) * k))) =
      ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
      ((-1 : ℤ) ^ (((s + (i.val : ℤ) * k) + 1).natAbs) *
        (Int.fib k * Int.fib (((j.val : ℤ) - (i.val : ℤ)) * k))) :=
    Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j hj => hfactor i j hj))
  rw [hrewrite]
  have hsplit_inner : ∀ i : Fin (r + 1),
      ∏ j ∈ Finset.Ioi i, ((-1 : ℤ) ^ (((s + (i.val : ℤ) * k) + 1).natAbs) *
        (Int.fib k * Int.fib (((j.val : ℤ) - (i.val : ℤ)) * k))) =
      (((-1 : ℤ) ^ (((s + (i.val : ℤ) * k) + 1).natAbs)) ^ (Finset.Ioi i).card) *
        (((Int.fib k) ^ (Finset.Ioi i).card) *
          ∏ j ∈ Finset.Ioi i, Int.fib (((j.val : ℤ) - (i.val : ℤ)) * k)) := by
    intro i
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_const]
  rw [Finset.prod_congr rfl (fun i _ => hsplit_inner i)]
  have houter : ∏ i : Fin (r + 1), (((-1 : ℤ) ^ (((s + (i.val : ℤ) * k) + 1).natAbs)) ^
      (Finset.Ioi i).card) * (((Int.fib k) ^ (Finset.Ioi i).card) *
        ∏ j ∈ Finset.Ioi i, Int.fib (((j.val : ℤ) - (i.val : ℤ)) * k)) =
      (∏ i : Fin (r + 1), ((-1 : ℤ) ^ (((s + (i.val : ℤ) * k) + 1).natAbs)) ^
        (Finset.Ioi i).card) *
      ((∏ i : Fin (r + 1), (Int.fib k) ^ (Finset.Ioi i).card) *
        ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
          Int.fib (((j.val : ℤ) - (i.val : ℤ)) * k)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [houter]
  have hsign : (∏ i : Fin (r + 1), ((-1 : ℤ) ^ (((s + (i.val : ℤ) * k) + 1).natAbs)) ^
      (Finset.Ioi i).card) =
      (-1 : ℤ) ^ (((s + 1) * (Nat.choose (r + 1) 2 : ℤ) +
        k * (Nat.choose (r + 1) 3 : ℤ)).natAbs) := by
    have hA : ∀ i : Fin (r + 1),
        (((-1 : ℤ) ^ (((s + (i.val : ℤ) * k) + 1).natAbs)) ^ (Finset.Ioi i).card) =
        (-1 : ℤ) ^ (((((Finset.Ioi i).card : ℕ) : ℤ) *
          ((s + (i.val : ℤ) * k) + 1)).natAbs) := by
      intro i
      rw [← pow_mul]
      congr 1
      rw [Int.natAbs_mul, Int.natAbs_natCast, mul_comm]
    rw [Finset.prod_congr rfl (fun i _ => hA i)]
    rw [neg_one_natAbs_sum]
    have hsum : ∑ i : Fin (r + 1), (((Finset.Ioi i).card : ℕ) : ℤ) *
        ((s + (i.val : ℤ) * k) + 1) =
        (s + 1) * (Nat.choose (r + 1) 2 : ℤ) + k * (Nat.choose (r + 1) 3 : ℤ) := by
      have hexpand : ∀ i : Fin (r + 1), (((Finset.Ioi i).card : ℕ) : ℤ) *
          ((s + (i.val : ℤ) * k) + 1) =
          (s + 1) * ((Finset.Ioi i).card : ℤ) + k * ((i.val : ℤ) * ((Finset.Ioi i).card : ℤ)) := by
        intro i
        ring
      rw [Finset.sum_congr rfl (fun i _ => hexpand i)]
      rw [Finset.sum_add_distrib]
      have hleft : ∑ i : Fin (r + 1), (s + 1) * (((Finset.Ioi i).card : ℕ) : ℤ) =
          (s + 1) * (Nat.choose (r + 1) 2 : ℤ) := by
        rw [← Finset.mul_sum]
        congr 1
        have h := card_pairs r
        have hc : ((Nat.choose (r + 1) 2 : ℕ) : ℤ) =
            ∑ i : Fin (r + 1), ((((Finset.Ioi i).card) : ℕ) : ℤ) := by
          rw [← Nat.cast_sum]
          congr 1
          exact h.symm
        have hc2 : (Nat.choose (r + 1) 2 : ℤ) =
            ∑ i : Fin (r + 1), (((Finset.Ioi i).card : ℕ) : ℤ) := hc
        rw [hc2]
      have hright : ∑ i : Fin (r + 1), k * ((i.val : ℤ) * (((Finset.Ioi i).card : ℕ) : ℤ)) =
          k * (Nat.choose (r + 1) 3 : ℤ) := by
        rw [← Finset.mul_sum]
        congr 1
        have h := wsum_fin r
        have hc : ((Nat.choose (r + 1) 3 : ℕ) : ℤ) =
            ∑ i : Fin (r + 1), ((((i.val * (Finset.Ioi i).card : ℕ))) : ℤ) := by
          rw [← Nat.cast_sum]
          congr 1
          exact h.symm
        rw [hc]
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.cast_mul]
      rw [hleft, hright]
    rw [hsum]
  have hfib : (∏ i : Fin (r + 1), (Int.fib k) ^ (Finset.Ioi i).card) =
      Int.fib k ^ Nat.choose (r + 1) 2 := by
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    exact card_pairs r
  have hprod : (∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
        Int.fib (((j.val : ℤ) - (i.val : ℤ)) * k)) =
      Finset.prod (Finset.Icc 1 r)
        (fun ℓ => Int.fib (k * (ℓ : ℤ)) ^ (r + 1 - ℓ)) := by
    have hbridge : ∀ i : Fin (r + 1), ∀ j ∈ Finset.Ioi i,
        Int.fib (((j.val : ℤ) - (i.val : ℤ)) * k) =
        (fun d : ℕ => Int.fib (k * ((d : ℕ) : ℤ))) (j.val - i.val) := by
      intro i j hj
      have hlt : i.val < j.val := Fin.lt_def.mp (Finset.mem_Ioi.mp hj)
      have hle : i.val ≤ j.val := le_of_lt hlt
      have hcast : (((j.val - i.val : ℕ)) : ℤ) = (j.val : ℤ) - (i.val : ℤ) :=
        Nat.cast_sub hle
      simp only
      rw [← hcast]
      congr 1
      ring
    have hre : (∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
          Int.fib (((j.val : ℤ) - (i.val : ℤ)) * k)) =
        ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
          (fun d : ℕ => Int.fib (k * ((d : ℕ) : ℤ))) (j.val - i.val) :=
      Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j hj => hbridge i j hj))
    rw [hre]
    exact pair_diff_prod_fin r (fun d : ℕ => Int.fib (k * ((d : ℕ) : ℤ)))
  rw [hsign, hfib, hprod]

end MetaMathlibExt
