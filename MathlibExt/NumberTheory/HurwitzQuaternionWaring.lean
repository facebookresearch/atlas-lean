/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

section

namespace MetaMathlibExt

/-- Hurwitz integrality predicate shared by all helpers. -/
private def IsHurwitz (z : Quaternion ℚ) : Prop :=
  (∃ a b c d : ℤ,
    z.re = (a : ℚ) ∧ z.imI = (b : ℚ) ∧ z.imJ = (c : ℚ) ∧ z.imK = (d : ℚ)) ∨
  (∃ a b c d : ℤ,
    z.re = (a : ℚ) + 1 / 2 ∧ z.imI = (b : ℚ) + 1 / 2 ∧
      z.imJ = (c : ℚ) + 1 / 2 ∧ z.imK = (d : ℚ) + 1 / 2)

/-- A sum over `Fin 0` vanishes. -/
private theorem sum_fin_zero {M : Type*} [AddCommMonoid M] (f : Fin 0 → M) :
    ∑ i, f i = 0 :=
  Fin.sum_univ_zero f

/-- Appending one summand to a `Fin`-indexed sum. -/
private theorem sum_snoc {M : Type*} [AddCommMonoid M] {n : ℕ}
    (f : Fin n → M) (c : M) (P : M → Prop)
    (hf : ∀ i, P (f i)) (hc : P c) :
    ∃ h : Fin (n + 1) → M, (∀ j, P (h j)) ∧
      ∑ i, h i = ∑ i, f i + c := by
  refine ⟨Fin.snoc f c, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < n
    · have hj' : j = Fin.castSucc ⟨j.val, hj⟩ := by
        ext
        rfl
      rw [hj', Fin.snoc_castSucc]
      exact hf _
    · have hjm : j.val = n := by
        have hlt := j.isLt
        omega
      have hj' : j = Fin.last n := by
        ext
        rw [Fin.val_last]
        exact hjm
      rw [hj', Fin.snoc_last]
      exact hc
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- Concatenating two `Fin`-indexed sums. -/
private theorem sum_combine {M : Type*} [AddCommMonoid M] {m : ℕ}
    (f : Fin m → M) {n : ℕ} (g : Fin n → M) (P : M → Prop)
    (hf : ∀ i, P (f i)) (hg : ∀ i, P (g i)) :
    ∃ h : Fin (m + n) → M, (∀ j, P (h j)) ∧
      ∑ i, h i = ∑ i, f i + ∑ i, g i := by
  induction n with
  | zero =>
    change ∃ h : Fin m → M, (∀ j, P (h j)) ∧
      ∑ i, h i = ∑ i, f i + ∑ i, g i
    refine ⟨f, hf, ?_⟩
    have hg0 : ∑ i, g i = 0 := sum_fin_zero g
    rw [hg0, add_zero]
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 from by omega]
    obtain ⟨h', hh', hsum'⟩ :=
      ih (fun i => g i.castSucc) (fun i => hg _)
    obtain ⟨h, hh, hsum⟩ := sum_snoc h' (g (Fin.last n)) P hh' (hg _)
    refine ⟨h, hh, ?_⟩
    rw [hsum, hsum', Fin.sum_univ_castSucc g, add_assoc]

/-- Flattening a dependently-indexed family of `Fin`-sums into one `Fin`-sum. -/
private theorem sum_kpiece {M : Type*} [AddCommMonoid M] {k : ℕ} :
    ∀ {s : Fin k → ℕ} (F : ∀ a, Fin (s a) → M) (P : M → Prop),
      (∀ a b, P (F a b)) →
      ∃ H : Fin (∑ a, s a) → M, (∀ j, P (H j)) ∧
        ∑ i, H i = ∑ a, ∑ b, F a b := by
  induction k with
  | zero =>
    intro s F P hF
    have hs : ∑ a, s a = 0 := sum_fin_zero s
    rw [hs]
    refine ⟨fun i => (Nat.not_lt_zero _ i.isLt).elim, ?_, ?_⟩
    · intro j
      exact (Nat.not_lt_zero _ j.isLt).elim
    · exact (sum_fin_zero _).trans (sum_fin_zero _).symm
  | succ k ih =>
    intro s F P hF
    rw [Fin.sum_univ_castSucc s]
    obtain ⟨H', hP', hsum'⟩ :=
      ih (fun a => F a.castSucc) P (fun a b => hF _ _)
    obtain ⟨H, hP, hsum⟩ :=
      sum_combine H' (fun b => F (Fin.last k) b) P hP' (fun b => hF _ _)
    refine ⟨H, hP, ?_⟩
    rw [hsum, hsum', Fin.sum_univ_castSucc (fun a => ∑ b, F a b)]

/-- Appending one powered summand to a `Fin`-indexed family of bases. -/
private theorem sum_snoc_pow {M : Type*} [AddCommMonoid M] [Pow M ℕ] {n : ℕ}
    (f : Fin n → M) (c : M) (P : M → Prop) (ℓ : ℕ)
    (hf : ∀ i, P (f i)) (hc : P c) :
    ∃ h : Fin (n + 1) → M, (∀ j, P (h j)) ∧
      ∑ i, (h i) ^ ℓ = ∑ i, (f i) ^ ℓ + c ^ ℓ := by
  refine ⟨Fin.snoc (α := fun _ => M) f c, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < n
    · have hj' : j = Fin.castSucc ⟨j.val, hj⟩ := by
        ext
        rfl
      rw [hj']
      simp only [Fin.snoc_castSucc]
      exact hf _
    · have hjm : j.val = n := by
        have hlt := j.isLt
        omega
      have hj' : j = Fin.last n := by
        ext
        rw [Fin.val_last]
        exact hjm
      rw [hj']
      simp only [Fin.snoc_last]
      exact hc
  · have hcast : ∀ i : Fin n,
        (Fin.snoc (α := fun _ => M) f c i.castSucc) ^ ℓ = (f i) ^ ℓ := by
      intro i
      simp only [Fin.snoc_castSucc]
    have hlast : (Fin.snoc (α := fun _ => M) f c (Fin.last n)) ^ ℓ = c ^ ℓ := by
      simp only [Fin.snoc_last]
    have hsum : (∑ i : Fin (n + 1), (Fin.snoc (α := fun _ => M) f c i) ^ ℓ) =
        (∑ i : Fin n, (Fin.snoc (α := fun _ => M) f c i.castSucc) ^ ℓ) +
        (Fin.snoc (α := fun _ => M) f c (Fin.last n)) ^ ℓ :=
      Fin.sum_univ_castSucc _
    have hS : (∑ i : Fin n, (Fin.snoc (α := fun _ => M) f c i.castSucc) ^ ℓ) =
        ∑ i : Fin n, (f i) ^ ℓ :=
      Finset.sum_congr rfl (fun i _ => hcast i)
    rw [hsum, hS, hlast]

/-- Concatenating two `Fin`-indexed families of bases. -/
private theorem sum_combine_pow {M : Type*} [AddCommMonoid M] [Pow M ℕ]
    {m : ℕ} (f : Fin m → M) {n : ℕ} (g : Fin n → M) (P : M → Prop) (ℓ : ℕ)
    (hf : ∀ i, P (f i)) (hg : ∀ i, P (g i)) :
    ∃ h : Fin (m + n) → M, (∀ j, P (h j)) ∧
      ∑ i, (h i) ^ ℓ = ∑ i, (f i) ^ ℓ + ∑ i, (g i) ^ ℓ := by
  induction n with
  | zero =>
    change ∃ h : Fin m → M, (∀ j, P (h j)) ∧
      ∑ i, (h i) ^ ℓ = ∑ i, (f i) ^ ℓ + ∑ i, (g i) ^ ℓ
    refine ⟨f, hf, ?_⟩
    have hg0 : ∑ i, (g i) ^ ℓ = 0 := sum_fin_zero _
    rw [hg0, add_zero]
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 from by omega]
    obtain ⟨h', hh', hsum'⟩ :=
      ih (fun i => g i.castSucc) (fun i => hg _)
    obtain ⟨h, hh, hsum⟩ := sum_snoc_pow h' (g (Fin.last n)) P ℓ hh' (hg _)
    refine ⟨h, hh, ?_⟩
    have hcast : (∑ i : Fin (n + 1), (g i) ^ ℓ) =
        (∑ i : Fin n, (g i.castSucc) ^ ℓ) + (g (Fin.last n)) ^ ℓ :=
      Fin.sum_univ_castSucc _
    rw [hsum, hsum', hcast, add_assoc]

/-- Flattening a dependently-indexed family of base-families. -/
private theorem sum_kpiece_pow {M : Type*} [AddCommMonoid M] [Pow M ℕ]
    {k : ℕ} :
    ∀ {s : Fin k → ℕ} (F : ∀ a, Fin (s a) → M) (P : M → Prop) (ℓ : ℕ),
      (∀ a b, P (F a b)) →
      ∃ H : Fin (∑ a, s a) → M, (∀ j, P (H j)) ∧
        ∑ i, (H i) ^ ℓ = ∑ a, ∑ b, (F a b) ^ ℓ := by
  induction k with
  | zero =>
    intro s F P ℓ hF
    have hs : ∑ a, s a = 0 := sum_fin_zero s
    rw [hs]
    refine ⟨fun i => (Nat.not_lt_zero _ i.isLt).elim, ?_, ?_⟩
    · intro j
      exact (Nat.not_lt_zero _ j.isLt).elim
    · exact (sum_fin_zero _).trans (sum_fin_zero _).symm
  | succ k ih =>
    intro s F P ℓ hF
    rw [Fin.sum_univ_castSucc s]
    obtain ⟨H', hP', hsum'⟩ :=
      ih (fun a => F a.castSucc) P ℓ (fun a b => hF _ _)
    obtain ⟨H, hP, hsum⟩ :=
      sum_combine_pow H' (fun b => F (Fin.last k) b) P ℓ hP' (fun b => hF _ _)
    refine ⟨H, hP, ?_⟩
    have hcast : (∑ a : Fin (k + 1), ∑ b, (F a b) ^ ℓ) =
        (∑ a : Fin k, ∑ b, (F a.castSucc b) ^ ℓ) +
        (∑ b, (F (Fin.last k) b) ^ ℓ) :=
      Fin.sum_univ_castSucc _
    rw [hsum, hsum', hcast]

/-- The finite-difference sum `H ℓ t m = ∑_{j ≤ ℓ} (-1)^{ℓ-j} C(ℓ,j) (m+j)^t`. -/
private def Hdiff (ℓ t : ℕ) (m : ℤ) : ℤ :=
  ∑ j ∈ Finset.range (ℓ + 1),
    (-1 : ℤ) ^ (ℓ - j) * ((ℓ.choose j : ℕ) : ℤ) * (m + (j : ℤ)) ^ t

/-- Pascal recurrence for the difference sums. -/
private theorem Hdiff_step (ℓ t : ℕ) (m : ℤ) :
    Hdiff (ℓ + 1) t m = Hdiff ℓ t (m + 1) - Hdiff ℓ t m := by
  have h1 : ∀ j ∈ Finset.range (ℓ + 1), ℓ + 1 - (j + 1) = ℓ - j := by
    intro j _
    omega
  have h2 : ∀ j : ℕ, (m : ℤ) + ((j + 1 : ℕ) : ℤ) = (m + 1) + (j : ℤ) := by
    intro j
    push_cast
    ring
  have hsplit : ∀ j ∈ Finset.range (ℓ + 1),
      (-1 : ℤ) ^ (ℓ + 1 - (j + 1)) * (((ℓ + 1).choose (j + 1) : ℕ) : ℤ) *
        (m + ((j + 1 : ℕ) : ℤ)) ^ t =
      ((-1 : ℤ) ^ (ℓ - j) * ((ℓ.choose j : ℕ) : ℤ) * ((m + 1) + (j : ℤ)) ^ t) +
      ((-1 : ℤ) ^ (ℓ - j) * ((ℓ.choose (j + 1) : ℕ) : ℤ) *
        ((m + 1) + (j : ℤ)) ^ t) := by
    intro j hj
    rw [h1 j hj, h2 j, Nat.choose_succ_succ', Nat.cast_add]
    ring
  have hshift : ∀ j ∈ Finset.range (ℓ + 1),
      (-1 : ℤ) ^ (ℓ - j) * ((ℓ.choose (j + 1) : ℕ) : ℤ) *
        ((m + 1) + (j : ℤ)) ^ t =
      (-1 : ℤ) ^ (ℓ + 1 - (j + 1)) * ((ℓ.choose (j + 1) : ℕ) : ℤ) *
        (m + ((j + 1 : ℕ) : ℤ)) ^ t := by
    intro j hj
    rw [h1 j hj, h2 j]
  have h0 : (-1 : ℤ) ^ (ℓ + 1 - 0) * ((((ℓ + 1).choose 0 : ℕ)) : ℤ) *
        (m + ((0 : ℕ) : ℤ)) ^ t =
      (-1 : ℤ) ^ (ℓ + 1 - 0) * (((ℓ.choose 0 : ℕ)) : ℤ) *
        (m + ((0 : ℕ) : ℤ)) ^ t := by
    rw [Nat.choose_zero_right, Nat.choose_zero_right]
  have hlt : ℓ < ℓ + 1 := by omega
  have hlast : (-1 : ℤ) ^ (ℓ + 1 - (ℓ + 1)) * (((ℓ.choose (ℓ + 1) : ℕ)) : ℤ) *
      (m + (((ℓ + 1 : ℕ)) : ℤ)) ^ t = 0 := by
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp only [Nat.cast_zero, mul_zero, zero_mul]
  have hneg : ∀ k ∈ Finset.range (ℓ + 1),
      (-1 : ℤ) ^ (ℓ + 1 - k) * ((ℓ.choose k : ℕ) : ℤ) * (m + (k : ℤ)) ^ t =
      -((-1 : ℤ) ^ (ℓ - k) * ((ℓ.choose k : ℕ) : ℤ) * (m + (k : ℤ)) ^ t) := by
    intro k hk
    have hkk : k ≤ ℓ := by
      have hmem := Finset.mem_range.mp hk
      omega
    have he : ℓ + 1 - k = (ℓ - k) + 1 := by omega
    rw [he, pow_succ]
    ring
  have hF0 : Hdiff (ℓ + 1) t m =
      (∑ j ∈ Finset.range (ℓ + 1),
        (-1 : ℤ) ^ (ℓ + 1 - (j + 1)) * (((ℓ + 1).choose (j + 1) : ℕ) : ℤ) *
        (m + ((j + 1 : ℕ) : ℤ)) ^ t) +
      ((-1 : ℤ) ^ (ℓ + 1 - 0) * ((((ℓ + 1).choose 0 : ℕ)) : ℤ) *
        (m + ((0 : ℕ) : ℤ)) ^ t) := by
    unfold Hdiff
    exact Finset.sum_range_succ' _ _
  have hsum : (∑ j ∈ Finset.range (ℓ + 1),
        (-1 : ℤ) ^ (ℓ + 1 - (j + 1)) * (((ℓ + 1).choose (j + 1) : ℕ) : ℤ) *
        (m + ((j + 1 : ℕ) : ℤ)) ^ t) =
      (∑ j ∈ Finset.range (ℓ + 1),
        (-1 : ℤ) ^ (ℓ - j) * ((ℓ.choose j : ℕ) : ℤ) *
        ((m + 1) + (j : ℤ)) ^ t) +
      (∑ j ∈ Finset.range (ℓ + 1),
        (-1 : ℤ) ^ (ℓ - j) * ((ℓ.choose (j + 1) : ℕ) : ℤ) *
        ((m + 1) + (j : ℤ)) ^ t) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j hj => hsplit j hj)
  have hback : (∑ j ∈ Finset.range (ℓ + 1),
        (-1 : ℤ) ^ (ℓ - j) * ((ℓ.choose (j + 1) : ℕ) : ℤ) *
        ((m + 1) + (j : ℤ)) ^ t) =
      ∑ j ∈ Finset.range (ℓ + 1),
        (-1 : ℤ) ^ (ℓ + 1 - (j + 1)) * ((ℓ.choose (j + 1) : ℕ) : ℤ) *
        (m + ((j + 1 : ℕ) : ℤ)) ^ t :=
    Finset.sum_congr rfl (fun j hj => hshift j hj)
  have hA : (∑ j ∈ Finset.range (ℓ + 1),
      (-1 : ℤ) ^ (ℓ - j) * ((ℓ.choose j : ℕ) : ℤ) *
      ((m + 1) + (j : ℤ)) ^ t) = Hdiff ℓ t (m + 1) := rfl
  have h5 : (∑ k ∈ Finset.range (ℓ + 1),
      (-1 : ℤ) ^ (ℓ + 1 - k) * ((ℓ.choose k : ℕ) : ℤ) *
      (m + (k : ℤ)) ^ t) = -(Hdiff ℓ t m) := by
    have hcongr : (∑ k ∈ Finset.range (ℓ + 1),
        (-1 : ℤ) ^ (ℓ + 1 - k) * ((ℓ.choose k : ℕ) : ℤ) *
        (m + (k : ℤ)) ^ t) =
        ∑ k ∈ Finset.range (ℓ + 1),
          -((-1 : ℤ) ^ (ℓ - k) * ((ℓ.choose k : ℕ) : ℤ) *
          (m + (k : ℤ)) ^ t) :=
      Finset.sum_congr rfl (fun k hk => hneg k hk)
    rw [hcongr, Finset.sum_neg_distrib]
    rfl
  have h3 : (∑ j ∈ Finset.range (ℓ + 1),
        (-1 : ℤ) ^ (ℓ + 1 - (j + 1)) * ((ℓ.choose (j + 1) : ℕ) : ℤ) *
        (m + ((j + 1 : ℕ) : ℤ)) ^ t) +
      ((-1 : ℤ) ^ (ℓ + 1 - 0) * (((ℓ.choose 0 : ℕ)) : ℤ) *
        (m + ((0 : ℕ) : ℤ)) ^ t) =
      ∑ k ∈ Finset.range (ℓ + 1 + 1),
        (-1 : ℤ) ^ (ℓ + 1 - k) * ((ℓ.choose k : ℕ) : ℤ) *
        (m + ((k : ℕ) : ℤ)) ^ t :=
    (Finset.sum_range_succ' (fun k =>
      (-1 : ℤ) ^ (ℓ + 1 - k) * ((ℓ.choose k : ℕ) : ℤ) *
      (m + ((k : ℕ) : ℤ)) ^ t) (ℓ + 1)).symm
  have h4 : (∑ k ∈ Finset.range (ℓ + 1 + 1),
      (-1 : ℤ) ^ (ℓ + 1 - k) * ((ℓ.choose k : ℕ) : ℤ) *
      (m + ((k : ℕ) : ℤ)) ^ t) =
      (∑ k ∈ Finset.range (ℓ + 1),
        (-1 : ℤ) ^ (ℓ + 1 - k) * ((ℓ.choose k : ℕ) : ℤ) *
        (m + (k : ℤ)) ^ t) +
      ((-1 : ℤ) ^ (ℓ + 1 - (ℓ + 1)) * (((ℓ.choose (ℓ + 1) : ℕ)) : ℤ) *
        (m + (((ℓ + 1 : ℕ)) : ℤ)) ^ t) :=
    Finset.sum_range_succ _ _
  have hG : (∑ j ∈ Finset.range (ℓ + 1),
        (-1 : ℤ) ^ (ℓ + 1 - (j + 1)) * ((ℓ.choose (j + 1) : ℕ) : ℤ) *
        (m + ((j + 1 : ℕ) : ℤ)) ^ t) +
      ((-1 : ℤ) ^ (ℓ + 1 - 0) * (((ℓ.choose 0 : ℕ)) : ℤ) *
        (m + ((0 : ℕ) : ℤ)) ^ t) =
      -(Hdiff ℓ t m) := by
    rw [h3, h4, hlast, add_zero]
    exact h5
  rw [hF0, hsum, h0, hback, add_assoc, hG, hA, sub_eq_add_neg]

/-- Binomial expansion of the difference sums in the base point. -/
private theorem Hdiff_expand (K T : ℕ) (m : ℤ) :
    Hdiff K T m = ∑ s ∈ Finset.range (T + 1),
      m ^ s * ((T.choose s : ℕ) : ℤ) * Hdiff K (T - s) 0 := by
  have hexpand : ∀ j : ℕ, (m + (j : ℤ)) ^ T =
      ∑ s ∈ Finset.range (T + 1),
        m ^ s * (j : ℤ) ^ (T - s) * ((T.choose s : ℕ) : ℤ) := by
    intro j
    exact add_pow m (j : ℤ) T
  have hA : Hdiff K T m = ∑ j ∈ Finset.range (K + 1),
      ((-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ)) *
      (∑ s ∈ Finset.range (T + 1),
        m ^ s * (j : ℤ) ^ (T - s) * ((T.choose s : ℕ) : ℤ)) := by
    have hrfl : Hdiff K T m = ∑ j ∈ Finset.range (K + 1),
        (-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ) * (m + (j : ℤ)) ^ T := rfl
    rw [hrfl]
    exact Finset.sum_congr rfl (fun j _ => by rw [hexpand j])
  have hB : (∑ j ∈ Finset.range (K + 1),
      ((-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ)) *
      (∑ s ∈ Finset.range (T + 1),
        m ^ s * (j : ℤ) ^ (T - s) * ((T.choose s : ℕ) : ℤ))) =
      ∑ j ∈ Finset.range (K + 1), ∑ s ∈ Finset.range (T + 1),
        ((-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ)) *
        (m ^ s * (j : ℤ) ^ (T - s) * ((T.choose s : ℕ) : ℤ)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  have hC : (∑ j ∈ Finset.range (K + 1), ∑ s ∈ Finset.range (T + 1),
        ((-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ)) *
        (m ^ s * (j : ℤ) ^ (T - s) * ((T.choose s : ℕ) : ℤ))) =
      ∑ s ∈ Finset.range (T + 1), ∑ j ∈ Finset.range (K + 1),
        ((-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ)) *
        (m ^ s * (j : ℤ) ^ (T - s) * ((T.choose s : ℕ) : ℤ)) :=
    Finset.sum_comm
  have hD : ∀ s ∈ Finset.range (T + 1),
      (∑ j ∈ Finset.range (K + 1),
        ((-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ)) *
        (m ^ s * (j : ℤ) ^ (T - s) * ((T.choose s : ℕ) : ℤ))) =
      m ^ s * ((T.choose s : ℕ) : ℤ) *
      (∑ j ∈ Finset.range (K + 1),
        ((-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ)) * (j : ℤ) ^ (T - s)) := by
    intro s _
    calc (∑ j ∈ Finset.range (K + 1),
            ((-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ)) *
            (m ^ s * (j : ℤ) ^ (T - s) * ((T.choose s : ℕ) : ℤ)))
          = ∑ j ∈ Finset.range (K + 1),
            (m ^ s * ((T.choose s : ℕ) : ℤ)) *
            (((-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ)) *
              (j : ℤ) ^ (T - s)) :=
          Finset.sum_congr rfl (fun j _ => by ring)
      _ = m ^ s * ((T.choose s : ℕ) : ℤ) *
          (∑ j ∈ Finset.range (K + 1),
            ((-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ)) *
            (j : ℤ) ^ (T - s)) := by
          rw [Finset.mul_sum]
  have hE : ∀ s ∈ Finset.range (T + 1),
      (∑ j ∈ Finset.range (K + 1),
        ((-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ)) * (j : ℤ) ^ (T - s)) =
      Hdiff K (T - s) 0 := by
    intro s _
    have hrfl : Hdiff K (T - s) 0 = ∑ j ∈ Finset.range (K + 1),
        (-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ) *
        ((0 : ℤ) + (j : ℤ)) ^ (T - s) := rfl
    rw [hrfl]
    apply Finset.sum_congr rfl
    intro j _
    rw [zero_add]
  have hF : ∀ s ∈ Finset.range (T + 1),
      (∑ j ∈ Finset.range (K + 1),
        ((-1 : ℤ) ^ (K - j) * ((K.choose j : ℕ) : ℤ)) *
        (m ^ s * (j : ℤ) ^ (T - s) * ((T.choose s : ℕ) : ℤ))) =
      m ^ s * ((T.choose s : ℕ) : ℤ) * Hdiff K (T - s) 0 := by
    intro s hs
    rw [hD s hs, hE s hs]
  rw [hA, hB, hC]
  exact Finset.sum_congr rfl (fun s hs => hF s hs)

/-- The difference sums vanish below the diagonal, equal `k!` on it, and grow
linearly just above it. -/
private theorem Hdiff_ABC : ∀ k : ℕ,
    (∀ t m, t < k → Hdiff k t m = 0) ∧
    (∀ m, Hdiff k k m = ((Nat.factorial k) : ℤ)) ∧
    (∀ m, Hdiff k (k + 1) m =
      ((Nat.factorial (k + 1)) : ℤ) * m + Hdiff k (k + 1) 0) := by
  intro k
  induction k with
  | zero =>
    have hH0 : ∀ t m, Hdiff 0 t m = m ^ t := by
      intro t m
      have hrfl : Hdiff 0 t m = ∑ j ∈ Finset.range 1,
          (-1 : ℤ) ^ (0 - j) * (((Nat.choose 0 j : ℕ)) : ℤ) *
          (m + (j : ℤ)) ^ t := rfl
      rw [hrfl, Finset.sum_range_one]
      simp only [Nat.sub_zero, pow_zero, Nat.choose_zero_right, Nat.cast_one,
        Nat.cast_zero, add_zero, mul_one, one_mul]
    have hf0 : Nat.factorial 0 = 1 := by decide
    refine ⟨?_, ?_, ?_⟩
    · intro t m ht
      omega
    · intro m
      simp only [hH0, pow_zero, hf0, Nat.cast_one]
    · intro m
      have e : (0 + 1 : ℕ) = 1 := by omega
      have hf1' : Nat.factorial 1 = 1 := by decide
      rw [hH0, hH0, e, hf1', Nat.cast_one, one_mul, pow_one, pow_one, add_zero]
  | succ k ih =>
    obtain ⟨ihA, ihB, ihC⟩ := ih
    have hA' : ∀ t m, t < k + 1 → Hdiff (k + 1) t m = 0 := by
      intro t m ht
      rw [Hdiff_step]
      rcases lt_or_eq_of_le (by omega : t ≤ k) with h | h
      · rw [ihA t (m + 1) h, ihA t m h, sub_self]
      · subst h
        rw [ihB (m + 1), ihB m, sub_self]
    have hB' : ∀ m, Hdiff (k + 1) (k + 1) m =
        ((Nat.factorial (k + 1)) : ℤ) := by
      intro m
      rw [Hdiff_step, ihC (m + 1), ihC m]
      ring
    refine ⟨hA', hB', ?_⟩
    intro m
    have hexp := Hdiff_expand (k + 1) ((k + 1) + 1) m
    rw [hexp]
    have hpeel1 : (∑ s ∈ Finset.range (((k + 1) + 1) + 1),
          m ^ s * (((((k + 1) + 1).choose s : ℕ)) : ℤ) *
          Hdiff (k + 1) (((k + 1) + 1) - s) 0) =
        (∑ s ∈ Finset.range ((k + 1) + 1),
          m ^ (s + 1) * (((((k + 1) + 1).choose (s + 1) : ℕ)) : ℤ) *
          Hdiff (k + 1) (((k + 1) + 1) - (s + 1)) 0) +
        (m ^ 0 * (((((k + 1) + 1).choose 0 : ℕ)) : ℤ) *
          Hdiff (k + 1) (((k + 1) + 1) - 0) 0) :=
      Finset.sum_range_succ' _ _
    have hpeel2 : (∑ s ∈ Finset.range ((k + 1) + 1),
          m ^ (s + 1) * (((((k + 1) + 1).choose (s + 1) : ℕ)) : ℤ) *
          Hdiff (k + 1) (((k + 1) + 1) - (s + 1)) 0) =
        (∑ s ∈ Finset.range (k + 1),
          m ^ ((s + 1) + 1) * (((((k + 1) + 1).choose ((s + 1) + 1) : ℕ)) : ℤ) *
          Hdiff (k + 1) (((k + 1) + 1) - ((s + 1) + 1)) 0) +
        (m ^ 1 * (((((k + 1) + 1).choose 1 : ℕ)) : ℤ) *
          Hdiff (k + 1) (((k + 1) + 1) - 1) 0) :=
      Finset.sum_range_succ' _ _
    have hrest : ∀ s ∈ Finset.range (k + 1),
        m ^ ((s + 1) + 1) * (((((k + 1) + 1).choose ((s + 1) + 1) : ℕ)) : ℤ) *
        Hdiff (k + 1) (((k + 1) + 1) - ((s + 1) + 1)) 0 = 0 := by
      intro s hs
      have hmem : s < k + 1 := Finset.mem_range.mp hs
      have hH : Hdiff (k + 1) (((k + 1) + 1) - ((s + 1) + 1)) 0 = 0 :=
        hA' _ 0 (by omega)
      rw [hH, mul_zero]
    have hrest0 : (∑ s ∈ Finset.range (k + 1),
        m ^ ((s + 1) + 1) * (((((k + 1) + 1).choose ((s + 1) + 1) : ℕ)) : ℤ) *
        Hdiff (k + 1) (((k + 1) + 1) - ((s + 1) + 1)) 0) = 0 :=
      Finset.sum_eq_zero (fun s hs => hrest s hs)
    have hG1 : m ^ 1 * (((((k + 1) + 1).choose 1 : ℕ)) : ℤ) *
        Hdiff (k + 1) (((k + 1) + 1) - 1) 0 =
        m * ((((k + 1) + 1) : ℕ) : ℤ) * ((Nat.factorial (k + 1)) : ℤ) := by
      have hT1 : ((k + 1) + 1) - 1 = k + 1 := by omega
      rw [hT1, hB' 0, Nat.choose_one_right, pow_one]
    have hG0 : m ^ 0 * (((((k + 1) + 1).choose 0 : ℕ)) : ℤ) *
        Hdiff (k + 1) (((k + 1) + 1) - 0) 0 =
        Hdiff (k + 1) ((k + 1) + 1) 0 := by
      rw [Nat.sub_zero, Nat.choose_zero_right, pow_zero, Nat.cast_one, mul_one,
        one_mul]
    rw [hpeel1, hpeel2, hrest0, zero_add, hG1, hG0]
    simp only [Nat.factorial_succ, Nat.cast_mul]
    ring

/-- Signed Waring representation over `ℤ`: every integer is a difference of two
bounded sums of `ℓ`-th powers. -/
private theorem signed_waring (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ B : ℕ, ∀ N : ℤ, ∃ (p q : ℕ) (x : Fin p → ℤ) (y : Fin q → ℤ),
      p + q ≤ B ∧ N = ∑ i, (x i) ^ ℓ - ∑ i, (y i) ^ ℓ := by
  obtain ⟨_, _, ihC⟩ := Hdiff_ABC (ℓ - 1)
  have hK : ℓ - 1 + 1 = ℓ := Nat.sub_add_cancel hℓ
  have hlin : ∀ m : ℤ, Hdiff (ℓ - 1) ℓ m =
      ((Nat.factorial ℓ) : ℤ) * m + Hdiff (ℓ - 1) ℓ 0 := by
    intro m
    have h := ihC m
    rw [hK] at h
    exact h
  have hH : ∀ m : ℤ, Hdiff (ℓ - 1) ℓ m =
      ∑ j ∈ Finset.range ℓ,
        ((-1 : ℤ) ^ (ℓ - 1 - j) * ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)) *
        (m + (j : ℤ)) ^ ℓ := by
    intro m
    have hrfl : Hdiff (ℓ - 1) ℓ m = ∑ j ∈ Finset.range (ℓ - 1 + 1),
        (-1 : ℤ) ^ (ℓ - 1 - j) * ((Nat.choose (ℓ - 1) j : ℕ) : ℤ) *
        (m + (j : ℤ)) ^ ℓ := rfl
    rw [hrfl, hK]
  have hz : ((0 : ℤ).toNat) = 0 := rfl
  have hsplit : ∀ j : ℕ, ∀ v : ℤ,
      ((-1 : ℤ) ^ (ℓ - 1 - j) * ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)) * v =
      (((max 0 ((-1 : ℤ) ^ (ℓ - 1 - j) *
        ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)))).toNat : ℤ) * v -
      (((max 0 (-((-1 : ℤ) ^ (ℓ - 1 - j) *
        ((Nat.choose (ℓ - 1) j : ℕ) : ℤ))))).toNat : ℤ) * v := by
    intro j v
    have hdecomp : ∀ d : ℤ, d =
        (((max 0 d).toNat : ℕ) : ℤ) - (((max 0 (-d)).toNat : ℕ) : ℤ) := by
      intro d
      by_cases hd : 0 ≤ d
      · rw [max_eq_right hd, max_eq_left (by omega : -d ≤ 0)]
        rw [hz, Nat.cast_zero, sub_zero]
        exact (Int.toNat_of_nonneg hd).symm
      · have hd' : d < 0 := by omega
        rw [max_eq_left (le_of_lt hd'), max_eq_right (by omega : (0 : ℤ) ≤ -d)]
        have hneg : 0 ≤ -d := by omega
        have hto := Int.toNat_of_nonneg hneg
        rw [hz, Nat.cast_zero, zero_sub, hto, neg_neg]
    have h := hdecomp ((-1 : ℤ) ^ (ℓ - 1 - j) *
      ((Nat.choose (ℓ - 1) j : ℕ) : ℤ))
    nth_rewrite 1 [h]
    ring
  have hcount : ∀ j : ℕ,
      (max 0 ((-1 : ℤ) ^ (ℓ - 1 - j) *
        ((Nat.choose (ℓ - 1) j : ℕ) : ℤ))).toNat +
      (max 0 (-((-1 : ℤ) ^ (ℓ - 1 - j) *
        ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)))).toNat =
      Int.toNat |(-1 : ℤ) ^ (ℓ - 1 - j) *
        ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)| := by
    intro j
    by_cases hd : 0 ≤ ((-1 : ℤ) ^ (ℓ - 1 - j) *
      ((Nat.choose (ℓ - 1) j : ℕ) : ℤ))
    · rw [max_eq_right hd, max_eq_left (by omega : -((-1 : ℤ) ^ (ℓ - 1 - j) *
        ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)) ≤ 0), abs_of_nonneg hd]
      rw [hz, add_zero]
    · have hd' : ((-1 : ℤ) ^ (ℓ - 1 - j) *
        ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)) < 0 := by omega
      rw [max_eq_left (le_of_lt hd'),
        max_eq_right (by omega : (0 : ℤ) ≤ -((-1 : ℤ) ^ (ℓ - 1 - j) *
          ((Nat.choose (ℓ - 1) j : ℕ) : ℤ))), abs_of_neg hd']
      rw [hz, zero_add]
  refine ⟨(∑ j ∈ Finset.range ℓ,
    Int.toNat |(-1 : ℤ) ^ (ℓ - 1 - j) *
      ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)|) + Nat.factorial ℓ, ?_⟩
  intro N
  have hMpos : (0 : ℤ) < ((Nat.factorial ℓ : ℕ) : ℤ) := by
    exact_mod_cast Nat.factorial_pos ℓ
  have hMne : ((Nat.factorial ℓ : ℕ) : ℤ) ≠ 0 := ne_of_gt hMpos
  obtain ⟨q, r, hdiv, hr0, hrM⟩ : ∃ q r : ℤ,
      ((Nat.factorial ℓ : ℕ) : ℤ) * q + r = N - Hdiff (ℓ - 1) ℓ 0 ∧
      0 ≤ r ∧ r < ((Nat.factorial ℓ : ℕ) : ℤ) :=
    ⟨_, _, Int.mul_ediv_add_emod _ _, Int.emod_nonneg _ hMne,
      Int.emod_lt_of_pos _ hMpos⟩
  have hNdecomp : N = Hdiff (ℓ - 1) ℓ q + r := by
    have hF := hlin q
    omega
  have hr : r = ((r.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hr0).symm
  have hN : N = (∑ j ∈ Finset.range ℓ, ((((max 0 ((-1 : ℤ) ^ (ℓ - 1 - j) *
          ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)))).toNat : ℤ) *
          (q + (j : ℤ)) ^ ℓ -
        (((max 0 (-((-1 : ℤ) ^ (ℓ - 1 - j) *
          ((Nat.choose (ℓ - 1) j : ℕ) : ℤ))))).toNat : ℤ) *
          (q + (j : ℤ)) ^ ℓ)) + ((r.toNat : ℕ) : ℤ) := by
    rw [hNdecomp, hH]
    nth_rewrite 1 [hr]
    have hS : (∑ j ∈ Finset.range ℓ,
          ((-1 : ℤ) ^ (ℓ - 1 - j) * ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)) *
          (q + (j : ℤ)) ^ ℓ) =
        ∑ j ∈ Finset.range ℓ, ((((max 0 ((-1 : ℤ) ^ (ℓ - 1 - j) *
            ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)))).toNat : ℤ) *
            (q + (j : ℤ)) ^ ℓ -
          (((max 0 (-((-1 : ℤ) ^ (ℓ - 1 - j) *
            ((Nat.choose (ℓ - 1) j : ℕ) : ℤ))))).toNat : ℤ) *
            (q + (j : ℤ)) ^ ℓ) :=
      Finset.sum_congr rfl (fun j _ => hsplit j _)
    rw [hS]
  have hrNat : r.toNat ≤ Nat.factorial ℓ := by
    have h1 : ((r.toNat : ℕ) : ℤ) < ((Nat.factorial ℓ : ℕ) : ℤ) := by
      rw [← hr]
      exact hrM
    have h2 : r.toNat < Nat.factorial ℓ := Nat.cast_lt.mp h1
    omega
  obtain ⟨Hp, _, hHpS⟩ := sum_kpiece_pow
    (s := fun a : Fin ℓ => (max 0 ((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
      ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ))).toNat)
    (fun a _ => (q + ((a : ℕ) : ℤ))) (fun _ => True) ℓ
    (fun _ _ => trivial)
  obtain ⟨Hm, _, hHmS⟩ := sum_kpiece_pow
    (s := fun a : Fin ℓ => (max 0 (-((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
      ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ)))).toNat)
    (fun a _ => (q + ((a : ℕ) : ℤ))) (fun _ => True) ℓ
    (fun _ _ => trivial)
  obtain ⟨P, _, hPS⟩ := sum_combine_pow Hp (fun _ : Fin r.toNat => (1 : ℤ))
    (fun _ => True) ℓ (fun _ => trivial) (fun _ => trivial)
  have hPeq : ∑ i, (P i) ^ ℓ = (∑ j ∈ Finset.range ℓ,
      ((((max 0 ((-1 : ℤ) ^ (ℓ - 1 - j) *
        ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)))).toNat : ℕ) : ℤ) *
      (q + (j : ℤ)) ^ ℓ) + ((r.toNat : ℕ) : ℤ) := by
    have eS : (∑ a : Fin ℓ, ∑ _ : Fin (max 0 ((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
        ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ))).toNat,
        ((q + ((a : ℕ) : ℤ)) ^ ℓ)) =
        ∑ a : Fin ℓ, ((((max 0 ((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
          ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ)))).toNat : ℕ) : ℤ) *
        (q + ((a : ℕ) : ℤ)) ^ ℓ := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have e3 : (∑ a : Fin ℓ, ((((max 0 ((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
        ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ)))).toNat : ℕ) : ℤ) *
        (q + ((a : ℕ) : ℤ)) ^ ℓ) =
        ∑ j ∈ Finset.range ℓ, ((((max 0 ((-1 : ℤ) ^ (ℓ - 1 - j) *
          ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)))).toNat : ℕ) : ℤ) *
        (q + (j : ℤ)) ^ ℓ :=
      Fin.sum_univ_eq_sum_range (fun j =>
        ((((max 0 ((-1 : ℤ) ^ (ℓ - 1 - j) *
          ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)))).toNat : ℕ) : ℤ) *
        (q + (j : ℤ)) ^ ℓ) ℓ
    have hR' : (∑ i : Fin r.toNat, ((fun _ : Fin r.toNat => (1 : ℤ)) i) ^ ℓ) =
        ((r.toNat : ℕ) : ℤ) := by
      simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
    rw [hPS, hHpS, eS, e3, hR']
  have hQeq : ∑ i, (Hm i) ^ ℓ = ∑ j ∈ Finset.range ℓ,
      ((((max 0 (-((-1 : ℤ) ^ (ℓ - 1 - j) *
        ((Nat.choose (ℓ - 1) j : ℕ) : ℤ))))).toNat : ℕ) : ℤ) *
      (q + (j : ℤ)) ^ ℓ := by
    have eS : (∑ a : Fin ℓ, ∑ _ : Fin (max 0 (-((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
        ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ)))).toNat,
        ((q + ((a : ℕ) : ℤ)) ^ ℓ)) =
        ∑ a : Fin ℓ, ((((max 0 (-((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
          ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ))))).toNat : ℕ) : ℤ) *
        (q + ((a : ℕ) : ℤ)) ^ ℓ := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have e3 : (∑ a : Fin ℓ, ((((max 0 (-((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
        ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ))))).toNat : ℕ) : ℤ) *
        (q + ((a : ℕ) : ℤ)) ^ ℓ) =
        ∑ j ∈ Finset.range ℓ, ((((max 0 (-((-1 : ℤ) ^ (ℓ - 1 - j) *
          ((Nat.choose (ℓ - 1) j : ℕ) : ℤ))))).toNat : ℕ) : ℤ) *
        (q + (j : ℤ)) ^ ℓ :=
      Fin.sum_univ_eq_sum_range (fun j =>
        ((((max 0 (-((-1 : ℤ) ^ (ℓ - 1 - j) *
          ((Nat.choose (ℓ - 1) j : ℕ) : ℤ))))).toNat : ℕ) : ℤ) *
        (q + (j : ℤ)) ^ ℓ) ℓ
    rw [hHmS, eS, e3]
  have hNfin : N = ∑ i, (P i) ^ ℓ - ∑ i, (Hm i) ^ ℓ := by
    rw [hPeq, hQeq, hN, Finset.sum_sub_distrib]
    ring
  have hcountS : (∑ a : Fin ℓ, ((max 0 ((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
      ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ))).toNat +
      (max 0 (-((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
      ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ)))).toNat)) =
      ∑ j ∈ Finset.range ℓ, Int.toNat |(-1 : ℤ) ^ (ℓ - 1 - j) *
        ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)| := by
    have e1 : (∑ a : Fin ℓ, ((max 0 ((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
        ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ))).toNat +
        (max 0 (-((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
        ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ)))).toNat)) =
        ∑ a : Fin ℓ, Int.toNat |(-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
          ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ)| :=
      Finset.sum_congr rfl (fun a _ => hcount _)
    have e2 : (∑ a : Fin ℓ, Int.toNat |(-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
        ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ)|) =
        ∑ j ∈ Finset.range ℓ, Int.toNat |(-1 : ℤ) ^ (ℓ - 1 - j) *
          ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)| :=
      Fin.sum_univ_eq_sum_range (fun j => Int.toNat |(-1 : ℤ) ^ (ℓ - 1 - j) *
        ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)|) ℓ
    rw [e1, e2]
  refine ⟨_, _, P, Hm, ?_, hNfin⟩
  have hsplit2 : (∑ a : Fin ℓ, (max 0 ((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
      ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ))).toNat) +
      (∑ a : Fin ℓ, (max 0 (-((-1 : ℤ) ^ (ℓ - 1 - (a : ℕ)) *
      ((Nat.choose (ℓ - 1) (a : ℕ) : ℕ) : ℤ)))).toNat) =
      ∑ j ∈ Finset.range ℓ, Int.toNat |(-1 : ℤ) ^ (ℓ - 1 - j) *
        ((Nat.choose (ℓ - 1) j : ℕ) : ℤ)| := by
    rw [← Finset.sum_add_distrib]
    exact hcountS
  omega

private theorem hurwitz_one : IsHurwitz 1 := by
  refine Or.inl ⟨1, 0, 0, 0, ?_, ?_, ?_, ?_⟩
  · simp only [Quaternion.re_one, Int.cast_one]
  · simp only [Quaternion.imI_one, Int.cast_zero]
  · simp only [Quaternion.imJ_one, Int.cast_zero]
  · simp only [Quaternion.imK_one, Int.cast_zero]

private theorem hurwitz_uA :
    IsHurwitz (⟨-1/2, 1/2, 1/2, 1/2⟩ : Quaternion ℚ) := by
  refine Or.inr ⟨-1, 0, 0, 0, ?_, ?_, ?_, ?_⟩
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num
  · change (1/2 : ℚ) = ((0 : ℤ) : ℚ) + 1/2
    norm_num
  · change (1/2 : ℚ) = ((0 : ℤ) : ℚ) + 1/2
    norm_num
  · change (1/2 : ℚ) = ((0 : ℤ) : ℚ) + 1/2
    norm_num

private theorem hurwitz_uA2 :
    IsHurwitz (⟨-1/2, -1/2, -1/2, -1/2⟩ : Quaternion ℚ) := by
  refine Or.inr ⟨-1, -1, -1, -1, ?_, ?_, ?_, ?_⟩
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num

private theorem hurwitz_uB :
    IsHurwitz (⟨-1/2, 1/2, -1/2, -1/2⟩ : Quaternion ℚ) := by
  refine Or.inr ⟨-1, 0, -1, -1, ?_, ?_, ?_, ?_⟩
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num
  · change (1/2 : ℚ) = ((0 : ℤ) : ℚ) + 1/2
    norm_num
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num

private theorem hurwitz_uC :
    IsHurwitz (⟨-1/2, -1/2, 1/2, 1/2⟩ : Quaternion ℚ) := by
  refine Or.inr ⟨-1, -1, 0, 0, ?_, ?_, ?_, ?_⟩
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num
  · change (1/2 : ℚ) = ((0 : ℤ) : ℚ) + 1/2
    norm_num
  · change (1/2 : ℚ) = ((0 : ℤ) : ℚ) + 1/2
    norm_num

private theorem hurwitz_uD :
    IsHurwitz (⟨-1/2, -1/2, 1/2, -1/2⟩ : Quaternion ℚ) := by
  refine Or.inr ⟨-1, -1, 0, -1, ?_, ?_, ?_, ?_⟩
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num
  · change (1/2 : ℚ) = ((0 : ℤ) : ℚ) + 1/2
    norm_num
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num

private theorem hurwitz_uE :
    IsHurwitz (⟨-1/2, 1/2, -1/2, 1/2⟩ : Quaternion ℚ) := by
  refine Or.inr ⟨-1, 0, -1, 0, ?_, ?_, ?_, ?_⟩
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num
  · change (1/2 : ℚ) = ((0 : ℤ) : ℚ) + 1/2
    norm_num
  · change (-1/2 : ℚ) = ((-1 : ℤ) : ℚ) + 1/2
    norm_num
  · change (1/2 : ℚ) = ((0 : ℤ) : ℚ) + 1/2
    norm_num

private theorem pow3_uA :
    (⟨-1/2, 1/2, 1/2, 1/2⟩ : Quaternion ℚ) ^ 3 = 1 := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one, pow_succ, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
  all_goals norm_num

private theorem pow3_uA2 :
    (⟨-1/2, -1/2, -1/2, -1/2⟩ : Quaternion ℚ) ^ 3 = 1 := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one, pow_succ, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
  all_goals norm_num

private theorem pow3_uB :
    (⟨-1/2, 1/2, -1/2, -1/2⟩ : Quaternion ℚ) ^ 3 = 1 := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one, pow_succ, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
  all_goals norm_num

private theorem pow3_uC :
    (⟨-1/2, -1/2, 1/2, 1/2⟩ : Quaternion ℚ) ^ 3 = 1 := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one, pow_succ, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
  all_goals norm_num

private theorem pow3_uD :
    (⟨-1/2, -1/2, 1/2, -1/2⟩ : Quaternion ℚ) ^ 3 = 1 := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one, pow_succ, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
  all_goals norm_num

private theorem pow3_uE :
    (⟨-1/2, 1/2, -1/2, 1/2⟩ : Quaternion ℚ) ^ 3 = 1 := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one, pow_succ, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
  all_goals norm_num

private theorem pow_mod3_one (u : Quaternion ℚ) (n : ℕ) (h3 : u ^ 3 = 1)
    (hmod : n % 3 = 1) : u ^ n = u := by
  have hdiv := Nat.div_add_mod n 3
  rw [hmod] at hdiv
  have hexp : u ^ n = u ^ (3 * (n / 3) + 1) := by
    conv_lhs => rw [← hdiv]
  rw [hexp, pow_add, pow_mul, h3, one_pow, pow_one, one_mul]

private theorem pow_mod3_two (u : Quaternion ℚ) (n : ℕ) (h3 : u ^ 3 = 1)
    (hmod : n % 3 = 2) : u ^ n = u ^ 2 := by
  have hdiv := Nat.div_add_mod n 3
  rw [hmod] at hdiv
  have hexp : u ^ n = u ^ (3 * (n / 3) + 2) := by
    conv_lhs => rw [← hdiv]
  rw [hexp, pow_add, pow_mul, h3, one_pow, one_mul]

private theorem pow_ell_twice (u : Quaternion ℚ) (ℓ : ℕ)
    (hmod : ℓ % 3 = 1 ∨ ℓ % 3 = 2) (h3 : u ^ 3 = 1) :
    (u ^ ℓ) ^ ℓ = u := by
  rcases hmod with h1 | h2
  · rw [pow_mod3_one u ℓ h3 h1, pow_mod3_one u ℓ h3 h1]
  · rw [pow_mod3_two u ℓ h3 h2, ← pow_mul]
    have h21 : (2 * ℓ) % 3 = 1 := by omega
    exact pow_mod3_one u (2 * ℓ) h3 h21

private theorem hurwitz_sq_uA :
    IsHurwitz ((⟨-1/2, 1/2, 1/2, 1/2⟩ : Quaternion ℚ) ^ 2) := by
  refine Or.inr ⟨-1, -1, -1, -1, ?_, ?_, ?_, ?_⟩
  · simp only [pow_two, Quaternion.re_mul]
    norm_num
  · simp only [pow_two, Quaternion.imI_mul]
    norm_num
  · simp only [pow_two, Quaternion.imJ_mul]
    norm_num
  · simp only [pow_two, Quaternion.imK_mul]
    norm_num

private theorem hurwitz_sq_uA2 :
    IsHurwitz ((⟨-1/2, -1/2, -1/2, -1/2⟩ : Quaternion ℚ) ^ 2) := by
  refine Or.inr ⟨-1, 0, 0, 0, ?_, ?_, ?_, ?_⟩
  · simp only [pow_two, Quaternion.re_mul]
    norm_num
  · simp only [pow_two, Quaternion.imI_mul]
    norm_num
  · simp only [pow_two, Quaternion.imJ_mul]
    norm_num
  · simp only [pow_two, Quaternion.imK_mul]
    norm_num

private theorem hurwitz_sq_uB :
    IsHurwitz ((⟨-1/2, 1/2, -1/2, -1/2⟩ : Quaternion ℚ) ^ 2) := by
  refine Or.inr ⟨-1, -1, 0, 0, ?_, ?_, ?_, ?_⟩
  · simp only [pow_two, Quaternion.re_mul]
    norm_num
  · simp only [pow_two, Quaternion.imI_mul]
    norm_num
  · simp only [pow_two, Quaternion.imJ_mul]
    norm_num
  · simp only [pow_two, Quaternion.imK_mul]
    norm_num

private theorem hurwitz_sq_uC :
    IsHurwitz ((⟨-1/2, -1/2, 1/2, 1/2⟩ : Quaternion ℚ) ^ 2) := by
  refine Or.inr ⟨-1, 0, -1, -1, ?_, ?_, ?_, ?_⟩
  · simp only [pow_two, Quaternion.re_mul]
    norm_num
  · simp only [pow_two, Quaternion.imI_mul]
    norm_num
  · simp only [pow_two, Quaternion.imJ_mul]
    norm_num
  · simp only [pow_two, Quaternion.imK_mul]
    norm_num

private theorem hurwitz_sq_uD :
    IsHurwitz ((⟨-1/2, -1/2, 1/2, -1/2⟩ : Quaternion ℚ) ^ 2) := by
  refine Or.inr ⟨-1, 0, -1, 0, ?_, ?_, ?_, ?_⟩
  · simp only [pow_two, Quaternion.re_mul]
    norm_num
  · simp only [pow_two, Quaternion.imI_mul]
    norm_num
  · simp only [pow_two, Quaternion.imJ_mul]
    norm_num
  · simp only [pow_two, Quaternion.imK_mul]
    norm_num

private theorem hurwitz_sq_uE :
    IsHurwitz ((⟨-1/2, 1/2, -1/2, 1/2⟩ : Quaternion ℚ) ^ 2) := by
  refine Or.inr ⟨-1, -1, 0, -1, ?_, ?_, ?_, ?_⟩
  · simp only [pow_two, Quaternion.re_mul]
    norm_num
  · simp only [pow_two, Quaternion.imI_mul]
    norm_num
  · simp only [pow_two, Quaternion.imJ_mul]
    norm_num
  · simp only [pow_two, Quaternion.imK_mul]
    norm_num

private theorem hurwitz_pow_ell (u : Quaternion ℚ) (ℓ : ℕ)
    (hmod : ℓ % 3 = 1 ∨ ℓ % 3 = 2) (h3 : u ^ 3 = 1)
    (hu : IsHurwitz u) (hu2 : IsHurwitz (u ^ 2)) :
    IsHurwitz (u ^ ℓ) := by
  rcases hmod with h1 | h2
  · rw [pow_mod3_one u ℓ h3 h1]
    exact hu
  · rw [pow_mod3_two u ℓ h3 h2]
    exact hu2

private theorem neg_one_eq :
    (-1 : Quaternion ℚ) =
      (⟨-1/2, 1/2, 1/2, 1/2⟩ : Quaternion ℚ) +
      (⟨-1/2, -1/2, -1/2, -1/2⟩ : Quaternion ℚ) := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg,
      Quaternion.imK_neg, Quaternion.re_one, Quaternion.imI_one,
      Quaternion.imJ_one, Quaternion.imK_one, Quaternion.re_add,
      Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add]
  all_goals norm_num

private theorem i_pos_eq :
    (⟨0, 1, 0, 0⟩ : Quaternion ℚ) = 1 +
      (⟨-1/2, 1/2, 1/2, 1/2⟩ : Quaternion ℚ) +
      (⟨-1/2, 1/2, -1/2, -1/2⟩ : Quaternion ℚ) := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add]
  all_goals norm_num

private theorem i_neg_eq :
    -((⟨0, 1, 0, 0⟩ : Quaternion ℚ)) = 1 +
      (⟨-1/2, -1/2, 1/2, 1/2⟩ : Quaternion ℚ) +
      (⟨-1/2, -1/2, -1/2, -1/2⟩ : Quaternion ℚ) := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg,
      Quaternion.imK_neg, Quaternion.re_one, Quaternion.imI_one,
      Quaternion.imJ_one, Quaternion.imK_one, Quaternion.re_add,
      Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add]
  all_goals norm_num

private theorem j_pos_eq :
    (⟨0, 0, 1, 0⟩ : Quaternion ℚ) = 1 +
      (⟨-1/2, 1/2, 1/2, 1/2⟩ : Quaternion ℚ) +
      (⟨-1/2, -1/2, 1/2, -1/2⟩ : Quaternion ℚ) := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add]
  all_goals norm_num

private theorem j_neg_eq :
    -((⟨0, 0, 1, 0⟩ : Quaternion ℚ)) = 1 +
      (⟨-1/2, 1/2, -1/2, 1/2⟩ : Quaternion ℚ) +
      (⟨-1/2, -1/2, -1/2, -1/2⟩ : Quaternion ℚ) := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg,
      Quaternion.imK_neg, Quaternion.re_one, Quaternion.imI_one,
      Quaternion.imJ_one, Quaternion.imK_one, Quaternion.re_add,
      Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add]
  all_goals norm_num

private theorem k_pos_eq :
    (⟨0, 0, 0, 1⟩ : Quaternion ℚ) = 1 +
      (⟨-1/2, -1/2, 1/2, 1/2⟩ : Quaternion ℚ) +
      (⟨-1/2, 1/2, -1/2, 1/2⟩ : Quaternion ℚ) := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add]
  all_goals norm_num

private theorem k_neg_eq :
    -((⟨0, 0, 0, 1⟩ : Quaternion ℚ)) = 1 +
      (⟨-1/2, 1/2, -1/2, -1/2⟩ : Quaternion ℚ) +
      (⟨-1/2, -1/2, 1/2, -1/2⟩ : Quaternion ℚ) := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg,
      Quaternion.imK_neg, Quaternion.re_one, Quaternion.imI_one,
      Quaternion.imJ_one, Quaternion.imK_one, Quaternion.re_add,
      Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add]
  all_goals norm_num

private theorem w0_pos_eq :
    (⟨1/2, 1/2, 1/2, 1/2⟩ : Quaternion ℚ) = 1 +
      (⟨-1/2, 1/2, 1/2, 1/2⟩ : Quaternion ℚ) := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add]
  all_goals norm_num

private theorem tmp_test : (⟨-1/2, 1/2, 1/2, 1/2⟩ : Quaternion ℚ) ^ 2 +
    (⟨-1/2, 1/2, 1/2, 1/2⟩ : Quaternion ℚ) + 1 = 0 := by
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
      Quaternion.imK_add, Quaternion.re_one, Quaternion.imI_one,
      Quaternion.imJ_one, Quaternion.imK_one, Quaternion.re_zero,
      Quaternion.imI_zero, Quaternion.imJ_zero, Quaternion.imK_zero,
      pow_two, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]
  all_goals norm_num

private theorem hurwitz_intCast (n : ℤ) : IsHurwitz (n : Quaternion ℚ) := by
  refine Or.inl ⟨n, 0, 0, 0, ?_, ?_, ?_, ?_⟩
  · rw [← Quaternion.coe_intCast, Quaternion.re_coe]
  · rw [← Quaternion.coe_intCast, Quaternion.imI_coe]
    simp only [Int.cast_zero]
  · rw [← Quaternion.coe_intCast, Quaternion.imJ_coe]
    simp only [Int.cast_zero]
  · rw [← Quaternion.coe_intCast, Quaternion.imK_coe]
    simp only [Int.cast_zero]

private theorem hurwitz_intCast_mul (n : ℤ) (v : Quaternion ℚ)
    (hv : IsHurwitz v) : IsHurwitz ((n : Quaternion ℚ) * v) := by
  have hn_re : (n : Quaternion ℚ).re = (n : ℚ) := by
    rw [← Quaternion.coe_intCast, Quaternion.re_coe]
  have hn_I : (n : Quaternion ℚ).imI = 0 := by
    rw [← Quaternion.coe_intCast, Quaternion.imI_coe]
  have hn_J : (n : Quaternion ℚ).imJ = 0 := by
    rw [← Quaternion.coe_intCast, Quaternion.imJ_coe]
  have hn_K : (n : Quaternion ℚ).imK = 0 := by
    rw [← Quaternion.coe_intCast, Quaternion.imK_coe]
  rcases hv with ⟨a, b, c, d, ha, hb, hc, hd⟩ | ⟨a, b, c, d, ha, hb, hc, hd⟩
  · refine Or.inl ⟨n * a, n * b, n * c, n * d, ?_, ?_, ?_, ?_⟩
    · rw [Quaternion.re_mul, hn_re, hn_I, hn_J, hn_K, ha, hb, hc, hd]
      push_cast
      ring
    · rw [Quaternion.imI_mul, hn_re, hn_I, hn_J, hn_K, ha, hb, hc, hd]
      push_cast
      ring
    · rw [Quaternion.imJ_mul, hn_re, hn_I, hn_J, hn_K, ha, hb, hc, hd]
      push_cast
      ring
    · rw [Quaternion.imK_mul, hn_re, hn_I, hn_J, hn_K, ha, hb, hc, hd]
      push_cast
      ring
  · by_cases hev : Even n
    · obtain ⟨t, ht⟩ := hev
      have hn2 : n = 2 * t := by omega
      have hnc : (n : ℚ) = 2 * (t : ℚ) := by exact_mod_cast hn2
      refine Or.inl ⟨n * a + t, n * b + t, n * c + t, n * d + t, ?_, ?_, ?_, ?_⟩
      · rw [Quaternion.re_mul, hn_re, hn_I, hn_J, hn_K, ha]
        push_cast
        rw [hnc]
        ring
      · rw [Quaternion.imI_mul, hn_re, hn_I, hn_J, hn_K, hb]
        push_cast
        rw [hnc]
        ring
      · rw [Quaternion.imJ_mul, hn_re, hn_I, hn_J, hn_K, hc]
        push_cast
        rw [hnc]
        ring
      · rw [Quaternion.imK_mul, hn_re, hn_I, hn_J, hn_K, hd]
        push_cast
        rw [hnc]
        ring
    · have hem : n % 2 = 1 := Int.not_even_iff.mp hev
      have hodd : Odd n := ⟨n / 2, by omega⟩
      obtain ⟨t, ht⟩ := hodd
      have hnc : (n : ℚ) = 2 * (t : ℚ) + 1 := by exact_mod_cast ht
      refine Or.inr ⟨n * a + t, n * b + t, n * c + t, n * d + t, ?_, ?_, ?_, ?_⟩
      · rw [Quaternion.re_mul, hn_re, hn_I, hn_J, hn_K, ha]
        push_cast
        rw [hnc]
        ring
      · rw [Quaternion.imI_mul, hn_re, hn_I, hn_J, hn_K, hb]
        push_cast
        rw [hnc]
        ring
      · rw [Quaternion.imJ_mul, hn_re, hn_I, hn_J, hn_K, hc]
        push_cast
        rw [hnc]
        ring
      · rw [Quaternion.imK_mul, hn_re, hn_I, hn_J, hn_K, hd]
        push_cast
        rw [hnc]
        ring

private theorem intCast_eq_mk (n : ℤ) :
    (n : Quaternion ℚ) = (⟨(n : ℚ), 0, 0, 0⟩ : Quaternion ℚ) := by
  rw [← Quaternion.coe_intCast]
  rfl

private theorem intCast_mul_i (n : ℤ) :
    ((n : Quaternion ℚ)) * (⟨0, 1, 0, 0⟩ : Quaternion ℚ) =
      (⟨0, (n : ℚ), 0, 0⟩ : Quaternion ℚ) := by
  have hn_re : (n : Quaternion ℚ).re = (n : ℚ) := by
    rw [← Quaternion.coe_intCast, Quaternion.re_coe]
  have hn_I : (n : Quaternion ℚ).imI = 0 := by
    rw [← Quaternion.coe_intCast, Quaternion.imI_coe]
  have hn_J : (n : Quaternion ℚ).imJ = 0 := by
    rw [← Quaternion.coe_intCast, Quaternion.imJ_coe]
  have hn_K : (n : Quaternion ℚ).imK = 0 := by
    rw [← Quaternion.coe_intCast, Quaternion.imK_coe]
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, hn_re, hn_I, hn_J, hn_K]
  all_goals ring

private theorem intCast_mul_j (n : ℤ) :
    ((n : Quaternion ℚ)) * (⟨0, 0, 1, 0⟩ : Quaternion ℚ) =
      (⟨0, 0, (n : ℚ), 0⟩ : Quaternion ℚ) := by
  have hn_re : (n : Quaternion ℚ).re = (n : ℚ) := by
    rw [← Quaternion.coe_intCast, Quaternion.re_coe]
  have hn_I : (n : Quaternion ℚ).imI = 0 := by
    rw [← Quaternion.coe_intCast, Quaternion.imI_coe]
  have hn_J : (n : Quaternion ℚ).imJ = 0 := by
    rw [← Quaternion.coe_intCast, Quaternion.imJ_coe]
  have hn_K : (n : Quaternion ℚ).imK = 0 := by
    rw [← Quaternion.coe_intCast, Quaternion.imK_coe]
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, hn_re, hn_I, hn_J, hn_K]
  all_goals ring

private theorem intCast_mul_k (n : ℤ) :
    ((n : Quaternion ℚ)) * (⟨0, 0, 0, 1⟩ : Quaternion ℚ) =
      (⟨0, 0, 0, (n : ℚ)⟩ : Quaternion ℚ) := by
  have hn_re : (n : Quaternion ℚ).re = (n : ℚ) := by
    rw [← Quaternion.coe_intCast, Quaternion.re_coe]
  have hn_I : (n : Quaternion ℚ).imI = 0 := by
    rw [← Quaternion.coe_intCast, Quaternion.imI_coe]
  have hn_J : (n : Quaternion ℚ).imJ = 0 := by
    rw [← Quaternion.coe_intCast, Quaternion.imJ_coe]
  have hn_K : (n : Quaternion ℚ).imK = 0 := by
    rw [← Quaternion.coe_intCast, Quaternion.imK_coe]
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, hn_re, hn_I, hn_J, hn_K]
  all_goals ring

private theorem singleton_one (ℓ : ℕ) :
    ∃ V : Fin 1 → Quaternion ℚ, (∀ t, IsHurwitz (V t)) ∧
      ∑ t, (V t) ^ ℓ = 1 := by
  refine ⟨fun _ => 1, fun _ => hurwitz_one, ?_⟩
  rw [Fin.sum_univ_one]
  exact one_pow ℓ

private theorem singleton_unit (u : Quaternion ℚ) (ℓ : ℕ)
    (hmod : ℓ % 3 = 1 ∨ ℓ % 3 = 2) (h3 : u ^ 3 = 1)
    (hu : IsHurwitz u) (hu2 : IsHurwitz (u ^ 2)) :
    ∃ V : Fin 1 → Quaternion ℚ, (∀ t, IsHurwitz (V t)) ∧
      ∑ t, (V t) ^ ℓ = u := by
  refine ⟨fun _ => u ^ ℓ, fun _ => hurwitz_pow_ell u ℓ hmod h3 hu hu2, ?_⟩
  rw [Fin.sum_univ_one]
  exact pow_ell_twice u ℓ hmod h3

private theorem waring_neg_one (ℓ : ℕ)
    (hmod : ℓ % 3 = 1 ∨ ℓ % 3 = 2) :
    ∃ V : Fin 2 → Quaternion ℚ, (∀ t, IsHurwitz (V t)) ∧
      ∑ t, (V t) ^ ℓ = -1 := by
  obtain ⟨V₁, hV₁, e₁⟩ := singleton_unit _ ℓ hmod pow3_uA hurwitz_uA hurwitz_sq_uA
  obtain ⟨V₂, hV₂, e₂⟩ := singleton_unit _ ℓ hmod pow3_uA2 hurwitz_uA2 hurwitz_sq_uA2
  obtain ⟨V, hV, esum⟩ := sum_combine_pow V₁ V₂ IsHurwitz ℓ hV₁ hV₂
  refine ⟨V, hV, ?_⟩
  rw [esum, e₁, e₂, ← neg_one_eq]

private theorem waring_i (ℓ : ℕ) (hmod : ℓ % 3 = 1 ∨ ℓ % 3 = 2) :
    ∃ V : Fin 3 → Quaternion ℚ, (∀ t, IsHurwitz (V t)) ∧
      ∑ t, (V t) ^ ℓ = (⟨0, 1, 0, 0⟩ : Quaternion ℚ) := by
  obtain ⟨V₁, hV₁, e₁⟩ := singleton_one ℓ
  obtain ⟨V₂, hV₂, e₂⟩ := singleton_unit _ ℓ hmod pow3_uA hurwitz_uA hurwitz_sq_uA
  obtain ⟨V₃, hV₃, e₃⟩ := singleton_unit _ ℓ hmod pow3_uB hurwitz_uB hurwitz_sq_uB
  obtain ⟨V₁₂, h₁₂, esum₁₂⟩ := sum_combine_pow V₁ V₂ IsHurwitz ℓ hV₁ hV₂
  obtain ⟨V, hV, esum⟩ := sum_combine_pow V₁₂ V₃ IsHurwitz ℓ h₁₂ hV₃
  refine ⟨V, hV, ?_⟩
  rw [esum, esum₁₂, e₁, e₂, e₃, ← i_pos_eq]

private theorem waring_neg_i (ℓ : ℕ) (hmod : ℓ % 3 = 1 ∨ ℓ % 3 = 2) :
    ∃ V : Fin 3 → Quaternion ℚ, (∀ t, IsHurwitz (V t)) ∧
      ∑ t, (V t) ^ ℓ = -((⟨0, 1, 0, 0⟩ : Quaternion ℚ)) := by
  obtain ⟨V₁, hV₁, e₁⟩ := singleton_one ℓ
  obtain ⟨V₂, hV₂, e₂⟩ := singleton_unit _ ℓ hmod pow3_uC hurwitz_uC hurwitz_sq_uC
  obtain ⟨V₃, hV₃, e₃⟩ := singleton_unit _ ℓ hmod pow3_uA2 hurwitz_uA2 hurwitz_sq_uA2
  obtain ⟨V₁₂, h₁₂, esum₁₂⟩ := sum_combine_pow V₁ V₂ IsHurwitz ℓ hV₁ hV₂
  obtain ⟨V, hV, esum⟩ := sum_combine_pow V₁₂ V₃ IsHurwitz ℓ h₁₂ hV₃
  refine ⟨V, hV, ?_⟩
  rw [esum, esum₁₂, e₁, e₂, e₃, ← i_neg_eq]

private theorem waring_j (ℓ : ℕ) (hmod : ℓ % 3 = 1 ∨ ℓ % 3 = 2) :
    ∃ V : Fin 3 → Quaternion ℚ, (∀ t, IsHurwitz (V t)) ∧
      ∑ t, (V t) ^ ℓ = (⟨0, 0, 1, 0⟩ : Quaternion ℚ) := by
  obtain ⟨V₁, hV₁, e₁⟩ := singleton_one ℓ
  obtain ⟨V₂, hV₂, e₂⟩ := singleton_unit _ ℓ hmod pow3_uA hurwitz_uA hurwitz_sq_uA
  obtain ⟨V₃, hV₃, e₃⟩ := singleton_unit _ ℓ hmod pow3_uD hurwitz_uD hurwitz_sq_uD
  obtain ⟨V₁₂, h₁₂, esum₁₂⟩ := sum_combine_pow V₁ V₂ IsHurwitz ℓ hV₁ hV₂
  obtain ⟨V, hV, esum⟩ := sum_combine_pow V₁₂ V₃ IsHurwitz ℓ h₁₂ hV₃
  refine ⟨V, hV, ?_⟩
  rw [esum, esum₁₂, e₁, e₂, e₃, ← j_pos_eq]

private theorem waring_neg_j (ℓ : ℕ) (hmod : ℓ % 3 = 1 ∨ ℓ % 3 = 2) :
    ∃ V : Fin 3 → Quaternion ℚ, (∀ t, IsHurwitz (V t)) ∧
      ∑ t, (V t) ^ ℓ = -((⟨0, 0, 1, 0⟩ : Quaternion ℚ)) := by
  obtain ⟨V₁, hV₁, e₁⟩ := singleton_one ℓ
  obtain ⟨V₂, hV₂, e₂⟩ := singleton_unit _ ℓ hmod pow3_uE hurwitz_uE hurwitz_sq_uE
  obtain ⟨V₃, hV₃, e₃⟩ := singleton_unit _ ℓ hmod pow3_uA2 hurwitz_uA2 hurwitz_sq_uA2
  obtain ⟨V₁₂, h₁₂, esum₁₂⟩ := sum_combine_pow V₁ V₂ IsHurwitz ℓ hV₁ hV₂
  obtain ⟨V, hV, esum⟩ := sum_combine_pow V₁₂ V₃ IsHurwitz ℓ h₁₂ hV₃
  refine ⟨V, hV, ?_⟩
  rw [esum, esum₁₂, e₁, e₂, e₃, ← j_neg_eq]

private theorem waring_k (ℓ : ℕ) (hmod : ℓ % 3 = 1 ∨ ℓ % 3 = 2) :
    ∃ V : Fin 3 → Quaternion ℚ, (∀ t, IsHurwitz (V t)) ∧
      ∑ t, (V t) ^ ℓ = (⟨0, 0, 0, 1⟩ : Quaternion ℚ) := by
  obtain ⟨V₁, hV₁, e₁⟩ := singleton_one ℓ
  obtain ⟨V₂, hV₂, e₂⟩ := singleton_unit _ ℓ hmod pow3_uC hurwitz_uC hurwitz_sq_uC
  obtain ⟨V₃, hV₃, e₃⟩ := singleton_unit _ ℓ hmod pow3_uE hurwitz_uE hurwitz_sq_uE
  obtain ⟨V₁₂, h₁₂, esum₁₂⟩ := sum_combine_pow V₁ V₂ IsHurwitz ℓ hV₁ hV₂
  obtain ⟨V, hV, esum⟩ := sum_combine_pow V₁₂ V₃ IsHurwitz ℓ h₁₂ hV₃
  refine ⟨V, hV, ?_⟩
  rw [esum, esum₁₂, e₁, e₂, e₃, ← k_pos_eq]

private theorem waring_neg_k (ℓ : ℕ) (hmod : ℓ % 3 = 1 ∨ ℓ % 3 = 2) :
    ∃ V : Fin 3 → Quaternion ℚ, (∀ t, IsHurwitz (V t)) ∧
      ∑ t, (V t) ^ ℓ = -((⟨0, 0, 0, 1⟩ : Quaternion ℚ)) := by
  obtain ⟨V₁, hV₁, e₁⟩ := singleton_one ℓ
  obtain ⟨V₂, hV₂, e₂⟩ := singleton_unit _ ℓ hmod pow3_uB hurwitz_uB hurwitz_sq_uB
  obtain ⟨V₃, hV₃, e₃⟩ := singleton_unit _ ℓ hmod pow3_uD hurwitz_uD hurwitz_sq_uD
  obtain ⟨V₁₂, h₁₂, esum₁₂⟩ := sum_combine_pow V₁ V₂ IsHurwitz ℓ hV₁ hV₂
  obtain ⟨V, hV, esum⟩ := sum_combine_pow V₁₂ V₃ IsHurwitz ℓ h₁₂ hV₃
  refine ⟨V, hV, ?_⟩
  rw [esum, esum₁₂, e₁, e₂, e₃, ← k_neg_eq]

private theorem waring_omega (ℓ : ℕ) (hmod : ℓ % 3 = 1 ∨ ℓ % 3 = 2) :
    ∃ V : Fin 2 → Quaternion ℚ, (∀ t, IsHurwitz (V t)) ∧
      ∑ t, (V t) ^ ℓ = (⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩ : Quaternion ℚ) := by
  obtain ⟨V₁, hV₁, e₁⟩ := singleton_one ℓ
  obtain ⟨V₂, hV₂, e₂⟩ := singleton_unit _ ℓ hmod pow3_uA hurwitz_uA hurwitz_sq_uA
  obtain ⟨V, hV, esum⟩ := sum_combine_pow V₁ V₂ IsHurwitz ℓ hV₁ hV₂
  refine ⟨V, hV, ?_⟩
  rw [esum, e₁, e₂, ← w0_pos_eq]

private theorem scale_sum {K : ℕ} (V : Fin K → Quaternion ℚ)
    (e : Quaternion ℚ) (ℓ : ℕ) (x : ℤ)
    (he : ∑ t, (V t) ^ ℓ = e) :
    ∑ t, (((x : Quaternion ℚ) * V t) ^ ℓ) =
      (((x ^ ℓ : ℤ)) : Quaternion ℚ) * e := by
  have hcomm : ∀ t, Commute (x : Quaternion ℚ) (V t) := by
    intro t
    have heq : (x : Quaternion ℚ) = (((x : ℚ)) : Quaternion ℚ) :=
      (Quaternion.coe_intCast x).symm
    rw [heq]
    exact Quaternion.coe_commute _ _
  have hterm : ∀ t, (((x : Quaternion ℚ) * V t) ^ ℓ) =
      (((x ^ ℓ : ℤ)) : Quaternion ℚ) * (V t) ^ ℓ := by
    intro t
    rw [(hcomm t).mul_pow]
    congr 1
    norm_cast
  calc ∑ t, (((x : Quaternion ℚ) * V t) ^ ℓ)
      = ∑ t, (((x ^ ℓ : ℤ)) : Quaternion ℚ) * (V t) ^ ℓ :=
        Finset.sum_congr rfl (fun t _ => hterm t)
    _ = (((x ^ ℓ : ℤ)) : Quaternion ℚ) * ∑ t, (V t) ^ ℓ := by
        rw [← Finset.mul_sum]
    _ = (((x ^ ℓ : ℤ)) : Quaternion ℚ) * e := by rw [he]

private theorem coord_waring (ℓ B K₁ K₂ : ℕ)
    (e : Quaternion ℚ) (N : ℤ)
    (V₁ : Fin K₁ → Quaternion ℚ) (V₂ : Fin K₂ → Quaternion ℚ)
    (hV₁ : ∀ t, IsHurwitz (V₁ t)) (hV₂ : ∀ t, IsHurwitz (V₂ t))
    (e₁ : ∑ t, (V₁ t) ^ ℓ = e) (e₂ : ∑ t, (V₂ t) ^ ℓ = -e)
    (hK₁ : K₁ ≤ 3) (hK₂ : K₂ ≤ 3)
    (p q : ℕ) (x : Fin p → ℤ) (y : Fin q → ℤ)
    (hB : p + q ≤ B) (hN : N = ∑ i, (x i) ^ ℓ - ∑ i, (y i) ^ ℓ) :
    ∃ n : ℕ, n ≤ 3 * B ∧ ∃ H : Fin n → Quaternion ℚ,
      (∀ t, IsHurwitz (H t)) ∧ ∑ i, (H i) ^ ℓ = ((N : Quaternion ℚ)) * e := by
  obtain ⟨Hp, hHp, hHpS⟩ := sum_kpiece_pow
    (s := fun _ : Fin p => K₁)
    (fun a t => ((x a : ℤ) : Quaternion ℚ) * V₁ t)
    IsHurwitz ℓ (fun a b => hurwitz_intCast_mul _ _ (hV₁ b))
  obtain ⟨Hm, hHm, hHmS⟩ := sum_kpiece_pow
    (s := fun _ : Fin q => K₂)
    (fun b t => ((y b : ℤ) : Quaternion ℚ) * V₂ t)
    IsHurwitz ℓ (fun b t => hurwitz_intCast_mul _ _ (hV₂ t))
  obtain ⟨H, hH, hHS⟩ := sum_combine_pow Hp Hm IsHurwitz ℓ hHp hHm
  have hpos : (∑ a, ∑ b, ((((x a : ℤ) : Quaternion ℚ) * V₁ b) ^ ℓ)) =
      ((((∑ a, (x a) ^ ℓ : ℤ))) : Quaternion ℚ) * e := by
    have h1 : ∀ a : Fin p, (∑ b, ((((x a : ℤ) : Quaternion ℚ) * V₁ b) ^ ℓ)) =
        ((((x a ^ ℓ : ℤ))) : Quaternion ℚ) * e := fun a => scale_sum V₁ e ℓ _ e₁
    calc ∑ a, ∑ b, ((((x a : ℤ) : Quaternion ℚ) * V₁ b) ^ ℓ)
        = ∑ a, ((((x a ^ ℓ : ℤ))) : Quaternion ℚ) * e :=
          Finset.sum_congr rfl (fun a _ => h1 a)
      _ = (∑ a, ((((x a ^ ℓ : ℤ))) : Quaternion ℚ)) * e := by
          rw [← Finset.sum_mul]
      _ = ((((∑ a, (x a) ^ ℓ : ℤ))) : Quaternion ℚ) * e := by
          congr 1
          norm_cast
  have hneg : (∑ b, ∑ t, ((((y b : ℤ) : Quaternion ℚ) * V₂ t) ^ ℓ)) =
      ((((∑ b, (y b) ^ ℓ : ℤ))) : Quaternion ℚ) * (-e) := by
    have h1 : ∀ b : Fin q, (∑ t, ((((y b : ℤ) : Quaternion ℚ) * V₂ t) ^ ℓ)) =
        ((((y b ^ ℓ : ℤ))) : Quaternion ℚ) * (-e) := fun b => scale_sum V₂ _ ℓ _ e₂
    calc ∑ b, ∑ t, ((((y b : ℤ) : Quaternion ℚ) * V₂ t) ^ ℓ)
        = ∑ b, ((((y b ^ ℓ : ℤ))) : Quaternion ℚ) * (-e) :=
          Finset.sum_congr rfl (fun b _ => h1 b)
      _ = (∑ b, ((((y b ^ ℓ : ℤ))) : Quaternion ℚ)) * (-e) := by
          rw [← Finset.sum_mul]
      _ = ((((∑ b, (y b) ^ ℓ : ℤ))) : Quaternion ℚ) * (-e) := by
          congr 1
          norm_cast
  have hP : ∑ i, (Hp i) ^ ℓ = ((((∑ a, (x a) ^ ℓ : ℤ))) : Quaternion ℚ) * e := by
    rw [hHpS]
    exact hpos
  have hQ : ∑ i, (Hm i) ^ ℓ =
      ((((∑ b, (y b) ^ ℓ : ℤ))) : Quaternion ℚ) * (-e) := by
    rw [hHmS]
    exact hneg
  have hfinal : ∑ i, (H i) ^ ℓ = ((N : Quaternion ℚ)) * e := by
    rw [hHS, hP, hQ, mul_neg, ← sub_eq_add_neg, ← sub_mul]
    congr 1
    rw [hN]
    norm_cast
  refine ⟨_, ?_, H, hH, hfinal⟩
  have hsum1 : (∑ _ : Fin p, K₁) = p * K₁ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id]
  have hsum2 : (∑ _ : Fin q, K₂) = q * K₂ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id]
  rw [hsum1, hsum2]
  calc p * K₁ + q * K₂ ≤ p * 3 + q * 3 :=
        Nat.add_le_add (Nat.mul_le_mul_left p hK₁) (Nat.mul_le_mul_left q hK₂)
    _ = 3 * (p + q) := by ring
    _ ≤ 3 * B := Nat.mul_le_mul_left 3 hB

/-! # Waring-type bound for Hurwitz quaternion integers -/

/-- **Waring's problem for Hurwitz quaternion integers.** Call a rational quaternion a Hurwitz
integer if its four coordinates are either all integers or all of the form $a + \tfrac12$ with
$a$ an integer. For every positive integer $\ell$ with $\ell \equiv 1$ or $\ell \equiv 2 \pmod 3$
there is a natural number $g$ such that every Hurwitz integer is a sum of at most $g$ $\ell$-th
powers of Hurwitz integers.

Proves `Wanted` entry `hurwitz_quaternion_waring_bound`.

Source: Janyarak Tongsomporn, Nicola Oswald, and Jörn Steuding,
"Waring's Problem for Hurwitz Quaternion Integers," Journal of Integer
Sequences 22 (2019), Article 19.8.1, Theorem (label 1), lines 127–129,
https://cs.uwaterloo.ca/journals/JIS/VOL22/Steuding/steuding6.tex
-/
theorem hurwitz_quaternion_waring_bound
    (ℓ : ℕ) (hℓpos : 0 < ℓ) (hℓmod : ℓ % 3 = 1 ∨ ℓ % 3 = 2) :
    let IsHurwitz : Quaternion ℚ → Prop := fun z =>
      (∃ a b c d : ℤ,
        z.re = (a : ℚ) ∧ z.imI = (b : ℚ) ∧ z.imJ = (c : ℚ) ∧ z.imK = (d : ℚ)) ∨
      (∃ a b c d : ℤ,
        z.re = (a : ℚ) + 1 / 2 ∧ z.imI = (b : ℚ) + 1 / 2 ∧
          z.imJ = (c : ℚ) + 1 / 2 ∧ z.imK = (d : ℚ) + 1 / 2)
    ∃ g : ℕ, ∀ z : Quaternion ℚ, IsHurwitz z →
      ∃ n : ℕ, n ≤ g ∧ ∃ q : Fin n → Quaternion ℚ,
        (∀ i, IsHurwitz (q i)) ∧ ∑ i, (q i) ^ ℓ = z := by
  change ∃ g : ℕ, ∀ z : Quaternion ℚ, IsHurwitz z →
    ∃ n : ℕ, n ≤ g ∧ ∃ q : Fin n → Quaternion ℚ,
      (∀ i, IsHurwitz (q i)) ∧ ∑ i, (q i) ^ ℓ = z
  have hℓ : 1 ≤ ℓ := by omega
  obtain ⟨B, hB⟩ := signed_waring ℓ hℓ
  obtain ⟨V1p, hV1p, e1p⟩ := singleton_one ℓ
  obtain ⟨V1m, hV1m, e1m⟩ := waring_neg_one ℓ hℓmod
  obtain ⟨Vip, hVip, eip⟩ := waring_i ℓ hℓmod
  obtain ⟨Vim, hVim, eim⟩ := waring_neg_i ℓ hℓmod
  obtain ⟨Vjp, hVjp, ejp⟩ := waring_j ℓ hℓmod
  obtain ⟨Vjm, hVjm, ejm⟩ := waring_neg_j ℓ hℓmod
  obtain ⟨Vkp, hVkp, ekp⟩ := waring_k ℓ hℓmod
  obtain ⟨Vkm, hVkm, ekm⟩ := waring_neg_k ℓ hℓmod
  obtain ⟨Vo, hVo, eo⟩ := waring_omega ℓ hℓmod
  refine ⟨12 * B + 2, ?_⟩
  intro z hz
  rcases hz with ⟨a, b, c, d, ha, hb, hc, hd⟩ | ⟨a, b, c, d, ha, hb, hc, hd⟩
  · obtain ⟨p1, q1, x1, y1, hB1, hN1⟩ := hB a
    obtain ⟨p2, q2, x2, y2, hB2, hN2⟩ := hB b
    obtain ⟨p3, q3, x3, y3, hB3, hN3⟩ := hB c
    obtain ⟨p4, q4, x4, y4, hB4, hN4⟩ := hB d
    obtain ⟨n1, hn1, H1, hH1, eH1⟩ := coord_waring ℓ B 1 2 1 a
      V1p V1m hV1p hV1m e1p e1m (by decide) (by decide) p1 q1 x1 y1 hB1 hN1
    obtain ⟨n2, hn2, H2, hH2, eH2⟩ := coord_waring ℓ B 3 3
      (⟨0, 1, 0, 0⟩ : Quaternion ℚ) b Vip Vim hVip hVim eip eim
      (by decide) (by decide) p2 q2 x2 y2 hB2 hN2
    obtain ⟨n3, hn3, H3, hH3, eH3⟩ := coord_waring ℓ B 3 3
      (⟨0, 0, 1, 0⟩ : Quaternion ℚ) c Vjp Vjm hVjp hVjm ejp ejm
      (by decide) (by decide) p3 q3 x3 y3 hB3 hN3
    obtain ⟨n4, hn4, H4, hH4, eH4⟩ := coord_waring ℓ B 3 3
      (⟨0, 0, 0, 1⟩ : Quaternion ℚ) d Vkp Vkm hVkp hVkm ekp ekm
      (by decide) (by decide) p4 q4 x4 y4 hB4 hN4
    obtain ⟨H12, hH12, eH12⟩ := sum_combine_pow H1 H2 IsHurwitz ℓ hH1 hH2
    obtain ⟨H123, hH123, eH123⟩ := sum_combine_pow H12 H3 IsHurwitz ℓ hH12 hH3
    obtain ⟨H, hH, eH⟩ := sum_combine_pow H123 H4 IsHurwitz ℓ hH123 hH4
    refine ⟨_, ?_, H, hH, ?_⟩
    · omega
    · rw [eH, eH123, eH12, eH1, eH2, eH3, eH4, mul_one, intCast_mul_i,
        intCast_mul_j, intCast_mul_k, intCast_eq_mk]
      refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
        simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
          Quaternion.imK_add]
      · rw [ha]
        ring
      · rw [hb]
        ring
      · rw [hc]
        ring
      · rw [hd]
        ring
  · obtain ⟨p1, q1, x1, y1, hB1, hN1⟩ := hB a
    obtain ⟨p2, q2, x2, y2, hB2, hN2⟩ := hB b
    obtain ⟨p3, q3, x3, y3, hB3, hN3⟩ := hB c
    obtain ⟨p4, q4, x4, y4, hB4, hN4⟩ := hB d
    obtain ⟨n1, hn1, H1, hH1, eH1⟩ := coord_waring ℓ B 1 2 1 a
      V1p V1m hV1p hV1m e1p e1m (by decide) (by decide) p1 q1 x1 y1 hB1 hN1
    obtain ⟨n2, hn2, H2, hH2, eH2⟩ := coord_waring ℓ B 3 3
      (⟨0, 1, 0, 0⟩ : Quaternion ℚ) b Vip Vim hVip hVim eip eim
      (by decide) (by decide) p2 q2 x2 y2 hB2 hN2
    obtain ⟨n3, hn3, H3, hH3, eH3⟩ := coord_waring ℓ B 3 3
      (⟨0, 0, 1, 0⟩ : Quaternion ℚ) c Vjp Vjm hVjp hVjm ejp ejm
      (by decide) (by decide) p3 q3 x3 y3 hB3 hN3
    obtain ⟨n4, hn4, H4, hH4, eH4⟩ := coord_waring ℓ B 3 3
      (⟨0, 0, 0, 1⟩ : Quaternion ℚ) d Vkp Vkm hVkp hVkm ekp ekm
      (by decide) (by decide) p4 q4 x4 y4 hB4 hN4
    obtain ⟨H12, hH12, eH12⟩ := sum_combine_pow H1 H2 IsHurwitz ℓ hH1 hH2
    obtain ⟨H123, hH123, eH123⟩ := sum_combine_pow H12 H3 IsHurwitz ℓ hH12 hH3
    obtain ⟨HL, hHL, eHL⟩ := sum_combine_pow H123 H4 IsHurwitz ℓ hH123 hH4
    obtain ⟨H, hH, eH⟩ := sum_combine_pow HL Vo IsHurwitz ℓ hHL hVo
    refine ⟨_, ?_, H, hH, ?_⟩
    · omega
    · rw [eH, eHL, eH123, eH12, eH1, eH2, eH3, eH4, eo, mul_one, intCast_mul_i,
        intCast_mul_j, intCast_mul_k, intCast_eq_mk]
      refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
        simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
          Quaternion.imK_add]
      · rw [ha]
        ring
      · rw [hb]
        ring
      · rw [hc]
        ring
      · rw [hd]
        ring

end MetaMathlibExt
end
