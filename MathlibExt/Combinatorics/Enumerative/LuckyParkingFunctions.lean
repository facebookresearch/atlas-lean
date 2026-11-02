/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

/-! # Expected lucky spots of weakly increasing parking functions
-/

private abbrev Park (n : ℕ) := { a : Fin n → Fin n // Monotone a ∧ ∀ i, (a i).val ≤ i.val }

private instance Park.decidablePred (n : ℕ) :
    DecidablePred (fun a : Fin n → Fin n => Monotone a ∧ ∀ i, (a i).val ≤ i.val) :=
  fun _ => inferInstance

private instance Park.fintype (n : ℕ) : Fintype (Park n) := Subtype.fintype _

private abbrev Marked (n : ℕ) := Σ _a : Park n, { i : Fin n // _a.1 i = i }

private instance Marked.fintype' (n : ℕ) : Fintype (Marked n) := by
  unfold Marked
  infer_instance

private lemma park_zero_val (m : ℕ) (a : Park m) (hm : 0 < m) :
    (a.1 ⟨0, hm⟩).val = 0 := by
  have h := a.2.2 ⟨0, hm⟩
  simp only at h
  omega

private lemma park_card_eq_filter (n : ℕ) :
    Fintype.card (Park n) =
      (Finset.univ.filter
        (fun a : Fin n → Fin n => Monotone a ∧ ∀ i, (a i).val ≤ i.val)).card :=
  Fintype.card_subtype _

private def markedEquivSigma (n : ℕ) :
    Marked n ≃
      ↥((Finset.univ.filter
        (fun a : Fin n → Fin n => Monotone a ∧ ∀ i, (a i).val ≤ i.val)).sigma
        (fun a => Finset.univ.filter (fun i : Fin n => a i = i))) where
  toFun x :=
    ⟨⟨x.1.1, x.2.1⟩, Finset.mem_sigma.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.1.2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2.2⟩⟩⟩
  invFun y :=
    ⟨⟨y.1.1, (Finset.mem_filter.mp (Finset.mem_sigma.mp y.2).1).2⟩,
      ⟨y.1.2, (Finset.mem_filter.mp (Finset.mem_sigma.mp y.2).2).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma marked_card_eq_sum (n : ℕ) :
    Fintype.card (Marked n) =
      ∑ a ∈ Finset.univ.filter
        (fun a : Fin n → Fin n => Monotone a ∧ ∀ i, (a i).val ≤ i.val),
        (Finset.univ.filter (fun i : Fin n => a i = i)).card := by
  have h1 := Fintype.card_congr (markedEquivSigma n)
  rw [Fintype.card_coe] at h1
  rw [h1, Finset.card_sigma]

private def splitLower (n : ℕ) (a : Fin n → Fin n) (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val)
    (i0 : Fin n) : Fin i0.val → Fin i0.val :=
  fun j => ⟨(a ⟨j.val, by omega⟩).val, by
    have h := ha.2 ⟨j.val, by omega⟩
    simp only at h ⊢
    omega⟩

private lemma splitLower_mono (n : ℕ) (a : Fin n → Fin n) (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val)
    (i0 : Fin n) : Monotone (splitLower n a ha i0) := by
  intro j k hjk
  have hjk' : j.val ≤ k.val := Fin.le_def.mp hjk
  change (splitLower n a ha i0 j).val ≤ (splitLower n a ha i0 k).val
  simp only [splitLower]
  have hmon : a ⟨j.val, by omega⟩ ≤ a ⟨k.val, by omega⟩ := by
    apply ha.1
    rw [Fin.le_def]
    simp only
    exact hjk'
  exact Fin.le_def.mp hmon

private lemma splitLower_bound (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) (i0 : Fin n)
    (j : Fin i0.val) : (splitLower n a ha i0 j).val ≤ j.val := by
  simp only [splitLower]
  have h := ha.2 ⟨j.val, by omega⟩
  simp only at h ⊢
  omega

private def splitUpper (n : ℕ) (a : Fin n → Fin n) (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val)
    (i0 : Fin n) (hi : a i0 = i0) : Fin (n - i0.val) → Fin (n - i0.val) :=
  fun k => ⟨(a ⟨i0.val + k.val, by omega⟩).val - i0.val, by
    have hmon : i0 ≤ a ⟨i0.val + k.val, by omega⟩ := by
      calc i0 = a i0 := hi.symm
        _ ≤ a ⟨i0.val + k.val, by omega⟩ := ha.1 (by rw [Fin.le_def]; simp only; omega)
    have hle : i0.val ≤ (a ⟨i0.val + k.val, by omega⟩).val := Fin.le_def.mp hmon
    have hlt : (a ⟨i0.val + k.val, by omega⟩).val < n := (a _).isLt
    omega⟩

private lemma splitUpper_mono (n : ℕ) (a : Fin n → Fin n) (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val)
    (i0 : Fin n) (hi : a i0 = i0) : Monotone (splitUpper n a ha i0 hi) := by
  intro k1 k2 hle
  have hle' : k1.val ≤ k2.val := Fin.le_def.mp hle
  change (splitUpper n a ha i0 hi k1).val ≤ (splitUpper n a ha i0 hi k2).val
  simp only [splitUpper]
  have hmon : a ⟨i0.val + k1.val, by omega⟩ ≤ a ⟨i0.val + k2.val, by omega⟩ := by
    apply ha.1
    rw [Fin.le_def]
    simp only
    omega
  have h := Fin.le_def.mp hmon
  omega

private lemma splitUpper_bound (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) (i0 : Fin n)
    (hi : a i0 = i0) (k : Fin (n - i0.val)) :
    (splitUpper n a ha i0 hi k).val ≤ k.val := by
  simp only [splitUpper]
  have h := ha.2 ⟨i0.val + k.val, by omega⟩
  simp only at h ⊢
  omega

private def joinFun (n : ℕ) (i0 : Fin n) (l : Park i0.val)
    (u : Park (n - i0.val)) : Fin n → Fin n :=
  fun j =>
    if h : j.val < i0.val then
      ⟨(l.1 ⟨j.val, h⟩).val, by
        have h1 := (l.1 ⟨j.val, h⟩).isLt
        have h2 := i0.isLt
        omega⟩
    else
      ⟨(u.1 ⟨j.val - i0.val, by
        have hj := j.isLt
        have hi := i0.isLt
        omega⟩).val + i0.val, by
        have h1 := (u.1 ⟨j.val - i0.val, by
          have hj := j.isLt
          have hi := i0.isLt
          omega⟩).isLt
        have hi := i0.isLt
        omega⟩

private lemma joinFun_val_of_lt (n : ℕ) (i0 : Fin n) (l : Park i0.val)
    (u : Park (n - i0.val)) (j : Fin n) (h : j.val < i0.val) :
    (joinFun n i0 l u j).val = (l.1 ⟨j.val, h⟩).val := by
  simp only [joinFun, dite_eq_left h]

private lemma joinFun_val_of_ge (n : ℕ) (i0 : Fin n) (l : Park i0.val)
    (u : Park (n - i0.val)) (j : Fin n) (h : ¬ j.val < i0.val) :
    (joinFun n i0 l u j).val =
      (u.1 ⟨j.val - i0.val, by
        have _hj := j.isLt
        have _hi := i0.isLt
        omega⟩).val + i0.val := by
  simp only [joinFun, dite_eq_right h]

private lemma joinFun_mono (n : ℕ) (i0 : Fin n) (l : Park i0.val)
    (u : Park (n - i0.val)) : Monotone (joinFun n i0 l u) := by
  intro j1 j2 hle
  have hle' : j1.val ≤ j2.val := Fin.le_def.mp hle
  by_cases h1 : j1.val < i0.val
  · by_cases h2 : j2.val < i0.val
    · rw [Fin.le_def]
      rw [joinFun_val_of_lt n i0 l u j1 h1]
      rw [joinFun_val_of_lt n i0 l u j2 h2]
      have hmon : l.1 ⟨j1.val, h1⟩ ≤ l.1 ⟨j2.val, h2⟩ := by
        apply l.2.1
        rw [Fin.le_def]
        simp only
        omega
      exact Fin.le_def.mp hmon
    · rw [Fin.le_def]
      rw [joinFun_val_of_lt n i0 l u j1 h1]
      rw [joinFun_val_of_ge n i0 l u j2 h2]
      have hlt : (l.1 ⟨j1.val, h1⟩).val < i0.val :=
        (l.1 ⟨j1.val, h1⟩).isLt
      omega
  · by_cases h2 : j2.val < i0.val
    · have hcon : j1.val < i0.val := lt_of_le_of_lt hle' h2
      exact absurd hcon h1
    · rw [Fin.le_def]
      rw [joinFun_val_of_ge n i0 l u j1 h1]
      rw [joinFun_val_of_ge n i0 l u j2 h2]
      have hle_sub : j1.val - i0.val ≤ j2.val - i0.val := by
        omega
      have hmon :
          u.1 ⟨j1.val - i0.val, by
            have _hj := j1.isLt
            have _hi := i0.isLt
            omega⟩ ≤
          u.1 ⟨j2.val - i0.val, by
            have _hj := j2.isLt
            have _hi := i0.isLt
            omega⟩ := by
        apply u.2.1
        rw [Fin.le_def]
        simp only
        exact hle_sub
      have h := Fin.le_def.mp hmon
      omega

private lemma joinFun_bound (n : ℕ) (i0 : Fin n) (l : Park i0.val)
    (u : Park (n - i0.val)) (j : Fin n) :
    (joinFun n i0 l u j).val ≤ j.val := by
  by_cases h : j.val < i0.val
  · rw [joinFun_val_of_lt n i0 l u j h]
    have hb := l.2.2 ⟨j.val, h⟩
    simp only at hb
    exact hb
  · rw [joinFun_val_of_ge n i0 l u j h]
    have hb := u.2.2 ⟨j.val - i0.val, by
      have _hj := j.isLt
      have _hi := i0.isLt
      omega⟩
    simp only at hb
    omega

private lemma joinFun_fixed (n : ℕ) (i0 : Fin n) (l : Park i0.val)
    (u : Park (n - i0.val)) : joinFun n i0 l u i0 = i0 := by
  have hneg : ¬ i0.val < i0.val := lt_irrefl _
  have hval := joinFun_val_of_ge n i0 l u i0 hneg
  have hpos : 0 < n - i0.val := by
    have _hi := i0.isLt
    omega
  have heq :
      (⟨i0.val - i0.val, by
        have _hj := i0.isLt
        have _hi := i0.isLt
        omega⟩ : Fin (n - i0.val)) =
        ⟨0, hpos⟩ := by
    apply Fin.ext
    simp only
    omega
  have hzero := park_zero_val (n - i0.val) u hpos
  apply Fin.ext
  rw [hval, heq, hzero]
  omega

private abbrev Fiber (n : ℕ) (i0 : Fin n) := { a : Park n // a.1 i0 = i0 }

private instance Fiber.fintype (n : ℕ) (i0 : Fin n) : Fintype (Fiber n i0) := by
  unfold Fiber
  infer_instance

private def fiberToProd (n : ℕ) (i0 : Fin n) (x : Fiber n i0) :
    Park i0.val × Park (n - i0.val) :=
  (⟨splitLower n x.1.1 x.1.2 i0, splitLower_mono n x.1.1 x.1.2 i0,
      fun j => splitLower_bound n x.1.1 x.1.2 i0 j⟩,
    ⟨splitUpper n x.1.1 x.1.2 i0 x.2,
      splitUpper_mono n x.1.1 x.1.2 i0 x.2,
      fun k => splitUpper_bound n x.1.1 x.1.2 i0 x.2 k⟩)

private def fiberFromProd (n : ℕ) (i0 : Fin n)
    (p : Park i0.val × Park (n - i0.val)) : Fiber n i0 :=
  ⟨⟨joinFun n i0 p.1 p.2, joinFun_mono n i0 p.1 p.2,
      fun j => joinFun_bound n i0 p.1 p.2 j⟩,
    joinFun_fixed n i0 p.1 p.2⟩

private lemma fiber_ge_le (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) (i0 : Fin n)
    (hi : a i0 = i0) (j : Fin n) (hle : i0.val ≤ j.val) :
    i0.val ≤ (a j).val := by
  have hij : i0 ≤ j := Fin.le_def.mpr hle
  have hmon : a i0 ≤ a j := ha.1 hij
  have hle2 : i0 ≤ a j := hi ▸ hmon
  exact Fin.le_def.mp hle2

private lemma fiber_left_inv (n : ℕ) (i0 : Fin n) (x : Fiber n i0) :
    fiberFromProd n i0 (fiberToProd n i0 x) = x := by
  obtain ⟨⟨a, ha⟩, hi⟩ := x
  apply Subtype.ext
  apply Subtype.ext
  funext j
  apply Fin.ext
  simp only [fiberFromProd, fiberToProd]
  by_cases h : j.val < i0.val
  · have hJ := joinFun_val_of_lt n i0 (fiberToProd n i0 ⟨⟨a, ha⟩, hi⟩).1
      (fiberToProd n i0 ⟨⟨a, ha⟩, hi⟩).2 j h
    simp only [fiberToProd, splitLower] at hJ
    exact hJ
  · have hJ := joinFun_val_of_ge n i0 (fiberToProd n i0 ⟨⟨a, ha⟩, hi⟩).1
      (fiberToProd n i0 ⟨⟨a, ha⟩, hi⟩).2 j h
    simp only [fiberToProd, splitUpper] at hJ
    rw [hJ]
    have hle : i0.val ≤ j.val := by
      omega
    have heq :
        ∀ h' : i0.val + (j.val - i0.val) < n,
          (⟨i0.val + (j.val - i0.val), h'⟩ : Fin n) = j := by
      intro _
      apply Fin.ext
      simp only
      omega
    rw [heq _]
    have hle2 := fiber_ge_le n a ha i0 hi j hle
    omega

private lemma fiber_right_inv (n : ℕ) (i0 : Fin n)
    (p : Park i0.val × Park (n - i0.val)) :
    fiberToProd n i0 (fiberFromProd n i0 p) = p := by
  obtain ⟨l, u⟩ := p
  apply Prod.ext
  · apply Subtype.ext
    funext j
    apply Fin.ext
    simp only [fiberToProd, fiberFromProd, splitLower]
    have h : (⟨j.val, by omega⟩ : Fin n).val < i0.val := j.isLt
    have hJ := joinFun_val_of_lt n i0 l u ⟨j.val, by omega⟩ h
    exact hJ
  · apply Subtype.ext
    funext k
    apply Fin.ext
    simp only [fiberToProd, fiberFromProd, splitUpper]
    have hneg : ¬ (⟨i0.val + k.val, by omega⟩ : Fin n).val < i0.val := by
      simp only
      omega
    have hJ := joinFun_val_of_ge n i0 l u ⟨i0.val + k.val, by omega⟩ hneg
    rw [hJ]
    have heq :
        ∀ h' : (i0.val + k.val) - i0.val < n - i0.val,
          (⟨(i0.val + k.val) - i0.val, h'⟩ : Fin (n - i0.val)) = k := by
      intro _
      apply Fin.ext
      simp only
      omega
    rw [heq _]
    omega

private def fiberEquiv (n : ℕ) (i0 : Fin n) :
    Fiber n i0 ≃ Park i0.val × Park (n - i0.val) where
  toFun := fiberToProd n i0
  invFun := fiberFromProd n i0
  left_inv := fiber_left_inv n i0
  right_inv := fiber_right_inv n i0

private def markedFiberEquiv (n : ℕ) :
    Marked n ≃ Σ i0 : Fin n, Fiber n i0 where
  toFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  invFun y := ⟨y.2.1, ⟨y.1, y.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma marked_card_eq_fiber_sum (n : ℕ) :
    Fintype.card (Marked n) =
      ∑ i0 : Fin n,
        Fintype.card (Park i0.val) * Fintype.card (Park (n - i0.val)) := by
  have h1 := Fintype.card_congr (markedFiberEquiv n)
  rw [h1, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i0 _
  have h2 := Fintype.card_congr (fiberEquiv n i0)
  rw [h2, Fintype.card_prod]

private def plainFun (n : ℕ) (a : Fin n → Fin n) :
    Fin (n + 1) → Fin (n + 1) :=
  fun k =>
    if h : k.val = 0 then ⟨0, by omega⟩
    else
      ⟨(a ⟨k.val - 1, by omega⟩).val, by
        have _h1 := (a ⟨k.val - 1, by omega⟩).isLt
        omega⟩

private lemma plainFun_val_of_zero (n : ℕ) (a : Fin n → Fin n)
    (k : Fin (n + 1)) (h : k.val = 0) :
    (plainFun n a k).val = 0 := by
  simp only [plainFun, dite_eq_left h]

private lemma plainFun_val_of_ne (n : ℕ) (a : Fin n → Fin n)
    (k : Fin (n + 1)) (h : ¬ k.val = 0) :
    (plainFun n a k).val = (a ⟨k.val - 1, by omega⟩).val := by
  simp only [plainFun, dite_eq_right h]

private lemma plainFun_mono (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) :
    Monotone (plainFun n a) := by
  intro k1 k2 hle
  have hle' : k1.val ≤ k2.val := Fin.le_def.mp hle
  by_cases h1 : k1.val = 0
  · rw [Fin.le_def, plainFun_val_of_zero n a k1 h1]
    exact Nat.zero_le _
  · by_cases h2 : k2.val = 0
    · have hcon : k1.val = 0 := by
        omega
      exact absurd hcon h1
    · rw [Fin.le_def]
      rw [plainFun_val_of_ne n a k1 h1]
      rw [plainFun_val_of_ne n a k2 h2]
      have hmon : a ⟨k1.val - 1, by omega⟩ ≤ a ⟨k2.val - 1, by omega⟩ := by
        apply ha.1
        rw [Fin.le_def]
        simp only
        omega
      exact Fin.le_def.mp hmon

private lemma plainFun_bound (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) (k : Fin (n + 1)) :
    (plainFun n a k).val ≤ k.val := by
  by_cases h : k.val = 0
  · rw [plainFun_val_of_zero n a k h]
    omega
  · rw [plainFun_val_of_ne n a k h]
    have hb := ha.2 ⟨k.val - 1, by omega⟩
    simp only at hb
    omega

private def embedPlain (n : ℕ) (a : Park n) : Park (n + 1) :=
  ⟨plainFun n a.1, plainFun_mono n a.1 a.2,
    fun k => plainFun_bound n a.1 a.2 k⟩

private lemma plain_no_fixed (n : ℕ) (a : Park n) (k : Fin (n + 1))
    (hpos : 0 < k.val) : (embedPlain n a).1 k ≠ k := by
  intro heq
  have hval : ((embedPlain n a).1 k).val = k.val := congrArg Fin.val heq
  have hne : k.val ≠ 0 := by
    omega
  have hB := plainFun_val_of_ne n a.1 k hne
  have hb := a.2.2 ⟨k.val - 1, by omega⟩
  simp only [embedPlain] at hval hB
  simp only at hb
  omega

private def markedFun (n : ℕ) (a : Fin n → Fin n) (i0 : Fin n) :
    Fin (n + 1) → Fin (n + 1) :=
  fun k =>
    if h0 : k.val = 0 then ⟨0, by omega⟩
    else if h1 : k.val - 1 < i0.val then
      ⟨(a ⟨k.val - 1, by omega⟩).val, by
        have _h1 := (a ⟨k.val - 1, by omega⟩).isLt
        omega⟩
    else
      ⟨(a ⟨k.val - 1, by omega⟩).val + 1, by
        have _h1 := (a ⟨k.val - 1, by omega⟩).isLt
        omega⟩

private lemma markedFun_val_of_zero (n : ℕ) (a : Fin n → Fin n)
    (i0 : Fin n) (k : Fin (n + 1)) (h : k.val = 0) :
    (markedFun n a i0 k).val = 0 := by
  simp only [markedFun, dite_eq_left h]

private lemma markedFun_val_of_lt (n : ℕ) (a : Fin n → Fin n)
    (i0 : Fin n) (k : Fin (n + 1)) (h0 : ¬ k.val = 0)
    (h1 : k.val - 1 < i0.val) :
    (markedFun n a i0 k).val = (a ⟨k.val - 1, by omega⟩).val := by
  simp only [markedFun, dite_eq_right h0, dite_eq_left h1]

private lemma markedFun_val_of_ge (n : ℕ) (a : Fin n → Fin n)
    (i0 : Fin n) (k : Fin (n + 1)) (h0 : ¬ k.val = 0)
    (h1 : ¬ k.val - 1 < i0.val) :
    (markedFun n a i0 k).val =
      (a ⟨k.val - 1, by omega⟩).val + 1 := by
  simp only [markedFun, dite_eq_right h0, dite_eq_right h1]

private lemma markedFun_mono (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) (i0 : Fin n) :
    Monotone (markedFun n a i0) := by
  intro k1 k2 hle
  have hle' : k1.val ≤ k2.val := Fin.le_def.mp hle
  by_cases h10 : k1.val = 0
  · rw [Fin.le_def, markedFun_val_of_zero n a i0 k1 h10]
    exact Nat.zero_le _
  · by_cases h20 : k2.val = 0
    · have hcon : k1.val = 0 := by
        omega
      exact absurd hcon h10
    · by_cases h11 : k1.val - 1 < i0.val
      · by_cases h21 : k2.val - 1 < i0.val
        · rw [Fin.le_def]
          rw [markedFun_val_of_lt n a i0 k1 h10 h11]
          rw [markedFun_val_of_lt n a i0 k2 h20 h21]
          have hmon :
              a ⟨k1.val - 1, by omega⟩ ≤ a ⟨k2.val - 1, by omega⟩ := by
            apply ha.1
            rw [Fin.le_def]
            simp only
            omega
          exact Fin.le_def.mp hmon
        · rw [Fin.le_def]
          rw [markedFun_val_of_lt n a i0 k1 h10 h11]
          rw [markedFun_val_of_ge n a i0 k2 h20 h21]
          have hmon :
              a ⟨k1.val - 1, by omega⟩ ≤ a ⟨k2.val - 1, by omega⟩ := by
            apply ha.1
            rw [Fin.le_def]
            simp only
            omega
          have h := Fin.le_def.mp hmon
          omega
      · by_cases h21 : k2.val - 1 < i0.val
        · have hcon : k1.val - 1 < i0.val := by
            omega
          exact absurd hcon h11
        · rw [Fin.le_def]
          rw [markedFun_val_of_ge n a i0 k1 h10 h11]
          rw [markedFun_val_of_ge n a i0 k2 h20 h21]
          have hmon :
              a ⟨k1.val - 1, by omega⟩ ≤ a ⟨k2.val - 1, by omega⟩ := by
            apply ha.1
            rw [Fin.le_def]
            simp only
            omega
          have h := Fin.le_def.mp hmon
          omega

private lemma markedFun_bound (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) (i0 : Fin n)
    (k : Fin (n + 1)) : (markedFun n a i0 k).val ≤ k.val := by
  by_cases h0 : k.val = 0
  · rw [markedFun_val_of_zero n a i0 k h0]
    omega
  · by_cases h1 : k.val - 1 < i0.val
    · rw [markedFun_val_of_lt n a i0 k h0 h1]
      have hb := ha.2 ⟨k.val - 1, by omega⟩
      simp only at hb
      omega
    · rw [markedFun_val_of_ge n a i0 k h0 h1]
      have hb := ha.2 ⟨k.val - 1, by omega⟩
      simp only at hb
      omega

private def embedMarked (n : ℕ) (m : Marked n) : Park (n + 1) :=
  ⟨markedFun n m.1.1 m.2.1, markedFun_mono n m.1.1 m.1.2 m.2.1,
    fun k => markedFun_bound n m.1.1 m.1.2 m.2.1 k⟩

private lemma marked_fixed (n : ℕ) (m : Marked n) :
    (embedMarked n m).1 ⟨m.2.1.val + 1, by omega⟩ =
      ⟨m.2.1.val + 1, by omega⟩ := by
  obtain ⟨⟨a, ha⟩, ⟨i0, hi⟩⟩ := m
  apply Fin.ext
  have h0 : ¬ (⟨i0.val + 1, by omega⟩ : Fin (n + 1)).val = 0 := by
    simp only
    omega
  have h1 :
      ¬ (⟨i0.val + 1, by omega⟩ : Fin (n + 1)).val - 1 < i0.val := by
    simp only
    omega
  have hB := markedFun_val_of_ge n a i0 ⟨i0.val + 1, by omega⟩ h0 h1
  simp only [embedMarked] at hB ⊢
  rw [hB]
  have heq :
      ∀ h' : (⟨i0.val + 1, by omega⟩ : Fin (n + 1)).val - 1 < n,
        (⟨(⟨i0.val + 1, by omega⟩ : Fin (n + 1)).val - 1, h'⟩ : Fin n) =
          i0 := by
    intro _
    apply Fin.ext
    simp only
    omega
  have hAi : a ⟨(⟨i0.val + 1, by omega⟩ : Fin (n + 1)).val - 1, by omega⟩ =
      i0 := by
    rw [heq _]
    exact hi
  have hval := congrArg Fin.val hAi
  simp only at hval ⊢
  omega

private lemma marked_no_small_fixed (n : ℕ) (m : Marked n)
    (k : Fin (n + 1)) (hpos : 0 < k.val)
    (hlt : k.val < m.2.1.val + 1) : (embedMarked n m).1 k ≠ k := by
  obtain ⟨⟨a, ha⟩, ⟨i0, hi⟩⟩ := m
  have hlt' : k.val < i0.val + 1 := hlt
  intro heq
  have hval : ((embedMarked n ⟨⟨a, ha⟩, ⟨i0, hi⟩⟩).1 k).val = k.val :=
    congrArg Fin.val heq
  have h0 : k.val ≠ 0 := by
    omega
  have h1 : k.val - 1 < i0.val := by
    omega
  have hmem : k.val - 1 < n := by
    omega
  have hB : (markedFun n a i0 k).val = (a ⟨k.val - 1, hmem⟩).val := by
    simp only [markedFun, dite_eq_right h0, dite_eq_left h1]
  have hb := ha.2 ⟨k.val - 1, hmem⟩
  simp only [embedMarked] at hval
  simp only at hb
  omega

private lemma embedPlain_injective (n : ℕ) :
    Function.Injective (embedPlain n) := by
  intro a1 a2 heq
  obtain ⟨a1f, ha1⟩ := a1
  obtain ⟨a2f, ha2⟩ := a2
  apply Subtype.ext
  funext j
  apply Fin.ext
  have hk : (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val ≠ 0 := by
    simp only
    omega
  have h1 : (plainFun n a1f ⟨j.val + 1, by omega⟩).val =
      (a1f ⟨(⟨j.val + 1, by omega⟩ : Fin (n + 1)).val - 1, by omega⟩).val := by
    simp only [plainFun, dite_eq_right hk]
  have h2 : (plainFun n a2f ⟨j.val + 1, by omega⟩).val =
      (a2f ⟨(⟨j.val + 1, by omega⟩ : Fin (n + 1)).val - 1, by omega⟩).val := by
    simp only [plainFun, dite_eq_right hk]
  have hval :
      ((embedPlain n ⟨a1f, ha1⟩).1 ⟨j.val + 1, by omega⟩).val =
        ((embedPlain n ⟨a2f, ha2⟩).1 ⟨j.val + 1, by omega⟩).val := by
    rw [heq]
  simp only [embedPlain] at hval
  rw [h1, h2] at hval
  exact hval

private lemma embedMarked_injective (n : ℕ) :
    Function.Injective (embedMarked n) := by
  intro m1 m2 heq
  have hi_eq : m1.2.1.val = m2.2.1.val := by
    have h12 : ¬ m1.2.1.val < m2.2.1.val := by
      intro hlt
      have hpos :
          0 < (⟨m1.2.1.val + 1, by omega⟩ : Fin (n + 1)).val := by
        simp only
        omega
      have hlt2 :
          (⟨m1.2.1.val + 1, by omega⟩ : Fin (n + 1)).val <
            m2.2.1.val + 1 := by
        simp only
        omega
      have hNe := marked_no_small_fixed n m2 ⟨m1.2.1.val + 1, by omega⟩
        hpos hlt2
      have hFix1 := marked_fixed n m1
      have heq' :
          (embedMarked n m1).1 ⟨m1.2.1.val + 1, by omega⟩ =
            (embedMarked n m2).1 ⟨m1.2.1.val + 1, by omega⟩ := by
        rw [heq]
      have hFix2 :
          (embedMarked n m2).1 ⟨m1.2.1.val + 1, by omega⟩ =
            ⟨m1.2.1.val + 1, by omega⟩ := by
        rw [← heq']
        exact hFix1
      exact hNe hFix2
    have h21 : ¬ m2.2.1.val < m1.2.1.val := by
      intro hlt
      have hpos :
          0 < (⟨m2.2.1.val + 1, by omega⟩ : Fin (n + 1)).val := by
        simp only
        omega
      have hlt2 :
          (⟨m2.2.1.val + 1, by omega⟩ : Fin (n + 1)).val <
            m1.2.1.val + 1 := by
        simp only
        omega
      have hNe := marked_no_small_fixed n m1 ⟨m2.2.1.val + 1, by omega⟩
        hpos hlt2
      have hFix2 := marked_fixed n m2
      have heq' :
          (embedMarked n m1).1 ⟨m2.2.1.val + 1, by omega⟩ =
            (embedMarked n m2).1 ⟨m2.2.1.val + 1, by omega⟩ := by
        rw [heq]
      have hFix1 :
          (embedMarked n m1).1 ⟨m2.2.1.val + 1, by omega⟩ =
            ⟨m2.2.1.val + 1, by omega⟩ := by
        rw [heq']
        exact hFix2
      exact hNe hFix1
    omega
  have ha_eq : m1.1.1 = m2.1.1 := by
    funext j
    apply Fin.ext
    have h0 : (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val ≠ 0 := by
      simp only
      omega
    have heq_k :
        ((embedMarked n m1).1 ⟨j.val + 1, by omega⟩).val =
          ((embedMarked n m2).1 ⟨j.val + 1, by omega⟩).val := by
      rw [heq]
    simp only [embedMarked] at heq_k
    by_cases h1 : (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val - 1 <
        m1.2.1.val
    · have h2 : (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val - 1 <
          m2.2.1.val := by
        omega
      have hB1 := markedFun_val_of_lt n m1.1.1 m1.2.1
        ⟨j.val + 1, by omega⟩ h0 h1
      have hB2 := markedFun_val_of_lt n m2.1.1 m2.2.1
        ⟨j.val + 1, by omega⟩ h0 h2
      rw [hB1, hB2] at heq_k
      exact heq_k
    · have h2 : ¬ (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val - 1 <
          m2.2.1.val := by
        omega
      have hB1 := markedFun_val_of_ge n m1.1.1 m1.2.1
        ⟨j.val + 1, by omega⟩ h0 h1
      have hB2 := markedFun_val_of_ge n m2.1.1 m2.2.1
        ⟨j.val + 1, by omega⟩ h0 h2
      rw [hB1, hB2] at heq_k
      have heq_k' : (m1.1.1 j).val + 1 = (m2.1.1 j).val + 1 := heq_k
      omega
  obtain ⟨⟨a1f, ha1⟩, ⟨i1, hi1⟩⟩ := m1
  obtain ⟨⟨a2f, ha2⟩, ⟨i2, hi2⟩⟩ := m2
  have hi_eq' : i1.val = i2.val := hi_eq
  have hi_fin : i1 = i2 := Fin.ext hi_eq'
  have ha_fun : a1f = a2f := ha_eq
  subst ha_fun
  subst hi_fin
  rfl

private lemma embed_disjoint (n : ℕ) (a : Park n) (m : Marked n) :
    embedPlain n a ≠ embedMarked n m := by
  intro heq
  have hFix := marked_fixed n m
  have hpos : 0 < (⟨m.2.1.val + 1, by omega⟩ : Fin (n + 1)).val := by
    simp only
    omega
  have hNe := plain_no_fixed n a ⟨m.2.1.val + 1, by omega⟩ hpos
  have heq' : (embedPlain n a).1 ⟨m.2.1.val + 1, by omega⟩ =
      ⟨m.2.1.val + 1, by omega⟩ := by
    rw [heq]
    exact hFix
  exact hNe heq'

private def sumToPark (n : ℕ) : Park n ⊕ Marked n → Park (n + 1) :=
  Sum.elim (embedPlain n) (embedMarked n)

private lemma sumToPark_injective (n : ℕ) :
    Function.Injective (sumToPark n) := by
  intro x y hxy
  cases x with
  | inl a1 =>
    cases y with
    | inl a2 =>
      have ha : a1 = a2 := embedPlain_injective n (by
        simp only [sumToPark] at hxy
        exact hxy)
      rw [ha]
    | inr m2 =>
      have hcon : embedPlain n a1 = embedMarked n m2 := by
        simp only [sumToPark] at hxy
        exact hxy
      exact absurd hcon (embed_disjoint n a1 m2)
  | inr m1 =>
    cases y with
    | inl a2 =>
      have hcon : embedMarked n m1 = embedPlain n a2 := by
        simp only [sumToPark] at hxy
        exact hxy
      have hcon2 : embedPlain n a2 = embedMarked n m1 := hcon.symm
      exact absurd hcon2 (embed_disjoint n a2 m1)
    | inr m2 =>
      have hm : m1 = m2 := embedMarked_injective n (by
        simp only [sumToPark] at hxy
        exact hxy)
      rw [hm]

private def unplainFun (n : ℕ) (b : Park (n + 1))
    (hNo : ∀ k : Fin (n + 1), 0 < k.val → b.1 k ≠ k) :
    Fin n → Fin n :=
  fun j =>
    ⟨(b.1 ⟨j.val + 1, by omega⟩).val, by
      have hpos :
          0 < (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
        simp only
        omega
      have hNe := hNo ⟨j.val + 1, by omega⟩ hpos
      have hb := b.2.2 ⟨j.val + 1, by omega⟩
      simp only at hb
      have hval_ne :
          (b.1 ⟨j.val + 1, by omega⟩).val ≠
            (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
        intro hEq
        exact hNe (Fin.ext hEq)
      simp only at hval_ne
      omega⟩

private lemma unplainFun_mono (n : ℕ) (b : Park (n + 1))
    (hNo : ∀ k : Fin (n + 1), 0 < k.val → b.1 k ≠ k) :
    Monotone (unplainFun n b hNo) := by
  intro j1 j2 hle
  have hle' : j1.val ≤ j2.val := Fin.le_def.mp hle
  have hmon : b.1 ⟨j1.val + 1, by omega⟩ ≤ b.1 ⟨j2.val + 1, by omega⟩ := by
    apply b.2.1
    rw [Fin.le_def]
    simp only
    omega
  rw [Fin.le_def]
  exact Fin.le_def.mp hmon

private lemma unplainFun_bound (n : ℕ) (b : Park (n + 1))
    (hNo : ∀ k : Fin (n + 1), 0 < k.val → b.1 k ≠ k) (j : Fin n) :
    (unplainFun n b hNo j).val ≤ j.val := by
  have hpos : 0 < (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
    simp only
    omega
  have hNe := hNo ⟨j.val + 1, by omega⟩ hpos
  have hb := b.2.2 ⟨j.val + 1, by omega⟩
  simp only at hb
  have hval_ne :
      (b.1 ⟨j.val + 1, by omega⟩).val ≠
        (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
    intro hEq
    exact hNe (Fin.ext hEq)
  simp only at hval_ne
  change (b.1 ⟨j.val + 1, by omega⟩).val ≤ j.val
  omega

private lemma embedPlain_unplain (n : ℕ) (b : Park (n + 1))
    (hNo : ∀ k : Fin (n + 1), 0 < k.val → b.1 k ≠ k) :
    embedPlain n ⟨unplainFun n b hNo, unplainFun_mono n b hNo,
      fun j => unplainFun_bound n b hNo j⟩ = b := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  by_cases h0 : k.val = 0
  · have hL : ((embedPlain n ⟨unplainFun n b hNo, unplainFun_mono n b hNo,
        fun j => unplainFun_bound n b hNo j⟩).1 k).val = 0 :=
      plainFun_val_of_zero n _ k h0
    have hb := b.2.2 k
    omega
  · have hL : ((embedPlain n ⟨unplainFun n b hNo, unplainFun_mono n b hNo,
        fun j => unplainFun_bound n b hNo j⟩).1 k).val =
        (unplainFun n b hNo ⟨k.val - 1, by omega⟩).val :=
      plainFun_val_of_ne n _ k h0
    have heq : (⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩ :
        Fin (n + 1)) = k := by
      apply Fin.ext
      simp only
      omega
    have hU : (unplainFun n b hNo ⟨k.val - 1, by omega⟩).val =
        (b.1 k).val := by
      have hrfl : (unplainFun n b hNo ⟨k.val - 1, by omega⟩).val =
          (b.1 ⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩).val := rfl
      rw [hrfl, heq]
    rw [hL, hU]

private def unmarkedFun (n : ℕ) (b : Park (n + 1)) (i0 : Fin n) :
    Fin n → Fin n :=
  fun j =>
    if h : j.val < i0.val then
      ⟨(b.1 ⟨j.val + 1, by omega⟩).val, by
        have hb := b.2.2 ⟨j.val + 1, by omega⟩
        simp only at hb
        have hi := i0.isLt
        omega⟩
    else
      ⟨(b.1 ⟨j.val + 1, by omega⟩).val - 1, by
        have hlt := (b.1 ⟨j.val + 1, by omega⟩).isLt
        omega⟩

private lemma unmarkedFun_val_of_lt (n : ℕ) (b : Park (n + 1)) (i0 : Fin n)
    (j : Fin n) (h : j.val < i0.val) :
    (unmarkedFun n b i0 j).val = (b.1 ⟨j.val + 1, by omega⟩).val := by
  simp only [unmarkedFun, dite_eq_left h]

private lemma unmarkedFun_val_of_ge (n : ℕ) (b : Park (n + 1)) (i0 : Fin n)
    (j : Fin n) (h : ¬ j.val < i0.val) :
    (unmarkedFun n b i0 j).val =
      (b.1 ⟨j.val + 1, by omega⟩).val - 1 := by
  simp only [unmarkedFun, dite_eq_right h]

private lemma unmarkedFun_mono (n : ℕ) (b : Park (n + 1)) (i0 : Fin n)
    (hfix : b.1 ⟨i0.val + 1, by omega⟩ = ⟨i0.val + 1, by omega⟩) :
    Monotone (unmarkedFun n b i0) := by
  intro j1 j2 hle
  have hle' : j1.val ≤ j2.val := Fin.le_def.mp hle
  by_cases h1 : j1.val < i0.val
  · by_cases h2 : j2.val < i0.val
    · rw [Fin.le_def, unmarkedFun_val_of_lt n b i0 j1 h1,
        unmarkedFun_val_of_lt n b i0 j2 h2]
      have hmon : b.1 ⟨j1.val + 1, by omega⟩ ≤
          b.1 ⟨j2.val + 1, by omega⟩ := by
        apply b.2.1
        rw [Fin.le_def]
        simp only
        omega
      exact Fin.le_def.mp hmon
    · rw [Fin.le_def, unmarkedFun_val_of_lt n b i0 j1 h1,
        unmarkedFun_val_of_ge n b i0 j2 h2]
      have hb1 := b.2.2 ⟨j1.val + 1, by omega⟩
      simp only at hb1
      have hleK : (⟨i0.val + 1, by omega⟩ : Fin (n + 1)) ≤
          ⟨j2.val + 1, by omega⟩ := by
        rw [Fin.le_def]
        simp only
        omega
      have hmon : b.1 ⟨i0.val + 1, by omega⟩ ≤
          b.1 ⟨j2.val + 1, by omega⟩ := b.2.1 hleK
      have hfixV : (b.1 ⟨i0.val + 1, by omega⟩).val = i0.val + 1 :=
        congrArg Fin.val hfix
      have hle2 := Fin.le_def.mp hmon
      omega
  · by_cases h2 : j2.val < i0.val
    · have hcon : j1.val < i0.val := lt_of_le_of_lt hle' h2
      exact absurd hcon h1
    · rw [Fin.le_def, unmarkedFun_val_of_ge n b i0 j1 h1,
        unmarkedFun_val_of_ge n b i0 j2 h2]
      have hmon : b.1 ⟨j1.val + 1, by omega⟩ ≤
          b.1 ⟨j2.val + 1, by omega⟩ := by
        apply b.2.1
        rw [Fin.le_def]
        simp only
        omega
      have h := Fin.le_def.mp hmon
      omega

private lemma unmarkedFun_bound (n : ℕ) (b : Park (n + 1)) (i0 : Fin n)
    (hmin : ∀ k : Fin (n + 1), 0 < k.val → k.val < i0.val + 1 → b.1 k ≠ k)
    (j : Fin n) : (unmarkedFun n b i0 j).val ≤ j.val := by
  by_cases h : j.val < i0.val
  · rw [unmarkedFun_val_of_lt n b i0 j h]
    have hb := b.2.2 ⟨j.val + 1, by omega⟩
    simp only at hb
    have hpos : 0 < (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
      simp only
      omega
    have hlt : (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val < i0.val + 1 := by
      simp only
      omega
    have hNe := hmin ⟨j.val + 1, by omega⟩ hpos hlt
    have hval_ne : (b.1 ⟨j.val + 1, by omega⟩).val ≠
        (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
      intro hEq
      exact hNe (Fin.ext hEq)
    simp only at hval_ne
    omega
  · rw [unmarkedFun_val_of_ge n b i0 j h]
    have hb := b.2.2 ⟨j.val + 1, by omega⟩
    simp only at hb
    omega

private lemma unmarkedFun_fixed (n : ℕ) (b : Park (n + 1)) (i0 : Fin n)
    (hfix : b.1 ⟨i0.val + 1, by omega⟩ = ⟨i0.val + 1, by omega⟩) :
    unmarkedFun n b i0 i0 = i0 := by
  apply Fin.ext
  have hneg : ¬ i0.val < i0.val := lt_irrefl _
  rw [unmarkedFun_val_of_ge n b i0 i0 hneg]
  have hfixV : (b.1 ⟨i0.val + 1, by omega⟩).val = i0.val + 1 :=
    congrArg Fin.val hfix
  omega

private lemma embedMarked_unmarked (n : ℕ) (b : Park (n + 1)) (i0 : Fin n)
    (hfix : b.1 ⟨i0.val + 1, by omega⟩ = ⟨i0.val + 1, by omega⟩)
    (hmin : ∀ k : Fin (n + 1), 0 < k.val → k.val < i0.val + 1 → b.1 k ≠ k) :
    embedMarked n ⟨⟨unmarkedFun n b i0, unmarkedFun_mono n b i0 hfix,
      fun j => unmarkedFun_bound n b i0 hmin j⟩,
      ⟨i0, unmarkedFun_fixed n b i0 hfix⟩⟩ = b := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  by_cases h0 : k.val = 0
  · have hL : ((embedMarked n ⟨⟨unmarkedFun n b i0,
          unmarkedFun_mono n b i0 hfix,
          fun j => unmarkedFun_bound n b i0 hmin j⟩,
        ⟨i0, unmarkedFun_fixed n b i0 hfix⟩⟩).1 k).val = 0 :=
      markedFun_val_of_zero n _ i0 k h0
    have hb := b.2.2 k
    omega
  · by_cases h1 : k.val - 1 < i0.val
    · have hL : ((embedMarked n ⟨⟨unmarkedFun n b i0,
            unmarkedFun_mono n b i0 hfix,
            fun j => unmarkedFun_bound n b i0 hmin j⟩,
          ⟨i0, unmarkedFun_fixed n b i0 hfix⟩⟩).1 k).val =
          (unmarkedFun n b i0 ⟨k.val - 1, by omega⟩).val :=
        markedFun_val_of_lt n _ i0 k h0 h1
      have hlt : (⟨k.val - 1, by omega⟩ : Fin n).val < i0.val := h1
      have hU : (unmarkedFun n b i0 ⟨k.val - 1, by omega⟩).val =
          (b.1 ⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩).val :=
        unmarkedFun_val_of_lt n b i0 ⟨k.val - 1, by omega⟩ hlt
      have heq : (⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩ :
          Fin (n + 1)) = k := by
        apply Fin.ext
        simp only
        omega
      rw [hL, hU, heq]
    · have hL : ((embedMarked n ⟨⟨unmarkedFun n b i0,
            unmarkedFun_mono n b i0 hfix,
            fun j => unmarkedFun_bound n b i0 hmin j⟩,
          ⟨i0, unmarkedFun_fixed n b i0 hfix⟩⟩).1 k).val =
          (unmarkedFun n b i0 ⟨k.val - 1, by omega⟩).val + 1 :=
        markedFun_val_of_ge n _ i0 k h0 h1
      have hge : ¬ (⟨k.val - 1, by omega⟩ : Fin n).val < i0.val := h1
      have hU : (unmarkedFun n b i0 ⟨k.val - 1, by omega⟩).val =
          (b.1 ⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩).val - 1 :=
        unmarkedFun_val_of_ge n b i0 ⟨k.val - 1, by omega⟩ hge
      have heq : (⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩ :
          Fin (n + 1)) = k := by
        apply Fin.ext
        simp only
        omega
      have hleK : (⟨i0.val + 1, by omega⟩ : Fin (n + 1)) ≤ k := by
        rw [Fin.le_def]
        simp only
        omega
      have hmon : b.1 ⟨i0.val + 1, by omega⟩ ≤ b.1 k := b.2.1 hleK
      have hfixV : (b.1 ⟨i0.val + 1, by omega⟩).val = i0.val + 1 :=
        congrArg Fin.val hfix
      have hle := Fin.le_def.mp hmon
      have hge1 : 1 ≤
          (b.1 ⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩).val := by
        rw [heq]
        omega
      rw [hL, hU, heq]
      omega

private lemma sumToPark_surjective (n : ℕ) :
    Function.Surjective (sumToPark n) := by
  classical
  intro b
  by_cases h : ∃ k : Fin (n + 1), 0 < k.val ∧ b.1 k = k
  · obtain ⟨k_wit, hpos_wit, hfix_wit⟩ := h
    let S := Finset.univ.filter
      (fun k : Fin (n + 1) => 0 < k.val ∧ b.1 k = k)
    have hmem_wit : k_wit ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos_wit, hfix_wit⟩
    have hne : S.Nonempty := ⟨k_wit, hmem_wit⟩
    let k0 := S.min' hne
    have hk0_mem : k0 ∈ S := Finset.min'_mem _ _
    have hk0_filt := Finset.mem_filter.mp hk0_mem
    have hpos0 : 0 < k0.val := hk0_filt.2.1
    have hfix0 : b.1 k0 = k0 := hk0_filt.2.2
    have hmin_le : ∀ k ∈ S, k0 ≤ k :=
      fun k hk => Finset.min'_le _ _ hk
    let i0 : Fin n := ⟨k0.val - 1, by omega⟩
    have hi0_val : i0.val = k0.val - 1 := rfl
    have hFinEq : (⟨i0.val + 1, by omega⟩ : Fin (n + 1)) = k0 := by
      apply Fin.ext
      simp only
      omega
    have hfix : b.1 ⟨i0.val + 1, by omega⟩ =
        ⟨i0.val + 1, by omega⟩ := by
      rw [hFinEq]
      exact hfix0
    have hmin : ∀ k : Fin (n + 1), 0 < k.val → k.val < i0.val + 1 →
        b.1 k ≠ k := by
      intro k hpos hlt heq
      have hk_mem : k ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos, heq⟩
      have hle := hmin_le k hk_mem
      have hleV := Fin.le_def.mp hle
      omega
    let m : Marked n :=
      ⟨⟨unmarkedFun n b i0, unmarkedFun_mono n b i0 hfix,
        fun j => unmarkedFun_bound n b i0 hmin j⟩,
        ⟨i0, unmarkedFun_fixed n b i0 hfix⟩⟩
    use Sum.inr m
    change embedMarked n m = b
    exact embedMarked_unmarked n b i0 hfix hmin
  · have hNo : ∀ k : Fin (n + 1), 0 < k.val → b.1 k ≠ k := by
      intro k hpos heq
      exact h ⟨k, hpos, heq⟩
    let a : Park n :=
      ⟨unplainFun n b hNo, unplainFun_mono n b hNo,
        fun j => unplainFun_bound n b hNo j⟩
    use Sum.inl a
    change embedPlain n a = b
    exact embedPlain_unplain n b hNo

private lemma park_succ_card (n : ℕ) :
    Fintype.card (Park (n + 1)) =
      Fintype.card (Park n) + Fintype.card (Marked n) := by
  have hbij : Function.Bijective (sumToPark n) :=
    ⟨sumToPark_injective n, sumToPark_surjective n⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective (sumToPark n) hbij)
  rw [Fintype.card_sum] at hcard
  exact hcard.symm

private lemma park_zero_card : Fintype.card (Park 0) = 1 := by
  have huniq : Unique (Park 0) :=
    ⟨⟨fun i => Fin.elim0 i, fun a => Fin.elim0 a, fun i => Fin.elim0 i⟩,
      fun a => Subtype.ext (funext fun i => Fin.elim0 i)⟩
  exact @Fintype.card_unique _ huniq _

private lemma park_card_eq_catalan_aux : ∀ n m, m ≤ n →
    Fintype.card (Park m) = catalan m := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    rw [park_zero_card, catalan_zero]
  | succ n ih =>
    intro m hm
    by_cases hmn : m ≤ n
    · exact ih m hmn
    · have hmeq : m = n + 1 := by omega
      subst hmeq
      have hPn : Fintype.card (Park n) = catalan n := ih n (Nat.le_refl n)
      have hPsucc := park_succ_card n
      have hM := marked_card_eq_fiber_sum n
      have hMsum : Fintype.card (Marked n) =
          ∑ i : Fin n, catalan i.val * catalan (n - i.val) := by
        rw [hM]
        apply Finset.sum_congr rfl
        intro i _
        have hi1 : i.val ≤ n := Nat.le_of_lt i.isLt
        have hi2 : n - i.val ≤ n := Nat.sub_le n i.val
        rw [ih _ hi1, ih _ hi2]
      have hcat := catalan_succ n
      have hsplit := Fin.sum_univ_castSucc
        (fun i : Fin (n + 1) => catalan i.val * catalan (n - i.val))
      have hcast_sum : (∑ i : Fin n,
          catalan (i.castSucc).val * catalan (n - (i.castSucc).val)) =
          ∑ i : Fin n, catalan i.val * catalan (n - i.val) :=
        Finset.sum_congr rfl (fun i _ => rfl)
      have hlast : catalan (Fin.last n).val *
          catalan (n - (Fin.last n).val) =
          catalan n := by
        have hnn : n - n = 0 := by omega
        have hdef : catalan (Fin.last n).val *
            catalan (n - (Fin.last n).val) =
            catalan n * catalan (n - n) := rfl
        rw [hdef, hnn, catalan_zero, mul_one]
      rw [hPsucc, hPn, hMsum]
      rw [hcat, hsplit, hcast_sum, hlast]
      exact add_comm _ _

private lemma park_card_eq_catalan (n : ℕ) :
    Fintype.card (Park n) = catalan n :=
  park_card_eq_catalan_aux n n (Nat.le_refl n)

private lemma ratio_of_catalan (n : ℕ) (hn : 0 < n)
    (Cn : ℕ) (hCn : 0 < Cn)
    (h1 : (n + 1) * Cn = n.centralBinom)
    (h2 : (n + 2) * (catalan (n + 1)) = (n + 1).centralBinom)
    (h3 : (n + 1) * (n + 1).centralBinom = 2 * (2 * n + 1) * n.centralBinom)
    (M : ℕ)
    (hM : catalan (n + 1) = Cn + M) :
    (M : ℚ) / (Cn : ℚ) = ((3 : ℚ) * n) / (n + 2) := by
  have hCn' : (Cn : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hCn
  have hn2 : ((n : ℚ) + 2) ≠ 0 := by positivity
  have key : (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * Cn := by
    have e1 : (n+1) * ((n+2) * catalan (n+1)) = (n+1) * (2 * (2*n+1) * Cn) := by
      calc (n+1) * ((n+2) * catalan (n+1))
          = (n+2) * catalan (n+1) * (n+1) := by ring
        _ = (n+1).centralBinom * (n+1) := by rw [h2]
        _ = (n+1) * (n+1).centralBinom := by ring
        _ = 2 * (2*n+1) * n.centralBinom := h3
        _ = 2 * (2*n+1) * ((n+1) * Cn) := by rw [h1]
        _ = (n+1) * (2 * (2*n+1) * Cn) := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) e1
  have keyQ : ((n : ℚ) + 2) * (catalan (n+1) : ℚ) = 2 * (2 * n + 1) * (Cn : ℚ) := by
    exact_mod_cast key
  have hMQ : (M : ℚ) = (catalan (n+1) : ℚ) - (Cn : ℚ) := by
    have hcast : (catalan (n+1) : ℚ) = (Cn : ℚ) + (M : ℚ) := by exact_mod_cast hM
    linarith
  rw [hMQ]
  field_simp
  linarith [keyQ]

/--
**Expected number of lucky cars in weakly increasing parking functions.** Let $n \ge 1$. Number
cars and spots from $0$, and encode a weakly increasing parking function of length $n$ as a
nondecreasing map $a : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ with $a(i) \le i$ for every $i$.
The average, over all such maps $a$, of the number of indices $i$ with $a(i) = i$ equals
$\frac{3n}{n+2}$. Here car $i$ parks in spot $i$ and is lucky exactly when $a(i) = i$, so this
number counts both the lucky cars and the lucky spots.

Proves `Wanted` entry `expected_lucky_spots_weakly_increasing_parking_functions`.

Source: Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens,
and Marshall Moats, "Lucky Cars and Lucky Spots in Parking Functions,"
Journal of Integer Sequences 29 (2026), Article 26.1.1, Corollary,
lines 631–633 (supporting lemma lines 619–629),
https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.tex
The corollary attributes the Dyck-path expectation value to Deutsch.
-/
theorem expected_lucky_spots_weakly_increasing_parking_functions
    (n : ℕ) (hn : 0 < n) :
    let parkingFunctions := Finset.univ.filter fun a : Fin n → Fin n =>
      Monotone a ∧ ∀ i, (a i).val ≤ i.val
    (∑ a ∈ parkingFunctions,
        ((Finset.univ.filter fun i : Fin n => a i = i).card : ℚ)) /
      (parkingFunctions.card : ℚ) = ((3 : ℚ) * n) / (n + 2) := by
  dsimp only
  have hPCardNat : (Finset.univ.filter fun a : Fin n → Fin n =>
      Monotone a ∧ ∀ i, (a i).val ≤ i.val).card =
      Fintype.card (Park n) := (park_card_eq_filter n).symm
  have hPCard : ((Finset.univ.filter fun a : Fin n → Fin n =>
      Monotone a ∧ ∀ i, (a i).val ≤ i.val).card : ℚ) =
      (Fintype.card (Park n) : ℚ) := congrArg Nat.cast hPCardNat
  have hMSum : (∑ a ∈ Finset.univ.filter fun a : Fin n → Fin n =>
      Monotone a ∧ ∀ i, (a i).val ≤ i.val,
      ((Finset.univ.filter fun i : Fin n => a i = i).card : ℚ)) =
      (Fintype.card (Marked n) : ℚ) := by
    rw [← Nat.cast_sum]
    exact congrArg Nat.cast (marked_card_eq_sum n).symm
  rw [hPCard, hMSum]
  have hCpos : 0 < catalan n := by
    have hcb := Nat.centralBinom_pos n
    have h1 := succ_mul_catalan_eq_centralBinom n
    have hpos : 0 < (n + 1) * catalan n := by
      rw [h1]
      exact hcb
    have hne : catalan n ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hpos
      exact lt_irrefl 0 hpos
    exact Nat.pos_of_ne_zero hne
  have hCn : 0 < Fintype.card (Park n) := by
    rw [park_card_eq_catalan n]
    exact hCpos
  have h1 : (n + 1) * Fintype.card (Park n) = n.centralBinom := by
    rw [park_card_eq_catalan n]
    exact succ_mul_catalan_eq_centralBinom n
  have h2 : (n + 2) * catalan (n + 1) = (n + 1).centralBinom :=
    succ_mul_catalan_eq_centralBinom (n + 1)
  have h3 : (n + 1) * (n + 1).centralBinom =
      2 * (2 * n + 1) * n.centralBinom :=
    Nat.succ_mul_centralBinom_succ n
  have hP1 : Fintype.card (Park (n + 1)) = catalan (n + 1) :=
    park_card_eq_catalan (n + 1)
  have hM' : catalan (n + 1) =
      Fintype.card (Park n) + Fintype.card (Marked n) := by
    rw [← hP1]
    exact park_succ_card n
  exact ratio_of_catalan n hn (Fintype.card (Park n)) hCn h1 h2 h3
    (Fintype.card (Marked n)) hM'

end MetaMathlibExt
end
