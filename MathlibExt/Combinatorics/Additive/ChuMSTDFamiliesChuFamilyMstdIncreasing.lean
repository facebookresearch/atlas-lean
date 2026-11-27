/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamilies
import Mathlib.Data.Int.Interval

namespace MetaMathlibExt

@[expose] public section

open Pointwise

private theorem sDiff_append (a : ℤ) (p q : List ℕ) :
    setOfConsecutiveDifferences a (p ++ q) =
      setOfConsecutiveDifferences a p ∪ setOfConsecutiveDifferences (a + (p.sum : ℤ)) q := by
  induction p generalizing a with
  | nil =>
      have ha : a ∈ setOfConsecutiveDifferences a q := by
        cases q <;> simp [setOfConsecutiveDifferences]
      simp [setOfConsecutiveDifferences, ha]
  | cons g p ih =>
      simp [setOfConsecutiveDifferences_cons, ih, Finset.insert_union, add_assoc]

private theorem sum_chuBlock (k : ℕ) : (chuBlock k).sum = 4 * (k + 1) := by
  simp [chuBlock, List.sum_append]
  omega

private theorem mem_replicate4 (n : ℕ) (b y : ℤ) :
    y ∈ setOfConsecutiveDifferences b (List.replicate n 4) ↔
      ∃ i : ℕ, i ≤ n ∧ y = b + 4 * (i : ℤ) := by
  induction n generalizing b with
  | zero =>
      simp only [List.replicate_zero]
      constructor
      · intro hy
        have hy' : y = b := by simpa [setOfConsecutiveDifferences] using hy
        exact ⟨0, Nat.zero_le _, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        have hi0 : i = 0 := by omega
        subst hi0
        simp [setOfConsecutiveDifferences]
  | succ n ih =>
      rw [List.replicate_succ, setOfConsecutiveDifferences_cons, Finset.mem_insert, ih]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨0, Nat.zero_le _, by omega⟩
        · exact ⟨i + 1, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩
        by_cases hj0 : j = 0
        · subst hj0
          exact Or.inl (by omega)
        · exact Or.inr ⟨j - 1, by omega, by omega⟩

private theorem mem_chuBlock (k : ℕ) (a x : ℤ) :
    x ∈ setOfConsecutiveDifferences a (chuBlock k) ↔
      x = a ∨ (∃ i : ℕ, i ≤ k ∧ x = a + 1 + 4 * (i : ℤ)) ∨
        x = a + 4 * (k : ℤ) + 4 := by
  have hR : (List.replicate k 4).sum = k * 4 := by simp [List.sum_replicate]
  have h3 : ∀ (c y : ℤ), y ∈ setOfConsecutiveDifferences c [3] ↔ y = c ∨ y = c + 3 := by
    intro c y
    simp only [setOfConsecutiveDifferences, Finset.mem_insert, Finset.mem_singleton]
    omega
  simp only [chuBlock]
  have h1R : (1 :: List.replicate k 4).sum = 1 + k * 4 := by simp [hR]
  rw [sDiff_append, h1R, Finset.mem_union, setOfConsecutiveDifferences_cons,
    Finset.mem_insert, mem_replicate4, h3]
  constructor
  · rintro ((rfl | ⟨i, hi, rfl⟩) | h | h)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨i, hi, by omega⟩)
    · exact Or.inr (Or.inl ⟨k, le_rfl, by omega⟩)
    · exact Or.inr (Or.inr (by omega))
  · rintro (rfl | ⟨i, hi, rfl⟩ | rfl)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr ⟨i, hi, by omega⟩)
    · exact Or.inr (Or.inr (by omega))

private theorem mem_tail123 (a x : ℤ) :
    x ∈ setOfConsecutiveDifferences a [1, 1, 2] ↔
      x = a ∨ x = a + 1 ∨ x = a + 2 ∨ x = a + 4 := by
  simp only [setOfConsecutiveDifferences, Finset.mem_insert, Finset.mem_singleton]
  omega

private theorem mem_concat4 (a x : ℤ) (p q r s : List ℕ) :
    x ∈ setOfConsecutiveDifferences a (p ++ q ++ r ++ s) ↔
      x ∈ setOfConsecutiveDifferences a p ∨
        x ∈ setOfConsecutiveDifferences (a + (p.sum : ℤ)) q ∨
        x ∈ setOfConsecutiveDifferences (a + (p.sum : ℤ) + (q.sum : ℤ)) r ∨
        x ∈ setOfConsecutiveDifferences
          (a + (p.sum : ℤ) + (q.sum : ℤ) + (r.sum : ℤ)) s := by
  rw [sDiff_append, sDiff_append, sDiff_append, Finset.mem_union, Finset.mem_union,
    Finset.mem_union]
  have u1 : a + (((p ++ q).sum : ℕ) : ℤ) = a + (p.sum : ℤ) + (q.sum : ℤ) := by
    simp [List.sum_append]
    omega
  have u2 : a + ((((p ++ q) ++ r).sum : ℕ) : ℤ)
      = a + (p.sum : ℤ) + (q.sum : ℤ) + (r.sum : ℤ) := by
    simp [List.sum_append]
    omega
  rw [u1, u2]
  tauto

private abbrev Ashort (k : ℕ) : Finset ℤ :=
  setOfConsecutiveDifferences 0 ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ [1, 1, 2])

private abbrev Along (k : ℕ) : Finset ℤ :=
  setOfConsecutiveDifferences 0 ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ [1, 1, 2, 1])

private theorem mem_Ashort (k : ℕ) (x : ℤ) :
    x ∈ Ashort k ↔
      x ∈ setOfConsecutiveDifferences 0 [1, 1, 2] ∨
        x ∈ setOfConsecutiveDifferences 4 (chuBlock k) ∨
        x ∈ setOfConsecutiveDifferences (4 * (k : ℤ) + 8) (chuBlock (k + 1)) ∨
        x ∈ setOfConsecutiveDifferences (8 * (k : ℤ) + 16) [1, 1, 2] := by
  have hps : ([1, 1, 2] : List ℕ).sum = 4 := rfl
  simp only [Ashort]
  rw [mem_concat4, hps, sum_chuBlock, sum_chuBlock]
  have e1 : (0 : ℤ) + ((4 : ℕ) : ℤ) = 4 := by omega
  have e2 : (4 : ℤ) + ((4 * (k + 1) : ℕ) : ℤ) = 4 * (k : ℤ) + 8 := by omega
  have e3 : (4 : ℤ) + ((4 * (k + 1) : ℕ) : ℤ) + ((4 * (k + 1 + 1) : ℕ) : ℤ)
      = 8 * (k : ℤ) + 16 := by omega
  rw [e1, e3, e2]

private theorem Ashort_mem0 (k : ℕ) : (0 : ℤ) ∈ Ashort k := by
  rw [mem_Ashort k]
  refine Or.inl ?_
  rw [mem_tail123]
  exact Or.inl (by omega)

private theorem Ashort_mem1 (k : ℕ) : (1 : ℤ) ∈ Ashort k := by
  rw [mem_Ashort k]
  refine Or.inl ?_
  rw [mem_tail123]
  exact Or.inr (Or.inl (by omega))

private theorem Ashort_mem2 (k : ℕ) : (2 : ℤ) ∈ Ashort k := by
  rw [mem_Ashort k]
  refine Or.inl ?_
  rw [mem_tail123]
  exact Or.inr (Or.inr (Or.inl (by omega)))

private theorem Ashort_mem4 (k : ℕ) : (4 : ℤ) ∈ Ashort k := by
  rw [mem_Ashort k]
  refine Or.inl ?_
  rw [mem_tail123]
  exact Or.inr (Or.inr (Or.inr (by omega)))

private theorem Ashort_mem5p (k : ℕ) (j : ℕ) (hj : j ≤ k) :
    (5 : ℤ) + 4 * (j : ℤ) ∈ Ashort k := by
  rw [mem_Ashort k]
  refine Or.inr (Or.inl ?_)
  rw [mem_chuBlock]
  exact Or.inr (Or.inl ⟨j, hj, by omega⟩)

private theorem Ashort_memK8 (k : ℕ) : 4 * (k : ℤ) + 8 ∈ Ashort k := by
  rw [mem_Ashort k]
  refine Or.inr (Or.inl ?_)
  rw [mem_chuBlock]
  exact Or.inr (Or.inr (by omega))

private theorem Ashort_mem49p (k : ℕ) (i : ℕ) (hi : i ≤ k + 1) :
    4 * (k : ℤ) + 9 + 4 * (i : ℤ) ∈ Ashort k := by
  rw [mem_Ashort k]
  refine Or.inr (Or.inr (Or.inl ?_))
  rw [mem_chuBlock]
  exact Or.inr (Or.inl ⟨i, hi, by omega⟩)

private theorem Ashort_mem16 (k : ℕ) : 8 * (k : ℤ) + 16 ∈ Ashort k := by
  rw [mem_Ashort k]
  refine Or.inr (Or.inr (Or.inr ?_))
  rw [mem_tail123]
  exact Or.inl (by omega)

private theorem Ashort_mem17 (k : ℕ) : 8 * (k : ℤ) + 17 ∈ Ashort k := by
  rw [mem_Ashort k]
  refine Or.inr (Or.inr (Or.inr ?_))
  rw [mem_tail123]
  exact Or.inr (Or.inl (by omega))

private theorem Ashort_mem18 (k : ℕ) : 8 * (k : ℤ) + 18 ∈ Ashort k := by
  rw [mem_Ashort k]
  refine Or.inr (Or.inr (Or.inr ?_))
  rw [mem_tail123]
  exact Or.inr (Or.inr (Or.inl (by omega)))

private theorem Ashort_mem20 (k : ℕ) : 8 * (k : ℤ) + 20 ∈ Ashort k := by
  rw [mem_Ashort k]
  refine Or.inr (Or.inr (Or.inr ?_))
  rw [mem_tail123]
  exact Or.inr (Or.inr (Or.inr (by omega)))

private theorem Ashort_mem5pZ (k : ℕ) (i : ℤ) (hi0 : 0 ≤ i) (hik : i ≤ (k : ℤ)) :
    5 + 4 * i ∈ Ashort k := by
  have h := Ashort_mem5p k i.toNat (by omega)
  rwa [Int.toNat_of_nonneg hi0] at h

private theorem Ashort_mem49pZ (k : ℕ) (i : ℤ) (hi0 : 0 ≤ i) (hik : i ≤ (k : ℤ) + 1) :
    4 * (k : ℤ) + 9 + 4 * i ∈ Ashort k := by
  have h := Ashort_mem49p k i.toNat (by omega)
  rwa [Int.toNat_of_nonneg hi0] at h

private theorem Ashort_bounds (k : ℕ) (hk : 0 < k) (x : ℤ) (hx : x ∈ Ashort k) :
    0 ≤ x ∧ x ≤ 8 * (k : ℤ) + 20 := by
  rw [mem_Ashort k, mem_chuBlock, mem_chuBlock, mem_tail123, mem_tail123] at hx
  rcases hx with ((rfl|rfl|rfl|rfl)|(rfl|⟨i,hi,rfl⟩|rfl)|(rfl|⟨j,hj,rfl⟩|rfl)|
    (rfl|rfl|rfl|rfl))
  all_goals omega

private theorem Ashort_no3 (k : ℕ) (x : ℤ) (hx : x ∈ Ashort k) : x % 4 ≠ 3 := by
  rw [mem_Ashort k, mem_chuBlock, mem_chuBlock, mem_tail123, mem_tail123] at hx
  rcases hx with ((rfl|rfl|rfl|rfl)|(rfl|⟨i,hi,rfl⟩|rfl)|(rfl|⟨j,hj,rfl⟩|rfl)|
    (rfl|rfl|rfl|rfl))
  all_goals omega

private theorem Ashort_A0 (k : ℕ) (x : ℤ) (hx : x ∈ Ashort k) (hmod : x % 4 = 0) :
    x = 0 ∨ x = 4 ∨ x = 4 * (k : ℤ) + 8 ∨ x = 8 * (k : ℤ) + 16 ∨
      x = 8 * (k : ℤ) + 20 := by
  rw [mem_Ashort k, mem_chuBlock, mem_chuBlock, mem_tail123, mem_tail123] at hx
  rcases hx with ((rfl|rfl|rfl|rfl)|(rfl|⟨i,hi,rfl⟩|rfl)|(rfl|⟨j,hj,rfl⟩|rfl)|
    (rfl|rfl|rfl|rfl))
  all_goals omega

private theorem Ashort_A2 (k : ℕ) (x : ℤ) (hx : x ∈ Ashort k) (hmod : x % 4 = 2) :
    x = 2 ∨ x = 8 * (k : ℤ) + 18 := by
  rw [mem_Ashort k, mem_chuBlock, mem_chuBlock, mem_tail123, mem_tail123] at hx
  rcases hx with ((rfl|rfl|rfl|rfl)|(rfl|⟨i,hi,rfl⟩|rfl)|(rfl|⟨j,hj,rfl⟩|rfl)|
    (rfl|rfl|rfl|rfl))
  all_goals omega

private theorem Along_insert (k : ℕ) : Along k = insert (8 * (k : ℤ) + 21) (Ashort k) := by
  have hG : ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ [1, 1, 2]).sum = 8 * k + 20 := by
    simp [List.sum_append, sum_chuBlock]
    omega
  have hsplit : ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ [1, 1, 2, 1] : List ℕ)
      = ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ [1, 1, 2]) ++ [1] := by
    simp
  have h1 : ∀ (c x : ℤ), x ∈ setOfConsecutiveDifferences c [1] ↔ x = c ∨ x = c + 1 := by
    intro c x
    simp only [setOfConsecutiveDifferences, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hS1 : setOfConsecutiveDifferences (8 * (k : ℤ) + 20) [1]
      = {8 * (k : ℤ) + 20, 8 * (k : ℤ) + 21} := by
    apply Finset.ext
    intro x
    rw [h1]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hmem : (8 * (k : ℤ) + 20) ∈ Ashort k := Ashort_mem20 k
  have e : (0 : ℤ) + ((8 * k + 20 : ℕ) : ℤ) = 8 * (k : ℤ) + 20 := by omega
  simp only [Along]
  rw [hsplit, sDiff_append, hG, e, hS1]
  have hA : setOfConsecutiveDifferences 0 ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++
      [1, 1, 2]) = Ashort k := rfl
  rw [hA]
  apply Finset.ext
  intro x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | rfl | rfl)
    · exact Or.inr h
    · exact Or.inr hmem
    · exact Or.inl rfl
  · intro h
    rcases h with rfl | h
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl h

private theorem Along_mem0 (k : ℕ) : (0 : ℤ) ∈ Along k := by
  rw [Along_insert k]
  exact Finset.mem_insert_of_mem (Ashort_mem0 k)

private theorem Along_mem1 (k : ℕ) : (1 : ℤ) ∈ Along k := by
  rw [Along_insert k]
  exact Finset.mem_insert_of_mem (Ashort_mem1 k)

private theorem Along_mem2 (k : ℕ) : (2 : ℤ) ∈ Along k := by
  rw [Along_insert k]
  exact Finset.mem_insert_of_mem (Ashort_mem2 k)

private theorem Along_mem4 (k : ℕ) : (4 : ℤ) ∈ Along k := by
  rw [Along_insert k]
  exact Finset.mem_insert_of_mem (Ashort_mem4 k)

private theorem Along_mem5pZ (k : ℕ) (i : ℤ) (hi0 : 0 ≤ i) (hik : i ≤ (k : ℤ)) :
    5 + 4 * i ∈ Along k := by
  rw [Along_insert k]
  exact Finset.mem_insert_of_mem (Ashort_mem5pZ k i hi0 hik)

private theorem Along_memK8 (k : ℕ) : 4 * (k : ℤ) + 8 ∈ Along k := by
  rw [Along_insert k]
  exact Finset.mem_insert_of_mem (Ashort_memK8 k)

private theorem Along_mem49pZ (k : ℕ) (i : ℤ) (hi0 : 0 ≤ i) (hik : i ≤ (k : ℤ) + 1) :
    4 * (k : ℤ) + 9 + 4 * i ∈ Along k := by
  rw [Along_insert k]
  exact Finset.mem_insert_of_mem (Ashort_mem49pZ k i hi0 hik)

private theorem Along_mem16 (k : ℕ) : 8 * (k : ℤ) + 16 ∈ Along k := by
  rw [Along_insert k]
  exact Finset.mem_insert_of_mem (Ashort_mem16 k)

private theorem Along_mem17 (k : ℕ) : 8 * (k : ℤ) + 17 ∈ Along k := by
  rw [Along_insert k]
  exact Finset.mem_insert_of_mem (Ashort_mem17 k)

private theorem Along_mem18 (k : ℕ) : 8 * (k : ℤ) + 18 ∈ Along k := by
  rw [Along_insert k]
  exact Finset.mem_insert_of_mem (Ashort_mem18 k)

private theorem Along_mem20 (k : ℕ) : 8 * (k : ℤ) + 20 ∈ Along k := by
  rw [Along_insert k]
  exact Finset.mem_insert_of_mem (Ashort_mem20 k)

private theorem Along_mem21 (k : ℕ) : 8 * (k : ℤ) + 21 ∈ Along k := by
  rw [Along_insert k]
  simp

private theorem Along_bounds (k : ℕ) (hk : 0 < k) (x : ℤ) (hx : x ∈ Along k) :
    0 ≤ x ∧ x ≤ 8 * (k : ℤ) + 21 := by
  rw [Along_insert k, Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · omega
  · have h := Ashort_bounds k hk x hx
    omega

private theorem Along_no3 (k : ℕ) (x : ℤ) (hx : x ∈ Along k) : x % 4 ≠ 3 := by
  rw [Along_insert k, Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · omega
  · exact Ashort_no3 k x hx

private theorem Along_A0 (k : ℕ) (x : ℤ) (hx : x ∈ Along k) (hmod : x % 4 = 0) :
    x = 0 ∨ x = 4 ∨ x = 4 * (k : ℤ) + 8 ∨ x = 8 * (k : ℤ) + 16 ∨
      x = 8 * (k : ℤ) + 20 := by
  rw [Along_insert k, Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · omega
  · exact Ashort_A0 k x hx hmod

private theorem Along_A2 (k : ℕ) (x : ℤ) (hx : x ∈ Along k) (hmod : x % 4 = 2) :
    x = 2 ∨ x = 8 * (k : ℤ) + 18 := by
  rw [Along_insert k, Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · omega
  · exact Ashort_A2 k x hx hmod

private theorem neg_mem_sub (A : Finset ℤ) (d : ℤ) (hd : d ∈ A - A) : -d ∈ A - A := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_sub.mp hd
  exact Finset.mem_sub.mpr ⟨b, hb, a, ha, by omega⟩

private theorem absent6 (k : ℕ) (hk : 0 < k) (A : Finset ℤ)
    (hA0 : ∀ x ∈ A, x % 4 = 0 → x = 0 ∨ x = 4 ∨ x = 4 * (k : ℤ) + 8 ∨
      x = 8 * (k : ℤ) + 16 ∨ x = 8 * (k : ℤ) + 20)
    (hA2 : ∀ x ∈ A, x % 4 = 2 → x = 2 ∨ x = 8 * (k : ℤ) + 18)
    (hno3 : ∀ x ∈ A, x % 4 ≠ 3)
    (i : ℕ) (hi : i < k) : (6 : ℤ) + 4 * (i : ℤ) ∉ A - A := by
  intro hcon
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_sub.mp hcon
  have hcases : (a % 4 = 0 ∧ b % 4 = 2) ∨ (a % 4 = 2 ∧ b % 4 = 0) := by
    have h1 := hno3 a ha
    have h2 := hno3 b hb
    omega
  rcases hcases with ⟨ha0, hb2⟩ | ⟨ha2, hb0⟩
  · have haE := hA0 a ha ha0
    have hbE := hA2 b hb hb2
    rcases haE with rfl | rfl | rfl | rfl | rfl <;> rcases hbE with rfl | rfl <;> omega
  · have haE := hA2 a ha ha2
    have hbE := hA0 b hb hb0
    rcases haE with rfl | rfl <;> rcases hbE with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem absent8k (k : ℕ) (hk : 0 < k) (A : Finset ℤ)
    (hA0 : ∀ x ∈ A, x % 4 = 0 → x = 0 ∨ x = 4 ∨ x = 4 * (k : ℤ) + 8 ∨
      x = 8 * (k : ℤ) + 16 ∨ x = 8 * (k : ℤ) + 20)
    (hA2 : ∀ x ∈ A, x % 4 = 2 → x = 2 ∨ x = 8 * (k : ℤ) + 18)
    (hno3 : ∀ x ∈ A, x % 4 ≠ 3)
    (i : ℕ) (hi : i < k) : 8 * (k : ℤ) + 10 - 4 * (i : ℤ) ∉ A - A := by
  intro hcon
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_sub.mp hcon
  have hcases : (a % 4 = 0 ∧ b % 4 = 2) ∨ (a % 4 = 2 ∧ b % 4 = 0) := by
    have h1 := hno3 a ha
    have h2 := hno3 b hb
    omega
  rcases hcases with ⟨ha0, hb2⟩ | ⟨ha2, hb0⟩
  · have haE := hA0 a ha ha0
    have hbE := hA2 b hb hb2
    rcases haE with rfl | rfl | rfl | rfl | rfl <;> rcases hbE with rfl | rfl <;> omega
  · have haE := hA2 a ha ha2
    have hbE := hA0 b hb hb0
    rcases haE with rfl | rfl <;> rcases hbE with rfl | rfl | rfl | rfl | rfl <;> omega

private abbrev dPos1 (k : ℕ) : Finset ℤ :=
  (Finset.range k).image (fun i : ℕ => (6 : ℤ) + 4 * (i : ℤ))

private abbrev dPos2 (k : ℕ) : Finset ℤ :=
  (Finset.range k).image (fun i : ℕ => 8 * (k : ℤ) + 10 - 4 * (i : ℤ))

private abbrev dNeg1 (k : ℕ) : Finset ℤ :=
  (Finset.range k).image (fun i : ℕ => -((6 : ℤ) + 4 * (i : ℤ)))

private abbrev dNeg2 (k : ℕ) : Finset ℤ :=
  (Finset.range k).image (fun i : ℕ => -(8 * (k : ℤ) + 10 - 4 * (i : ℤ)))

private abbrev missD (k : ℕ) : Finset ℤ := dPos1 k ∪ dPos2 k ∪ dNeg1 k ∪ dNeg2 k

private theorem disj12 (k : ℕ) : Disjoint (dPos1 k) (dPos2 k) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [dPos1, dPos2, Finset.mem_image, Finset.mem_range] at hx1 hx2
  obtain ⟨i, hi, rfl⟩ := hx1
  obtain ⟨j, hj, hjx⟩ := hx2
  have hjx' : 8 * (k : ℤ) + 10 - 4 * (j : ℤ) = 6 + 4 * (i : ℤ) := hjx
  omega

private theorem disj13 (k : ℕ) : Disjoint (dPos1 k) (dNeg1 k) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [dPos1, dNeg1, Finset.mem_image, Finset.mem_range] at hx1 hx2
  obtain ⟨i, hi, rfl⟩ := hx1
  obtain ⟨j, hj, hjx⟩ := hx2
  have hjx' : -((6 : ℤ) + 4 * (j : ℤ)) = 6 + 4 * (i : ℤ) := hjx
  omega

private theorem disj14 (k : ℕ) : Disjoint (dPos1 k) (dNeg2 k) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [dPos1, dNeg2, Finset.mem_image, Finset.mem_range] at hx1 hx2
  obtain ⟨i, hi, rfl⟩ := hx1
  obtain ⟨j, hj, hjx⟩ := hx2
  have hjx' : -(8 * (k : ℤ) + 10 - 4 * (j : ℤ)) = 6 + 4 * (i : ℤ) := hjx
  omega

private theorem disj23 (k : ℕ) : Disjoint (dPos2 k) (dNeg1 k) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [dPos2, dNeg1, Finset.mem_image, Finset.mem_range] at hx1 hx2
  obtain ⟨i, hi, rfl⟩ := hx1
  obtain ⟨j, hj, hjx⟩ := hx2
  have hjx' : -((6 : ℤ) + 4 * (j : ℤ)) = 8 * (k : ℤ) + 10 - 4 * (i : ℤ) := hjx
  omega

private theorem disj24 (k : ℕ) : Disjoint (dPos2 k) (dNeg2 k) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [dPos2, dNeg2, Finset.mem_image, Finset.mem_range] at hx1 hx2
  obtain ⟨i, hi, rfl⟩ := hx1
  obtain ⟨j, hj, hjx⟩ := hx2
  have hjx' : -(8 * (k : ℤ) + 10 - 4 * (j : ℤ))
      = 8 * (k : ℤ) + 10 - 4 * (i : ℤ) := hjx
  omega

private theorem disj34 (k : ℕ) : Disjoint (dNeg1 k) (dNeg2 k) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [dNeg1, dNeg2, Finset.mem_image, Finset.mem_range] at hx1 hx2
  obtain ⟨i, hi, rfl⟩ := hx1
  obtain ⟨j, hj, hjx⟩ := hx2
  have hjx' : -(8 * (k : ℤ) + 10 - 4 * (j : ℤ)) = -((6 : ℤ) + 4 * (i : ℤ)) := hjx
  omega

private theorem card_missD (k : ℕ) : (missD k).card = 4 * k := by
  have inj1 : Function.Injective (fun i : ℕ => (6 : ℤ) + 4 * (i : ℤ)) := by
    intro i j hij
    have hij' : (6 : ℤ) + 4 * (i : ℤ) = 6 + 4 * (j : ℤ) := hij
    have h : (i : ℤ) = (j : ℤ) := by omega
    exact Int.ofNat_inj.mp h
  have inj2 : Function.Injective (fun i : ℕ => 8 * (k : ℤ) + 10 - 4 * (i : ℤ)) := by
    intro i j hij
    have hij' : 8 * (k : ℤ) + 10 - 4 * (i : ℤ) = 8 * (k : ℤ) + 10 - 4 * (j : ℤ) := hij
    have h : (i : ℤ) = (j : ℤ) := by omega
    exact Int.ofNat_inj.mp h
  have inj3 : Function.Injective (fun i : ℕ => -((6 : ℤ) + 4 * (i : ℤ))) := by
    intro i j hij
    have hij' : -((6 : ℤ) + 4 * (i : ℤ)) = -((6 : ℤ) + 4 * (j : ℤ)) := hij
    have h : (i : ℤ) = (j : ℤ) := by omega
    exact Int.ofNat_inj.mp h
  have inj4 : Function.Injective
      (fun i : ℕ => -(8 * (k : ℤ) + 10 - 4 * (i : ℤ))) := by
    intro i j hij
    have hij' : -(8 * (k : ℤ) + 10 - 4 * (i : ℤ))
        = -(8 * (k : ℤ) + 10 - 4 * (j : ℤ)) := hij
    have h : (i : ℤ) = (j : ℤ) := by omega
    exact Int.ofNat_inj.mp h
  have c1 : (dPos1 k).card = k := by
    rw [show dPos1 k = (Finset.range k).image (fun i : ℕ => (6 : ℤ) + 4 * (i : ℤ))
      from rfl, Finset.card_image_of_injective _ inj1, Finset.card_range]
  have c2 : (dPos2 k).card = k := by
    rw [show dPos2 k
        = (Finset.range k).image (fun i : ℕ => 8 * (k : ℤ) + 10 - 4 * (i : ℤ)) from rfl,
      Finset.card_image_of_injective _ inj2, Finset.card_range]
  have c3 : (dNeg1 k).card = k := by
    rw [show dNeg1 k = (Finset.range k).image (fun i : ℕ => -((6 : ℤ) + 4 * (i : ℤ)))
      from rfl, Finset.card_image_of_injective _ inj3, Finset.card_range]
  have c4 : (dNeg2 k).card = k := by
    rw [show dNeg2 k
        = (Finset.range k).image (fun i : ℕ => -(8 * (k : ℤ) + 10 - 4 * (i : ℤ)))
      from rfl, Finset.card_image_of_injective _ inj4, Finset.card_range]
  have e_top : Disjoint ((dPos1 k ∪ dPos2 k) ∪ dNeg1 k) (dNeg2 k) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨disj14 k, disj24 k⟩, disj34 k⟩
  have e_mid : Disjoint (dPos1 k ∪ dPos2 k) (dNeg1 k) :=
    Finset.disjoint_union_left.mpr ⟨disj13 k, disj23 k⟩
  simp only [missD]
  rw [Finset.card_union_of_disjoint e_top, Finset.card_union_of_disjoint e_mid,
    Finset.card_union_of_disjoint (disj12 k), c1, c2, c3, c4]
  omega

private abbrev sGrp1 (k : ℕ) : Finset ℤ :=
  (Finset.range (k - 1)).image (fun i : ℕ => (12 : ℤ) + 4 * (i : ℤ))

private abbrev sGrp2 (k : ℕ) : Finset ℤ :=
  (Finset.range k).image (fun i : ℕ => 4 * (k : ℤ) + 16 + 4 * (i : ℤ))

private abbrev sGrp3 (k : ℕ) : Finset ℤ :=
  (Finset.range (k - 1)).image (fun i : ℕ => 8 * (k : ℤ) + 28 + 4 * (i : ℤ))

private abbrev sGrp4 (k : ℕ) : Finset ℤ :=
  (Finset.range k).image (fun i : ℕ => 12 * (k : ℤ) + 32 + 4 * (i : ℤ))

private abbrev missS0 (k : ℕ) : Finset ℤ := sGrp1 k ∪ sGrp2 k ∪ sGrp3 k ∪ sGrp4 k

private theorem card_missS0 (k : ℕ) (hk : 0 < k) : (missS0 k).card ≤ 4 * k - 2 := by
  have inj1 : Function.Injective (fun i : ℕ => (12 : ℤ) + 4 * (i : ℤ)) := by
    intro i j hij
    have hij' : (12 : ℤ) + 4 * (i : ℤ) = 12 + 4 * (j : ℤ) := hij
    have h : (i : ℤ) = (j : ℤ) := by omega
    exact Int.ofNat_inj.mp h
  have inj2 : Function.Injective (fun i : ℕ => 4 * (k : ℤ) + 16 + 4 * (i : ℤ)) := by
    intro i j hij
    have hij' : 4 * (k : ℤ) + 16 + 4 * (i : ℤ) = 4 * (k : ℤ) + 16 + 4 * (j : ℤ) := hij
    have h : (i : ℤ) = (j : ℤ) := by omega
    exact Int.ofNat_inj.mp h
  have inj3 : Function.Injective (fun i : ℕ => 8 * (k : ℤ) + 28 + 4 * (i : ℤ)) := by
    intro i j hij
    have hij' : 8 * (k : ℤ) + 28 + 4 * (i : ℤ) = 8 * (k : ℤ) + 28 + 4 * (j : ℤ) := hij
    have h : (i : ℤ) = (j : ℤ) := by omega
    exact Int.ofNat_inj.mp h
  have inj4 : Function.Injective (fun i : ℕ => 12 * (k : ℤ) + 32 + 4 * (i : ℤ)) := by
    intro i j hij
    have hij' : 12 * (k : ℤ) + 32 + 4 * (i : ℤ) = 12 * (k : ℤ) + 32 + 4 * (j : ℤ) := hij
    have h : (i : ℤ) = (j : ℤ) := by omega
    exact Int.ofNat_inj.mp h
  have c1 : (sGrp1 k).card = k - 1 := by
    rw [show sGrp1 k
        = (Finset.range (k - 1)).image (fun i : ℕ => (12 : ℤ) + 4 * (i : ℤ)) from rfl,
      Finset.card_image_of_injective _ inj1, Finset.card_range]
  have c2 : (sGrp2 k).card = k := by
    rw [show sGrp2 k
        = (Finset.range k).image (fun i : ℕ => 4 * (k : ℤ) + 16 + 4 * (i : ℤ)) from rfl,
      Finset.card_image_of_injective _ inj2, Finset.card_range]
  have c3 : (sGrp3 k).card = k - 1 := by
    rw [show sGrp3 k
        = (Finset.range (k - 1)).image (fun i : ℕ => 8 * (k : ℤ) + 28 + 4 * (i : ℤ))
      from rfl, Finset.card_image_of_injective _ inj3, Finset.card_range]
  have c4 : (sGrp4 k).card = k := by
    rw [show sGrp4 k
        = (Finset.range k).image (fun i : ℕ => 12 * (k : ℤ) + 32 + 4 * (i : ℤ)) from rfl,
      Finset.card_image_of_injective _ inj4, Finset.card_range]
  simp only [missS0]
  have h1 := Finset.card_union_le ((sGrp1 k ∪ sGrp2 k) ∪ sGrp3 k) (sGrp4 k)
  have h2 := Finset.card_union_le (sGrp1 k ∪ sGrp2 k) (sGrp3 k)
  have h3 := Finset.card_union_le (sGrp1 k) (sGrp2 k)
  omega

private theorem missD_subset_short (k : ℕ) (hk : 0 < k) :
    missD k ⊆ Finset.Icc (-(8 * (k : ℤ) + 20)) (8 * (k : ℤ) + 20) \
      (Ashort k - Ashort k) := by
  intro x hx
  simp only [missD, Finset.mem_union, dPos1, dPos2, dNeg1, dNeg2, Finset.mem_image,
    Finset.mem_range] at hx
  rw [Finset.mem_sdiff, Finset.mem_Icc]
  rcases hx with ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · refine ⟨⟨by omega, by omega⟩, ?_⟩
    exact absent6 k hk (Ashort k) (Ashort_A0 k) (Ashort_A2 k) (Ashort_no3 k) i hi
  · refine ⟨⟨by omega, by omega⟩, ?_⟩
    exact absent8k k hk (Ashort k) (Ashort_A0 k) (Ashort_A2 k) (Ashort_no3 k) i hi
  · refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h := absent6 k hk (Ashort k) (Ashort_A0 k) (Ashort_A2 k) (Ashort_no3 k) i hi
    intro hcon
    have h2 := neg_mem_sub _ _ hcon
    rw [neg_neg] at h2
    exact h h2
  · refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h := absent8k k hk (Ashort k) (Ashort_A0 k) (Ashort_A2 k) (Ashort_no3 k) i hi
    intro hcon
    have h2 := neg_mem_sub _ _ hcon
    rw [neg_neg] at h2
    exact h h2

private theorem missD_subset_long (k : ℕ) (hk : 0 < k) :
    missD k ⊆ Finset.Icc (-(8 * (k : ℤ) + 21)) (8 * (k : ℤ) + 21) \
      (Along k - Along k) := by
  intro x hx
  simp only [missD, Finset.mem_union, dPos1, dPos2, dNeg1, dNeg2, Finset.mem_image,
    Finset.mem_range] at hx
  rw [Finset.mem_sdiff, Finset.mem_Icc]
  rcases hx with ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · refine ⟨⟨by omega, by omega⟩, ?_⟩
    exact absent6 k hk (Along k) (Along_A0 k) (Along_A2 k) (Along_no3 k) i hi
  · refine ⟨⟨by omega, by omega⟩, ?_⟩
    exact absent8k k hk (Along k) (Along_A0 k) (Along_A2 k) (Along_no3 k) i hi
  · refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h := absent6 k hk (Along k) (Along_A0 k) (Along_A2 k) (Along_no3 k) i hi
    intro hcon
    have h2 := neg_mem_sub _ _ hcon
    rw [neg_neg] at h2
    exact h h2
  · refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h := absent8k k hk (Along k) (Along_A0 k) (Along_A2 k) (Along_no3 k) i hi
    intro hcon
    have h2 := neg_mem_sub _ _ hcon
    rw [neg_neg] at h2
    exact h h2

private theorem sub_subset_Icc_short (k : ℕ) (hk : 0 < k) :
    Ashort k - Ashort k ⊆ Finset.Icc (-(8 * (k : ℤ) + 20)) (8 * (k : ℤ) + 20) := by
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hd
  have h1 := Ashort_bounds k hk a ha
  have h2 := Ashort_bounds k hk b hb
  rw [Finset.mem_Icc]
  omega

private theorem sub_subset_Icc_long (k : ℕ) (hk : 0 < k) :
    Along k - Along k ⊆ Finset.Icc (-(8 * (k : ℤ) + 21)) (8 * (k : ℤ) + 21) := by
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hd
  have h1 := Along_bounds k hk a ha
  have h2 := Along_bounds k hk b hb
  rw [Finset.mem_Icc]
  omega

private theorem add_subset_Icc_short (k : ℕ) (hk : 0 < k) :
    Ashort k + Ashort k ⊆ Finset.Icc 0 (2 * (8 * (k : ℤ) + 20)) := by
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
  have h1 := Ashort_bounds k hk a ha
  have h2 := Ashort_bounds k hk b hb
  rw [Finset.mem_Icc]
  omega

private theorem add_subset_Icc_long (k : ℕ) (hk : 0 < k) :
    Along k + Along k ⊆ Finset.Icc 0 (2 * (8 * (k : ℤ) + 21)) := by
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
  have h1 := Along_bounds k hk a ha
  have h2 := Along_bounds k hk b hb
  rw [Finset.mem_Icc]
  omega

private theorem cover_common (k : ℕ) (hk : 0 < k) (A : Finset ℤ)
    (h0 : (0 : ℤ) ∈ A) (h1 : (1 : ℤ) ∈ A) (h2 : (2 : ℤ) ∈ A) (h4 : (4 : ℤ) ∈ A)
    (hA1a : ∀ i : ℤ, 0 ≤ i → i ≤ (k : ℤ) → 5 + 4 * i ∈ A)
    (hK8 : 4 * (k : ℤ) + 8 ∈ A)
    (hA1b : ∀ i : ℤ, 0 ≤ i → i ≤ (k : ℤ) + 1 → 4 * (k : ℤ) + 9 + 4 * i ∈ A)
    (h16 : 8 * (k : ℤ) + 16 ∈ A) (h17 : 8 * (k : ℤ) + 17 ∈ A)
    (h18 : 8 * (k : ℤ) + 18 ∈ A) (h20 : 8 * (k : ℤ) + 20 ∈ A)
    (s : ℤ) (hs0 : 0 ≤ s) (hs1 : s ≤ 16 * (k : ℤ) + 40)
    (hsM : s ∉ missS0 k) (hsP : s ≠ 16 * (k : ℤ) + 39) :
    s ∈ A + A := by
  have add_mem {a b : ℤ} (ha : a ∈ A) (hb : b ∈ A) (h : a + b = s) : s ∈ A + A :=
    h ▸ Finset.add_mem_add ha hb
  have hmod : s % 4 = 0 ∨ s % 4 = 1 ∨ s % 4 = 2 ∨ s % 4 = 3 := by omega
  rcases hmod with hR0 | hR1 | hR2 | hR3
  · -- residue 0
    have hdvd : (4 : ℤ) ∣ s := by omega
    obtain ⟨t, ht⟩ := hdvd
    have ht0 : 0 ≤ t := by omega
    have ht1 : t ≤ 4 * (k : ℤ) + 10 := by omega
    have hG1 : ∀ i : ℕ, i < k - 1 → (12 : ℤ) + 4 * (i : ℤ) ≠ s := by
      intro i hi heq
      apply hsM
      simp only [missS0, Finset.mem_union, sGrp1, sGrp2, sGrp3, sGrp4,
        Finset.mem_image, Finset.mem_range]
      exact Or.inl (Or.inl (Or.inl ⟨i, hi, heq⟩))
    have hG2 : ∀ i : ℕ, i < k → 4 * (k : ℤ) + 16 + 4 * (i : ℤ) ≠ s := by
      intro i hi heq
      apply hsM
      simp only [missS0, Finset.mem_union, sGrp1, sGrp2, sGrp3, sGrp4,
        Finset.mem_image, Finset.mem_range]
      exact Or.inl (Or.inl (Or.inr ⟨i, hi, heq⟩))
    have hG3 : ∀ i : ℕ, i < k - 1 → 8 * (k : ℤ) + 28 + 4 * (i : ℤ) ≠ s := by
      intro i hi heq
      apply hsM
      simp only [missS0, Finset.mem_union, sGrp1, sGrp2, sGrp3, sGrp4,
        Finset.mem_image, Finset.mem_range]
      exact Or.inl (Or.inr ⟨i, hi, heq⟩)
    have hG4 : ∀ i : ℕ, i < k → 12 * (k : ℤ) + 32 + 4 * (i : ℤ) ≠ s := by
      intro i hi heq
      apply hsM
      simp only [missS0, Finset.mem_union, sGrp1, sGrp2, sGrp3, sGrp4,
        Finset.mem_image, Finset.mem_range]
      exact Or.inr ⟨i, hi, heq⟩
    have E1 : t < 3 ∨ (k : ℤ) + 1 < t := by
      by_contra hcon
      have hlo : 3 ≤ t := by omega
      have hhi : t ≤ (k : ℤ) + 1 := by omega
      have hi1 : ((t - 3).toNat : ℤ) = t - 3 := Int.toNat_of_nonneg (by omega)
      have hik : (t - 3).toNat < k - 1 := by omega
      exact hG1 _ hik (by omega)
    have E2 : t < (k : ℤ) + 4 ∨ 2 * (k : ℤ) + 3 < t := by
      by_contra hcon
      have hlo : (k : ℤ) + 4 ≤ t := by omega
      have hhi : t ≤ 2 * (k : ℤ) + 3 := by omega
      have hi1 : ((t - (k : ℤ) - 4).toNat : ℤ) = t - (k : ℤ) - 4 :=
        Int.toNat_of_nonneg (by omega)
      have hik : (t - (k : ℤ) - 4).toNat < k := by omega
      exact hG2 _ hik (by omega)
    have E3 : t < 2 * (k : ℤ) + 7 ∨ 3 * (k : ℤ) + 5 < t := by
      by_contra hcon
      have hlo : 2 * (k : ℤ) + 7 ≤ t := by omega
      have hhi : t ≤ 3 * (k : ℤ) + 5 := by omega
      have hi1 : ((t - 2 * (k : ℤ) - 7).toNat : ℤ) = t - 2 * (k : ℤ) - 7 :=
        Int.toNat_of_nonneg (by omega)
      have hik : (t - 2 * (k : ℤ) - 7).toNat < k - 1 := by omega
      exact hG3 _ hik (by omega)
    have E4 : t < 3 * (k : ℤ) + 8 ∨ 4 * (k : ℤ) + 7 < t := by
      by_contra hcon
      have hlo : 3 * (k : ℤ) + 8 ≤ t := by omega
      have hhi : t ≤ 4 * (k : ℤ) + 7 := by omega
      have hi1 : ((t - 3 * (k : ℤ) - 8).toNat : ℤ) = t - 3 * (k : ℤ) - 8 :=
        Int.toNat_of_nonneg (by omega)
      have hik : (t - 3 * (k : ℤ) - 8).toNat < k := by omega
      exact hG4 _ hik (by omega)
    have hsplit : t ≤ 2 ∨ ((k : ℤ) + 2 ≤ t ∧ t ≤ (k : ℤ) + 3) ∨
        (2 * (k : ℤ) + 4 ≤ t ∧ t ≤ 2 * (k : ℤ) + 6) ∨ (t = 3 * (k : ℤ) + 6 ∨
          t = 3 * (k : ℤ) + 7) ∨ (4 * (k : ℤ) + 8 ≤ t ∧ t ≤ 4 * (k : ℤ) + 10) := by
      omega
    rcases hsplit with h | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | (h | h) | ⟨hlo, hhi⟩
    · have hs3 : s = 0 ∨ s = 4 ∨ s = 8 := by omega
      rcases hs3 with rfl | rfl | rfl
      · exact add_mem h0 h0 (by omega)
      · exact add_mem h0 h4 (by omega)
      · exact add_mem h4 h4 (by omega)
    · have hs2 : 4 * (k : ℤ) + 8 + 0 = s ∨ 4 * (k : ℤ) + 8 + 4 = s := by omega
      rcases hs2 with h | h
      · exact add_mem hK8 h0 h
      · exact add_mem hK8 h4 h
    · have hs3 : 8 * (k : ℤ) + 16 + 0 = s ∨ 8 * (k : ℤ) + 20 + 0 = s ∨
        8 * (k : ℤ) + 20 + 4 = s := by omega
      rcases hs3 with h | h | h
      · exact add_mem h16 h0 h
      · exact add_mem h20 h0 h
      · exact add_mem h20 h4 h
    · have hs1 : (4 * (k : ℤ) + 8) + (8 * (k : ℤ) + 16) = s := by omega
      exact add_mem hK8 h16 hs1
    · have hs1 : (4 * (k : ℤ) + 8) + (8 * (k : ℤ) + 20) = s := by omega
      exact add_mem hK8 h20 hs1
    · have hs3 : (8 * (k : ℤ) + 16) + (8 * (k : ℤ) + 16) = s ∨
        (8 * (k : ℤ) + 16) + (8 * (k : ℤ) + 20) = s ∨
        (8 * (k : ℤ) + 20) + (8 * (k : ℤ) + 20) = s := by omega
      rcases hs3 with h | h | h
      · exact add_mem h16 h16 h
      · exact add_mem h16 h20 h
      · exact add_mem h20 h20 h
  · -- residue 1
    have hsplit : s ≤ 4 * (k : ℤ) + 5 ∨
        (4 * (k : ℤ) + 9 ≤ s ∧ s ≤ 8 * (k : ℤ) + 13) ∨
        (4 * (k : ℤ) + 13 ≤ s ∧ s ≤ 8 * (k : ℤ) + 17) ∨
        (8 * (k : ℤ) + 21 ≤ s ∧ s ≤ 12 * (k : ℤ) + 25) ∨
        (12 * (k : ℤ) + 29 ≤ s ∧ s ≤ 16 * (k : ℤ) + 37) := by omega
    rcases hsplit with h | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · have hs2 : s = 1 ∨ 5 ≤ s := by omega
      rcases hs2 with rfl | hlo5
      · exact add_mem h0 h1 (by omega)
      · have hdvd2 : (4 : ℤ) ∣ s - 5 := by omega
        obtain ⟨i, hi⟩ := hdvd2
        have hi0 : 0 ≤ i := by omega
        have hik : i ≤ (k : ℤ) := by omega
        exact add_mem h0 (hA1a i hi0 hik) (by omega)
    · have hdvd2 : (4 : ℤ) ∣ s - (4 * (k : ℤ) + 9) := by omega
      obtain ⟨i, hi⟩ := hdvd2
      have hi0 : 0 ≤ i := by omega
      have hik : i ≤ (k : ℤ) + 1 := by omega
      exact add_mem h0 (hA1b i hi0 hik) (by omega)
    · have hdvd2 : (4 : ℤ) ∣ s - (4 * (k : ℤ) + 13) := by omega
      obtain ⟨i, hi⟩ := hdvd2
      have hi0 : 0 ≤ i := by omega
      have hik : i ≤ (k : ℤ) + 1 := by omega
      exact add_mem h4 (hA1b i hi0 hik) (by omega)
    · have hsub : s ≤ 12 * (k : ℤ) + 21 ∨ 12 * (k : ℤ) + 25 ≤ s := by omega
      rcases hsub with hle | hge
      · have hdvd2 : (4 : ℤ) ∣ s - (8 * (k : ℤ) + 21) := by omega
        obtain ⟨i, hi⟩ := hdvd2
        have hi0 : 0 ≤ i := by omega
        have hik : i ≤ (k : ℤ) := by omega
        exact add_mem h16 (hA1a i hi0 hik) (by omega)
      · have hseq : s = 12 * (k : ℤ) + 25 := by omega
        have h5K : 5 + 4 * (k : ℤ) ∈ A := hA1a (k : ℤ) (by omega) le_rfl
        exact add_mem h20 h5K (by omega)
    · have hsub : s ≤ 16 * (k : ℤ) + 33 ∨ 16 * (k : ℤ) + 37 ≤ s := by omega
      rcases hsub with hle | hge
      · have hdvd2 : (4 : ℤ) ∣ s - (12 * (k : ℤ) + 29) := by omega
        obtain ⟨i, hi⟩ := hdvd2
        have hi0 : 0 ≤ i := by omega
        have hik : i ≤ (k : ℤ) + 1 := by omega
        exact add_mem h20 (hA1b i hi0 hik) (by omega)
      · have hseq : s = 16 * (k : ℤ) + 37 := by omega
        exact add_mem h20 h17 (by omega)
  · -- residue 2
    have h813 : 8 * (k : ℤ) + 13 ∈ A := by
      have h := hA1b ((k : ℤ) + 1) (by omega) (by omega)
      rwa [show 4 * (k : ℤ) + 9 + 4 * ((k : ℤ) + 1) = 8 * (k : ℤ) + 13 by omega] at h
    have hsplit : s ≤ 4 * (k : ℤ) + 6 ∨
        (4 * (k : ℤ) + 10 ≤ s ∧ s ≤ 8 * (k : ℤ) + 14) ∨
        (4 * (k : ℤ) + 14 ≤ s ∧ s ≤ 12 * (k : ℤ) + 18) ∨
        (12 * (k : ℤ) + 22 ≤ s ∧ s ≤ 16 * (k : ℤ) + 26) ∨
        (16 * (k : ℤ) + 30 ≤ s ∧ s ≤ 16 * (k : ℤ) + 38) := by omega
    rcases hsplit with h | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · have hs2 : s = 2 ∨ 6 ≤ s := by omega
      rcases hs2 with rfl | hlo6
      · exact add_mem h1 h1 (by omega)
      · have hdvd2 : (4 : ℤ) ∣ s - 6 := by omega
        obtain ⟨i, hi⟩ := hdvd2
        have hi0 : 0 ≤ i := by omega
        have hik : i ≤ (k : ℤ) := by omega
        exact add_mem h1 (hA1a i hi0 hik) (by omega)
    · have hdvd2 : (4 : ℤ) ∣ s - (4 * (k : ℤ) + 10) := by omega
      obtain ⟨i, hi⟩ := hdvd2
      have hi0 : 0 ≤ i := by omega
      have hik : i ≤ (k : ℤ) + 1 := by omega
      exact add_mem h1 (hA1b i hi0 hik) (by omega)
    · have hsub : s ≤ 8 * (k : ℤ) + 18 ∨ 8 * (k : ℤ) + 18 ≤ s := le_total _ _
      rcases hsub with hle | hge
      · have hdvd2 : (4 : ℤ) ∣ s - (4 * (k : ℤ) + 14) := by omega
        obtain ⟨i, hi⟩ := hdvd2
        have hi0 : 0 ≤ i := by omega
        have hik : i ≤ (k : ℤ) + 1 := by omega
        have h5 : 5 + 4 * (0 : ℤ) ∈ A := hA1a 0 (by omega) (by omega)
        exact add_mem (hA1b i hi0 hik) h5 (by omega)
      · have hdvd2 : (4 : ℤ) ∣ s - (8 * (k : ℤ) + 18) := by omega
        obtain ⟨i, hi⟩ := hdvd2
        have hi0 : 0 ≤ i := by omega
        have hik : i ≤ (k : ℤ) + 1 := by omega
        have h49 : 4 * (k : ℤ) + 9 + 4 * (0 : ℤ) ∈ A := hA1b 0 (by omega) (by omega)
        exact add_mem (hA1b i hi0 hik) h49 (by omega)
    · have hdvd2 : (4 : ℤ) ∣ s - (12 * (k : ℤ) + 22) := by omega
      obtain ⟨i, hi⟩ := hdvd2
      have hi0 : 0 ≤ i := by omega
      have hik : i ≤ (k : ℤ) + 1 := by omega
      exact add_mem (hA1b i hi0 hik) h813 (by omega)
    · have hs3 : s = 16 * (k : ℤ) + 30 ∨ s = 16 * (k : ℤ) + 34 ∨
        s = 16 * (k : ℤ) + 38 := by omega
      rcases hs3 with rfl | rfl | rfl
      · exact add_mem h17 h813 (by omega)
      · exact add_mem h17 h17 (by omega)
      · exact add_mem h20 h18 (by omega)
  · -- residue 3
    have hsplit : s ≤ 4 * (k : ℤ) + 7 ∨
        (4 * (k : ℤ) + 11 ≤ s ∧ s ≤ 8 * (k : ℤ) + 15) ∨
        (8 * (k : ℤ) + 19 ≤ s ∧ s ≤ 12 * (k : ℤ) + 23) ∨
        (12 * (k : ℤ) + 27 ≤ s ∧ s ≤ 16 * (k : ℤ) + 31) ∨
        16 * (k : ℤ) + 35 ≤ s := by omega
    rcases hsplit with h | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | hge
    · have hs2 : s = 3 ∨ 7 ≤ s := by omega
      rcases hs2 with rfl | hlo7
      · exact add_mem h1 h2 (by omega)
      · have hdvd2 : (4 : ℤ) ∣ s - 7 := by omega
        obtain ⟨i, hi⟩ := hdvd2
        have hi0 : 0 ≤ i := by omega
        have hik : i ≤ (k : ℤ) := by omega
        exact add_mem h2 (hA1a i hi0 hik) (by omega)
    · have hdvd2 : (4 : ℤ) ∣ s - (4 * (k : ℤ) + 11) := by omega
      obtain ⟨i, hi⟩ := hdvd2
      have hi0 : 0 ≤ i := by omega
      have hik : i ≤ (k : ℤ) + 1 := by omega
      exact add_mem h2 (hA1b i hi0 hik) (by omega)
    · have hsub : s = 8 * (k : ℤ) + 19 ∨ 8 * (k : ℤ) + 23 ≤ s := by omega
      rcases hsub with rfl | hge23
      · exact add_mem h1 h18 (by omega)
      · have hdvd2 : (4 : ℤ) ∣ s - (8 * (k : ℤ) + 23) := by omega
        obtain ⟨i, hi⟩ := hdvd2
        have hi0 : 0 ≤ i := by omega
        have hik : i ≤ (k : ℤ) := by omega
        exact add_mem (hA1a i hi0 hik) h18 (by omega)
    · have hdvd2 : (4 : ℤ) ∣ s - (12 * (k : ℤ) + 27) := by omega
      obtain ⟨i, hi⟩ := hdvd2
      have hi0 : 0 ≤ i := by omega
      have hik : i ≤ (k : ℤ) + 1 := by omega
      exact add_mem (hA1b i hi0 hik) h18 (by omega)
    · have hseq : s = 16 * (k : ℤ) + 35 := by omega
      subst hseq
      exact add_mem h17 h18 (by omega)

private theorem assembly_short (k : ℕ) (hk : 0 < k) :
    (Ashort k - Ashort k).card < (Ashort k + Ashort k).card := by
  have hDI := sub_subset_Icc_short k hk
  have hIcard : (Finset.Icc (-(8 * (k : ℤ) + 20)) (8 * (k : ℤ) + 20)).card
      = (2 * (8 * (k : ℤ) + 20) + 1).toNat := by
    rw [Int.card_Icc]
    congr 1
    omega
  have hJcard : (Finset.Icc 0 (2 * (8 * (k : ℤ) + 20))).card
      = (2 * (8 * (k : ℤ) + 20) + 1).toNat := by
    rw [Int.card_Icc]
    congr 1
  have hDge : 4 * k ≤ (Finset.Icc (-(8 * (k : ℤ) + 20)) (8 * (k : ℤ) + 20) \
      (Ashort k - Ashort k)).card := by
    have h := Finset.card_le_card (missD_subset_short k hk)
    rw [card_missD] at h
    exact h
  have hSM : Finset.Icc 0 (2 * (8 * (k : ℤ) + 20)) \ (Ashort k + Ashort k)
      ⊆ missS0 k ∪ {16 * (k : ℤ) + 39} := by
    intro s hs
    obtain ⟨hsJ, hsS⟩ := Finset.mem_sdiff.mp hs
    have hs0 : 0 ≤ s := by
      have h := Finset.mem_Icc.mp hsJ
      omega
    have hs1 : s ≤ 16 * (k : ℤ) + 40 := by
      have h := Finset.mem_Icc.mp hsJ
      omega
    by_cases h1 : s ∈ missS0 k
    · exact Finset.mem_union.mpr (Or.inl h1)
    · by_cases h2 : s = 16 * (k : ℤ) + 39
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr h2))
      · exfalso
        exact hsS (cover_common k hk (Ashort k) (Ashort_mem0 k) (Ashort_mem1 k)
          (Ashort_mem2 k) (Ashort_mem4 k) (Ashort_mem5pZ k) (Ashort_memK8 k)
          (Ashort_mem49pZ k) (Ashort_mem16 k) (Ashort_mem17 k) (Ashort_mem18 k)
          (Ashort_mem20 k) s hs0 hs1 h1 h2)
  have hSle : (Finset.Icc 0 (2 * (8 * (k : ℤ) + 20)) \
      (Ashort k + Ashort k)).card ≤ 4 * k - 1 := by
    have h := Finset.card_le_card hSM
    have hu := Finset.card_union_le (missS0 k) ({16 * (k : ℤ) + 39} : Finset ℤ)
    have hc := card_missS0 k hk
    rw [Finset.card_singleton] at hu
    omega
  have hDD : Disjoint (Ashort k - Ashort k)
      (Finset.Icc (-(8 * (k : ℤ) + 20)) (8 * (k : ℤ) + 20) \
        (Ashort k - Ashort k)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx2).2 hx1
  have hDU : (Ashort k - Ashort k) ∪
      (Finset.Icc (-(8 * (k : ℤ) + 20)) (8 * (k : ℤ) + 20) \
        (Ashort k - Ashort k))
      ⊆ Finset.Icc (-(8 * (k : ℤ) + 20)) (8 * (k : ℤ) + 20) := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hDI h
    · exact (Finset.mem_sdiff.mp h).1
  have hDcard := Finset.card_le_card hDU
  rw [Finset.card_union_of_disjoint hDD] at hDcard
  have hSU : Finset.Icc 0 (2 * (8 * (k : ℤ) + 20)) ⊆ (Ashort k + Ashort k) ∪
      (Finset.Icc 0 (2 * (8 * (k : ℤ) + 20)) \ (Ashort k + Ashort k)) := by
    intro x hx
    by_cases h : x ∈ Ashort k + Ashort k
    · exact Finset.mem_union.mpr (Or.inl h)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, h⟩))
  have hScard : (Finset.Icc 0 (2 * (8 * (k : ℤ) + 20))).card
      ≤ (Ashort k + Ashort k).card
        + (Finset.Icc 0 (2 * (8 * (k : ℤ) + 20)) \
          (Ashort k + Ashort k)).card :=
    le_trans (Finset.card_le_card hSU) (Finset.card_union_le _ _)
  omega

private theorem assembly_long (k : ℕ) (hk : 0 < k) :
    (Along k - Along k).card < (Along k + Along k).card := by
  have hDI := sub_subset_Icc_long k hk
  have hIcard : (Finset.Icc (-(8 * (k : ℤ) + 21)) (8 * (k : ℤ) + 21)).card
      = (2 * (8 * (k : ℤ) + 21) + 1).toNat := by
    rw [Int.card_Icc]
    congr 1
    omega
  have hJcard : (Finset.Icc 0 (2 * (8 * (k : ℤ) + 21))).card
      = (2 * (8 * (k : ℤ) + 21) + 1).toNat := by
    rw [Int.card_Icc]
    congr 1
  have hDge : 4 * k ≤ (Finset.Icc (-(8 * (k : ℤ) + 21)) (8 * (k : ℤ) + 21) \
      (Along k - Along k)).card := by
    have h := Finset.card_le_card (missD_subset_long k hk)
    rw [card_missD] at h
    exact h
  have hSM : Finset.Icc 0 (2 * (8 * (k : ℤ) + 21)) \ (Along k + Along k)
      ⊆ missS0 k := by
    intro s hs
    obtain ⟨hsJ, hsS⟩ := Finset.mem_sdiff.mp hs
    have hs0 : 0 ≤ s := by
      have h := Finset.mem_Icc.mp hsJ
      omega
    have hsJ' : s ≤ 2 * (8 * (k : ℤ) + 21) := by
      have h := Finset.mem_Icc.mp hsJ
      omega
    by_cases h1 : s ∈ missS0 k
    · exact h1
    · exfalso
      by_cases hle : s ≤ 16 * (k : ℤ) + 40
      · by_cases h2 : s = 16 * (k : ℤ) + 39
        · subst h2
          have hmem := Finset.add_mem_add (Along_mem21 k) (Along_mem18 k)
          have heq : (8 * (k : ℤ) + 21) + (8 * (k : ℤ) + 18)
              = 16 * (k : ℤ) + 39 := by omega
          rw [heq] at hmem
          exact hsS hmem
        · exact hsS (cover_common k hk (Along k) (Along_mem0 k) (Along_mem1 k)
            (Along_mem2 k) (Along_mem4 k) (Along_mem5pZ k) (Along_memK8 k)
            (Along_mem49pZ k) (Along_mem16 k) (Along_mem17 k) (Along_mem18 k)
            (Along_mem20 k) s hs0 hle h1 h2)
      · have hs3 : s = 16 * (k : ℤ) + 41 ∨ s = 16 * (k : ℤ) + 42 := by omega
        rcases hs3 with rfl | rfl
        · have hmem := Finset.add_mem_add (Along_mem21 k) (Along_mem20 k)
          have heq : (8 * (k : ℤ) + 21) + (8 * (k : ℤ) + 20)
              = 16 * (k : ℤ) + 41 := by omega
          rw [heq] at hmem
          exact hsS hmem
        · have hmem := Finset.add_mem_add (Along_mem21 k) (Along_mem21 k)
          have heq : (8 * (k : ℤ) + 21) + (8 * (k : ℤ) + 21)
              = 16 * (k : ℤ) + 42 := by omega
          rw [heq] at hmem
          exact hsS hmem
  have hSle : (Finset.Icc 0 (2 * (8 * (k : ℤ) + 21)) \
      (Along k + Along k)).card ≤ 4 * k - 2 := by
    have h := Finset.card_le_card hSM
    have hc := card_missS0 k hk
    omega
  have hDD : Disjoint (Along k - Along k)
      (Finset.Icc (-(8 * (k : ℤ) + 21)) (8 * (k : ℤ) + 21) \
        (Along k - Along k)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx2).2 hx1
  have hDU : (Along k - Along k) ∪
      (Finset.Icc (-(8 * (k : ℤ) + 21)) (8 * (k : ℤ) + 21) \
        (Along k - Along k))
      ⊆ Finset.Icc (-(8 * (k : ℤ) + 21)) (8 * (k : ℤ) + 21) := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hDI h
    · exact (Finset.mem_sdiff.mp h).1
  have hDcard := Finset.card_le_card hDU
  rw [Finset.card_union_of_disjoint hDD] at hDcard
  have hSU : Finset.Icc 0 (2 * (8 * (k : ℤ) + 21)) ⊆ (Along k + Along k) ∪
      (Finset.Icc 0 (2 * (8 * (k : ℤ) + 21)) \ (Along k + Along k)) := by
    intro x hx
    by_cases h : x ∈ Along k + Along k
    · exact Finset.mem_union.mpr (Or.inl h)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, h⟩))
  have hScard : (Finset.Icc 0 (2 * (8 * (k : ℤ) + 21))).card
      ≤ (Along k + Along k).card
        + (Finset.Icc 0 (2 * (8 * (k : ℤ) + 21)) \
          (Along k + Along k)).card :=
    le_trans (Finset.card_le_card hSU) (Finset.card_union_le _ _)
  omega

/-- **MSTD sets with $M^k$ before $M^{k+1}$ (Theorem 3).** Let $k$ be a positive integer, let
$M^n$ denote the block $1, 4, \dots, 4, 3$ with $n$ fours, and let $M_1$ be one of the
sequences $(1, 1, 2)$, $(1, 1, 2, 1)$. Let $A = (0 \mid 1, 1, 2, M^k, M^{k+1}, M_1)$ be the set
of partial sums, starting from $0$, of the concatenated sequence $1, 1, 2, M^k, M^{k+1}, M_1$.
Then $A$ is sum-dominated: $|A - A| < |A + A|$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 3 (`integers-2024-A32-thm-3`). -/
public theorem chu_family_mstd_increasing {k : ℕ} (hk : 0 < k) {M₁ : List ℕ}
    (hM₁ : M₁ = [1, 1, 2] ∨ M₁ = [1, 1, 2, 1]) :
    let A := setOfConsecutiveDifferences 0 ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ M₁)
    (A - A).card < (A + A).card := by
  rcases hM₁ with rfl | rfl
  · change (Ashort k - Ashort k).card < (Ashort k + Ashort k).card
    exact assembly_short k hk
  · change (Along k - Along k).card < (Along k + Along k).card
    exact assembly_long k hk

end

end MetaMathlibExt
