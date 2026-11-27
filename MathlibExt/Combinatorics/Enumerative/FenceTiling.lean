/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Basic
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.EquivFin

/-!
# Fence tilings and strongly restricted permutations

The theorem `fenceTiling_strongPerm_bijection` pairs the left and right slots covered by
each fence to give the bijection between fence tilings and displacement-restricted permutations.
-/

namespace MetaMathlibExt
namespace fenceTiling_strongPerm_bijection

/-- The unique fence joining the left slot of cell `i` to the right slot of cell `j`. -/
private def fence (i j : ℕ) : ℕ × ℕ :=
  if i ≤ j then (2 * i, j - i) else (2 * j + 1, i - j - 1)

private def Covers (f : ℕ × ℕ) (x : ℕ) : Prop :=
  x = f.1 ∨ x = f.1 + 1 + 2 * f.2

private theorem covers_left {i j k : ℕ} : Covers (fence i j) (2 * k) ↔ k = i := by
  unfold Covers fence
  split <;> dsimp <;> omega

private theorem covers_right {i j k : ℕ} : Covers (fence i j) (2 * k + 1) ↔ k = j := by
  unfold Covers fence
  split <;> dsimp <;> omega

private theorem fence_inj {i j k l : ℕ} (h : fence i j = fence k l) : i = k ∧ j = l := by
  have hl : Covers (fence i j) (2 * i) := covers_left.mpr rfl
  have hr : Covers (fence i j) (2 * j + 1) := covers_right.mpr rfl
  rw [h] at hl hr
  exact ⟨covers_left.mp hl, covers_right.mp hr⟩

private theorem exists_cells (f : ℕ × ℕ) : ∃ i j, fence i j = f := by
  obtain ⟨s, g⟩ := f
  by_cases h : s % 2 = 0
  · refine ⟨s / 2, s / 2 + g, ?_⟩
    simp only [fence, ite_eq_left (Nat.le_add_right _ _), Prod.mk.injEq]
    omega
  · refine ⟨s / 2 + g + 1, s / 2, ?_⟩
    rw [fence, ite_eq_right (by omega), Prod.mk.injEq]
    omega

private def Allowed (D : Finset ℤ) (n : ℕ) (f : ℕ × ℕ) : Prop :=
  f.1 + 1 + 2 * f.2 < 2 * n ∧
    ((f.1 % 2 = 0 ∧ (f.2 : ℤ) ∈ D) ∨ (f.1 % 2 = 1 ∧ -(f.2 : ℤ) - 1 ∈ D))

private theorem allowed_fence {D : Finset ℤ} {n i j : ℕ} :
    Allowed D n (fence i j) ↔ i < n ∧ j < n ∧ (j : ℤ) - i ∈ D := by
  unfold Allowed fence
  split <;> rename_i h
  · have hd : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
    simp only [Nat.mul_mod_right, Nat.zero_ne_one, false_and, or_false, true_and, hd]
    rw [← and_assoc]
    exact and_congr_left' (by omega)
  · have hd : -((i - j - 1 : ℕ) : ℤ) - 1 = (j : ℤ) - i := by omega
    have hp : (2 * j + 1) % 2 = 1 := by omega
    simp only [hp, Nat.one_ne_zero, false_and, false_or, true_and, hd]
    rw [← and_assoc]
    exact and_congr_left' (by omega)

private def Agrees (f : ℕ × ℕ) (k l : ℕ) : Prop :=
  (f.1 = 2 * k → (l : ℤ) = k + f.2) ∧
    (f.1 + 1 + 2 * f.2 = 2 * k → (l : ℤ) = k - f.2 - 1)

private theorem agrees_fence {i j k l : ℕ} :
    Agrees (fence i j) k l ↔ (k = i → l = j) := by
  unfold Agrees fence
  split <;> dsimp <;> omega

end fenceTiling_strongPerm_bijection

open fenceTiling_strongPerm_bijection

/-- **Fence tilings and strongly restricted permutations.** Let $D$ be a finite set of integers
and $n$ a natural number. Number the cells of an $n$-board $0, 1, \dots, n-1$ and give cell $i$
a left slot $2i$ and a right slot $2i + 1$. A fence $(s, g)$, with $s$ and $g$ natural numbers,
has teeth in slots $s$ and $s + 1 + 2g$. A tiling is a finite set of fences such that every
fence $(s, g)$ in it satisfies $s + 1 + 2g < 2n$ and either $s$ is even and $g \in D$, or $s$ is
odd and $-g - 1 \in D$, and such that every slot $x < 2n$ is a tooth of exactly one of its
fences. A tiling $t$ and a permutation $\pi$ of $\{0, 1, \dots, n-1\}$ are compatible if for
every cell $i$ and every fence $(s, g) \in t$: if $s = 2i$ then $\pi(i) = i + g$, and if
$s + 1 + 2g = 2i$ then $\pi(i) = i - g - 1$. Then for every tiling $t$ there is exactly one
permutation $\pi$ with $\pi(i) - i \in D$ for all $i$ that is compatible with $t$, and for every
permutation $\pi$ with $\pi(i) - i \in D$ for all $i$ there is exactly one tiling compatible
with $\pi$.

The lemma is due to Edwards and Allen (2015); the fences are $(\tfrac12, g)$-fences.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Lemma 12. -/
public theorem fenceTiling_strongPerm_bijection (D : Finset ℤ) (n : ℕ) :
    let IsTiling := fun t : Finset (ℕ × ℕ) =>
      (∀ f ∈ t, f.1 + 1 + 2 * f.2 < 2 * n ∧
        ((f.1 % 2 = 0 ∧ (f.2 : ℤ) ∈ D) ∨ (f.1 % 2 = 1 ∧ -(f.2 : ℤ) - 1 ∈ D))) ∧
      ∀ x < 2 * n, ∃! f, f ∈ t ∧ (x = f.1 ∨ x = f.1 + 1 + 2 * f.2)
    let Compatible := fun (t : Finset (ℕ × ℕ)) (π : Equiv.Perm (Fin n)) =>
      ∀ i : Fin n, ∀ f ∈ t,
        (f.1 = 2 * (i : ℕ) → ((π i : ℕ) : ℤ) = (i : ℕ) + f.2) ∧
        (f.1 + 1 + 2 * f.2 = 2 * (i : ℕ) → ((π i : ℕ) : ℤ) = (i : ℕ) - f.2 - 1)
    (∀ t, IsTiling t → ∃! π : Equiv.Perm (Fin n),
        (∀ i, ((π i : ℕ) : ℤ) - (i : ℕ) ∈ D) ∧ Compatible t π) ∧
      ∀ π : Equiv.Perm (Fin n), (∀ i, ((π i : ℕ) : ℤ) - (i : ℕ) ∈ D) →
        ∃! t, IsTiling t ∧ Compatible t π := by
  classical
  dsimp only
  constructor
  · rintro t ⟨ha, hc⟩
    change ∀ f ∈ t, Allowed D n f at ha
    change ∀ x < 2 * n, ∃! f, f ∈ t ∧ Covers f x at hc
    have row (i : Fin n) : ∃ j : Fin n, fence i j ∈ t := by
      obtain ⟨f, ⟨hf, hx⟩, _⟩ := hc (2 * i.val) (by omega)
      obtain ⟨k, j, rfl⟩ := exists_cells f
      obtain rfl := covers_left.mp hx
      exact ⟨⟨j, (allowed_fence.mp (ha _ hf)).2.1⟩, hf⟩
    -- The unique fence at each right slot makes the chosen cell map injective.
    choose p hp using row
    have hinj : Function.Injective p := by
      intro i k h
      have he := (hc (2 * (p i).val + 1) (by have := (p i).isLt; omega)).unique
        ⟨hp i, covers_right.mpr rfl⟩ ⟨hp k, covers_right.mpr (congrArg Fin.val h)⟩
      exact Fin.ext (fence_inj he).1
    let π := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj)
    refine ⟨π, ⟨fun i => (allowed_fence.mp (ha _ (hp i))).2.2, ?_⟩, ?_⟩
    · intro i f hf
      obtain ⟨k, j, rfl⟩ := exists_cells f
      apply agrees_fence.mpr
      rintro rfl
      have he := (hc (2 * i.val) (by omega)).unique
        ⟨hp i, covers_left.mpr rfl⟩ ⟨hf, covers_left.mpr rfl⟩
      exact (fence_inj he).2
    · rintro σ ⟨_, hσ⟩
      ext i
      exact agrees_fence.mp (hσ i _ (hp i)) rfl
  · intro π hD
    -- Take one fence for each pair in the graph of the permutation.
    let t := Finset.univ.image (fun i : Fin n => fence i (π i))
    have mem (f : ℕ × ℕ) : f ∈ t ↔ ∃ i : Fin n, fence i (π i) = f := by
      simp [t]
    refine ⟨t, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro f hf
      obtain ⟨i, rfl⟩ := (mem f).mp hf
      exact allowed_fence.mpr ⟨i.isLt, (π i).isLt, hD i⟩
    · intro x hx
      let k : Fin n := ⟨x / 2, by omega⟩
      by_cases he : x % 2 = 0
      · have hxk : x = 2 * k.val := by dsimp [k]; omega
        rw [hxk]
        refine ⟨fence k (π k), ⟨(mem _).mpr ⟨k, rfl⟩, covers_left.mpr rfl⟩, ?_⟩
        rintro f ⟨hf, hcov⟩
        obtain ⟨i, rfl⟩ := (mem f).mp hf
        obtain rfl : k = i := Fin.ext (covers_left.mp hcov)
        rfl
      · have hxk : x = 2 * k.val + 1 := by dsimp [k]; omega
        rw [hxk]
        obtain ⟨j, hj⟩ := π.surjective k
        rw [← hj]
        refine ⟨fence j (π j), ⟨(mem _).mpr ⟨j, rfl⟩, covers_right.mpr rfl⟩, ?_⟩
        rintro f ⟨hf, hcov⟩
        obtain ⟨i, rfl⟩ := (mem f).mp hf
        obtain rfl := π.injective (Fin.ext (covers_right.mp hcov))
        rfl
    · intro k f hf
      obtain ⟨i, rfl⟩ := (mem f).mp hf
      exact agrees_fence.mpr fun h => congrArg (fun a => (π a).val) (Fin.ext h)
    · rintro u ⟨⟨ha, hc⟩, hπ⟩
      have row (i : Fin n) : fence i (π i) ∈ u := by
        obtain ⟨f, ⟨hf, hx⟩, _⟩ := hc (2 * i.val) (by omega)
        obtain ⟨k, j, rfl⟩ := exists_cells f
        obtain rfl := covers_left.mp hx
        rwa [agrees_fence.mp (hπ i _ hf) rfl]
      ext f
      constructor
      · intro hf
        obtain ⟨i, j, rfl⟩ := exists_cells f
        let k : Fin n := ⟨i, (allowed_fence.mp (ha _ hf)).1⟩
        exact (mem _).mpr ⟨k, congrArg (fence i) (agrees_fence.mp (hπ k _ hf) rfl)⟩
      · intro hf
        obtain ⟨i, rfl⟩ := (mem f).mp hf
        exact row i

end MetaMathlibExt
