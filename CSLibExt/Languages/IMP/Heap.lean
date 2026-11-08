/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite heaps for separation logic over IMP
-/
module

public import Mathlib.Data.Finmap

/-!
# Finite heaps

A heap is a finite partial map from addresses (`Nat`) to values (`Nat`),
reusing Mathlib's `Finmap`. Membership `a ∈ h` means that the address `a`
is allocated in `h`, and `h.lookup a` returns its stored value, if any.

Heap union is `Finmap`'s left-biased key union: on overlapping addresses
the left heap wins. On disjoint heaps the union is commutative
(`Finmap.union_comm_of_disjoint`), which is the form separation logic uses.
Union algebra is used directly from `Finmap`; this file adds only the
heap-specific disjointness and update lemmas the union API lacks.
-/

@[expose] public section

namespace Cslib.IMP

/-- A heap is a finite partial map from addresses to values. -/
abbrev Heap := Finmap (fun _ : Nat => Nat)

namespace Heap

/-- Two heaps are disjoint when no address is allocated in both. -/
def Disjoint (h₁ h₂ : Heap) : Prop := ∀ a, a ∈ h₁ → a ∉ h₂

/-- Disjointness of heaps is symmetric. -/
@[symm]
theorem Disjoint.symm {h₁ h₂ : Heap} (h : Disjoint h₁ h₂) : Disjoint h₂ h₁ :=
  fun _a ha2 ha1 => h _a ha1 ha2

/-- The empty heap is disjoint from every heap on the left. -/
theorem disjoint_empty_left (h : Heap) : Disjoint ∅ h :=
  fun _ ha => absurd ha Finmap.notMem_empty

/-- The empty heap is disjoint from every heap on the right. -/
theorem disjoint_empty_right (h : Heap) : Disjoint h ∅ :=
  fun _ _ => Finmap.notMem_empty

/-- Erasing an address absent from the right component erases on the left. -/
theorem erase_union_of_notMem {a : Nat} {h₁ h₂ : Heap} (ha : a ∉ h₂) :
    Finmap.erase a (h₁ ∪ h₂) = Finmap.erase a h₁ ∪ h₂ := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = a
  · subst hx
    rw [Finmap.lookup_erase, Finmap.lookup_union_right Finmap.notMem_erase_self,
      Finmap.lookup_eq_none.mpr ha]
  · rw [Finmap.lookup_erase_ne hx]
    by_cases hx1 : x ∈ Finmap.erase a h₁
    · have hx1' : x ∈ h₁ := (Finmap.mem_erase.mp hx1).2
      rw [Finmap.lookup_union_left hx1, Finmap.lookup_union_left hx1',
        Finmap.lookup_erase_ne hx]
    · rw [Finmap.lookup_union_right hx1]
      by_cases hx1' : x ∈ h₁
      · exact absurd (Finmap.mem_erase.mpr ⟨hx, hx1'⟩) hx1
      · rw [Finmap.lookup_union_right hx1']

/-- Insertion on the left preserves disjointness at a fresh address. -/
theorem disjoint_insert_left {h₁ h₂ : Heap} {a v : Nat}
    (hd : Disjoint h₁ h₂) (ha : a ∉ h₂) : Disjoint (Finmap.insert a v h₁) h₂ := by
  intro x hx
  rw [Finmap.mem_insert] at hx
  rcases hx with rfl | hx
  · exact ha
  · exact hd x hx

/-- Erasure on the left preserves disjointness. -/
theorem disjoint_erase_left {h₁ h₂ : Heap} {a : Nat}
    (hd : Disjoint h₁ h₂) : Disjoint (Finmap.erase a h₁) h₂ :=
  fun x hx => hd x (Finmap.mem_erase.mp hx).2

/-- A singleton heap is disjoint from a heap iff its address is unallocated. -/
theorem disjoint_singleton_left {a v : Nat} {h : Heap} :
    Disjoint (Finmap.singleton a v) h ↔ a ∉ h := by
  constructor
  · intro hd
    apply hd a
    rw [Finmap.mem_singleton]
  · intro ha x hx
    rw [Finmap.mem_singleton] at hx
    subst hx
    exact ha

/-- Reinserting the stored value after erasure restores the heap. -/
theorem insert_erase_eq_self {h : Heap} {a v : Nat} (hv : h.lookup a = some v) :
    Finmap.insert a v (Finmap.erase a h) = h := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = a
  · subst hx
    rw [Finmap.lookup_insert, hv]
  · rw [Finmap.lookup_insert_of_ne _ hx, Finmap.lookup_erase_ne hx]

/-- Every heap leaves some address unallocated. -/
theorem exists_notMem (h : Heap) : ∃ a, a ∉ h := by
  refine ⟨h.keys.sup id + 1, ?_⟩
  intro hh
  have hle := Finset.le_sup (s := h.keys) (f := id) (Finmap.mem_keys.mpr hh)
  simp only [id_eq] at hle
  omega

end Heap

end Cslib.IMP
