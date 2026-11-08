/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# Bloom filters

A Bloom filter over `α` is a bit vector of length `m` together with a list of hash functions
`α → Fin m`, following the presentation in La Rocca, *Advanced Algorithms and Data Structures*,
Chapter 4. Inserting an element sets the bit selected by every hash function, and `mayContain`
reports whether all of those bits are set.

## Main definitions

* `BloomFilter` packages the hash functions with the bit vector.
* `BloomFilter.empty`, `BloomFilter.insert`, and `BloomFilter.mayContain` are the operations.

## Main statements

Bits are only ever set, never cleared, so membership answers have no false negatives:
`mayContain_insert_self` and the monotonicity statement `mayContain_insert_mono`. The exact set
of bits set after an insertion is `bit_insert_iff`. No false-positive probability is claimed:
the model supplies no distribution on elements or hashes.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

/--
A Bloom filter over `α` with `m` bits: a list of hash functions into `Fin m` and the bit vector.
No false-positive rate is claimed because the model supplies no probability distribution.
-/
public structure BloomFilter (α : Type u) (m : Nat) where
  /-- The hash functions; bit `h x` is set when `x` is inserted, for each `h` in the list. -/
  hashes : List (α → Fin m)
  /-- The bit vector. Bits start unset and are only ever set. -/
  bits : Vector Bool m

namespace BloomFilter

/-- The empty Bloom filter for the given hash functions: every bit is unset. -/
public def empty {α : Type u} {m : Nat} (hashes : List (α → Fin m)) : BloomFilter α m where
  hashes := hashes
  bits := Vector.replicate m false

/-- Inserts an element by setting the bit selected by each hash function. -/
public def insert {α : Type u} {m : Nat} (filter : BloomFilter α m) (x : α) :
    BloomFilter α m where
  hashes := filter.hashes
  bits := filter.hashes.foldl (fun bits h => bits.set (h x) true) filter.bits

/-- Whether every bit selected for `x` is set, so `x` may have been inserted. -/
public def mayContain {α : Type u} {m : Nat} (filter : BloomFilter α m) (x : α) : Bool :=
  filter.hashes.all fun h => filter.bits[h x]

private theorem foldl_set_get_iff {α : Type u} {m : Nat} :
    ∀ (hashes : List (α → Fin m)) (bits : Vector Bool m) (x : α) (i : Fin m),
      (hashes.foldl (fun bits h => bits.set (h x) true) bits)[i] = true ↔
        bits[i] = true ∨ ∃ h ∈ hashes, h x = i
  | [], bits, _, _ => by simp
  | h :: hashes, bits, x, i => by
      rw [List.foldl_cons, foldl_set_get_iff hashes (bits.set (h x) true) x i]
      by_cases hi : h x = i
      · subst i
        simp
      · have hget : (bits.set (h x) true)[i] = bits[i] :=
          Vector.getElem_set_ne (h x).isLt i.isLt (Fin.val_ne_of_ne hi)
        rw [hget]
        constructor
        · rintro (hbit | ⟨h', hmem, rfl⟩)
          · exact Or.inl hbit
          · exact Or.inr ⟨h', List.mem_cons_of_mem h hmem, rfl⟩
        · rintro (hbit | ⟨h', hmem, rfl⟩)
          · exact Or.inl hbit
          · rcases List.mem_cons.mp hmem with rfl | hmem
            · exact absurd rfl hi
            · exact Or.inr ⟨h', hmem, rfl⟩

/--
Bit-set characterization of insertion: after inserting `x`, bit `i` is set exactly when it was
already set or some hash function sends `x` to `i`.
-/
public theorem bit_insert_iff {α : Type u} {m : Nat} (filter : BloomFilter α m)
    (x : α) (i : Fin m) :
    (filter.insert x).bits[i] = true ↔
      filter.bits[i] = true ∨ ∃ h ∈ filter.hashes, h x = i :=
  foldl_set_get_iff filter.hashes filter.bits x i

/-- `mayContain` holds exactly when every hash-selected bit is set. -/
public theorem mayContain_iff {α : Type u} {m : Nat} (filter : BloomFilter α m) (x : α) :
    filter.mayContain x = true ↔ ∀ h ∈ filter.hashes, filter.bits[h x] = true := by
  simp [mayContain, List.all_eq_true]

/-- No false negatives: an element is reported present immediately after its own insertion. -/
public theorem mayContain_insert_self {α : Type u} {m : Nat} (filter : BloomFilter α m)
    (x : α) : (filter.insert x).mayContain x = true := by
  rw [mayContain_iff]
  intro h hmem
  rw [bit_insert_iff]
  exact Or.inr ⟨h, hmem, rfl⟩

/--
No false negatives under further inserts: insertion never clears a bit, so an element reported
present stays reported present after any later insertion.
-/
public theorem mayContain_insert_mono {α : Type u} {m : Nat} (filter : BloomFilter α m)
    (x y : α) (present : filter.mayContain x = true) :
    (filter.insert y).mayContain x = true := by
  rw [mayContain_iff] at present ⊢
  intro h hmem
  rw [bit_insert_iff]
  exact Or.inl (present h hmem)

/-- With at least one hash function, the empty filter reports every element absent. -/
public theorem mayContain_empty {α : Type u} {m : Nat} {hashes : List (α → Fin m)}
    (nonempty : hashes ≠ []) (x : α) :
    (empty hashes).mayContain x = false := by
  rcases hashes with _ | ⟨h, hashes⟩
  · exact absurd rfl nonempty
  · simp [mayContain, empty, List.all_cons]

end BloomFilter

end Cslib.Algorithms.Lean
