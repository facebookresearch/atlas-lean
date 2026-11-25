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
**Bloom filter.** A Bloom filter over a type $\alpha$ with $m$ bits consists of a finite list of
hash functions $\alpha \to \{0, \dots, m - 1\}$ and a bit vector of length $m$.

No false-positive rate is claimed because the model supplies no probability distribution.
-/
public structure BloomFilter (α : Type u) (m : Nat) where
  /-- The hash functions; bit `h x` is set when `x` is inserted, for each `h` in the list. -/
  hashes : List (α → Fin m)
  /-- The bit vector. Bits start unset and are only ever set. -/
  bits : Vector Bool m

namespace BloomFilter

/--
**Empty Bloom filter.** Let $\alpha$ be a type and $m$ a natural number. Given a list of hash
functions $\alpha \to \{0, \dots, m - 1\}$, the empty Bloom filter with these hash functions has
all of its $m$ bits unset.
-/
public def empty {α : Type u} {m : Nat} (hashes : List (α → Fin m)) : BloomFilter α m where
  hashes := hashes
  bits := Vector.replicate m false

/--
**Bloom filter insertion.** Inserting an element $x$ into a Bloom filter keeps its hash functions
and sets bit $h(x)$ for every hash function $h$ of the filter, leaving all other bits unchanged.
-/
public def insert {α : Type u} {m : Nat} (filter : BloomFilter α m) (x : α) :
    BloomFilter α m where
  hashes := filter.hashes
  bits := filter.hashes.foldl (fun bits h => bits.set (h x) true) filter.bits

/--
**Bloom filter membership query.** A Bloom filter reports that an element $x$ may be present
when bit $h(x)$ is set for every hash function $h$ of the filter, and reports $x$ absent
otherwise.
-/
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
**Bits set by an insertion.** Let $F$ be a Bloom filter over $\alpha$ with $m$ bits, let
$x \in \alpha$ and let $i \in \{0, \dots, m - 1\}$. Bit $i$ of the filter obtained by inserting
$x$ into $F$ is set if and only if bit $i$ of $F$ is set or some hash function $h$ of $F$
satisfies $h(x) = i$.
-/
public theorem bit_insert_iff {α : Type u} {m : Nat} (filter : BloomFilter α m)
    (x : α) (i : Fin m) :
    (filter.insert x).bits[i] = true ↔
      filter.bits[i] = true ∨ ∃ h ∈ filter.hashes, h x = i :=
  foldl_set_get_iff filter.hashes filter.bits x i

/--
**Membership query in terms of bits.** For a Bloom filter $F$ and an element $x$, $F$ reports
that $x$ may be present if and only if bit $h(x)$ of $F$ is set for every hash function $h$ of
$F$.
-/
public theorem mayContain_iff {α : Type u} {m : Nat} (filter : BloomFilter α m) (x : α) :
    filter.mayContain x = true ↔ ∀ h ∈ filter.hashes, filter.bits[h x] = true := by
  simp [mayContain, List.all_eq_true]

/--
**An inserted element is reported present.** For every Bloom filter $F$ and element $x$, the
filter obtained by inserting $x$ into $F$ reports that $x$ may be present.
-/
public theorem mayContain_insert_self {α : Type u} {m : Nat} (filter : BloomFilter α m)
    (x : α) : (filter.insert x).mayContain x = true := by
  rw [mayContain_iff]
  intro h hmem
  rw [bit_insert_iff]
  exact Or.inr ⟨h, hmem, rfl⟩

/--
**Insertion preserves positive answers.** Let $F$ be a Bloom filter and let $x$, $y$ be elements.
If $F$ reports that $x$ may be present, then so does the filter obtained by inserting $y$ into $F$.

Insertion never clears a bit, so an element reported present stays reported present after any
later insertion; in particular there are no false negatives under further inserts.
-/
public theorem mayContain_insert_mono {α : Type u} {m : Nat} (filter : BloomFilter α m)
    (x y : α) (present : filter.mayContain x = true) :
    (filter.insert y).mayContain x = true := by
  rw [mayContain_iff] at present ⊢
  intro h hmem
  rw [bit_insert_iff]
  exact Or.inl (present h hmem)

/-- **The empty Bloom filter reports every element absent.** Let $\alpha$ be a type, $m$ a
natural number and $H$ a nonempty list of hash functions $\alpha \to \{0, \dots, m - 1\}$. For
every element $x \in \alpha$, the empty Bloom filter with hash functions $H$ reports $x$ absent. -/
public theorem mayContain_empty {α : Type u} {m : Nat} {hashes : List (α → Fin m)}
    (nonempty : hashes ≠ []) (x : α) :
    (empty hashes).mayContain x = false := by
  rcases hashes with _ | ⟨h, hashes⟩
  · exact absurd rfl nonempty
  · simp [mayContain, empty, List.all_cons]

end BloomFilter

end Cslib.Algorithms.Lean
