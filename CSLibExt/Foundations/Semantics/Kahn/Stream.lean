/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Seq.Defs
public import Mathlib.Order.BoundedOrder.Basic

/-!
# Kahn streams and the prefix order

A stream is a finite or countably infinite sequence of values. It carries the prefix order:
every defined entry of the shorter stream must agree with the entry at the same position in
the extending stream. The empty stream is least. The elements themselves need no order.

See Gilles Kahn, *The semantics of a simple language for parallel programming*, IFIP Congress
74 (1974), §2.2.2. For the chain continuity of §2.2.4, use Mathlib's `ωScottContinuous`: it
preserves suprema of increasing countable chains and implies monotonicity. The construction
of chain suprema for streams and the interpretation of networks are separate from this order.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Foundations.Semantics.Kahn

/-- Finite or countably infinite streams, tagged for the prefix order. The underlying type
is Mathlib's `Stream'.Seq`, so termination excludes any later defined entries. -/
def Stream (α : Type*) := Stream'.Seq α

namespace Stream

variable {α : Type*}

/-- The value at position `n`, or `none` past the end of a finite stream. -/
def get? (s : Stream α) (n : ℕ) : Option α := Stream'.Seq.get? s n

/-- Embed a finite list into the stream domain. -/
def ofList (xs : List α) : Stream α := Stream'.Seq.ofList xs

/-- Embed a countably infinite sequence into the stream domain. -/
def ofStream (xs : Stream' α) : Stream α := Stream'.Seq.ofStream xs

@[simp]
theorem get?_ofList (xs : List α) (n : ℕ) : (ofList xs).get? n = xs[n]? := rfl

@[simp]
theorem get?_ofStream (xs : Stream' α) (n : ℕ) : (ofStream xs).get? n = some (xs n) := rfl

@[ext]
theorem ext {s t : Stream α} (h : ∀ n, s.get? n = t.get? n) : s = t :=
  Stream'.Seq.ext h

/-- **Stream prefix.** A stream `s` is a prefix of `t` if every defined entry of `s` is
present and equal at the same position in `t`. There is no restriction at positions where
`s` has already ended. -/
def IsPrefix (s t : Stream α) : Prop := ∀ n a, s.get? n = some a → t.get? n = some a

instance : PartialOrder (Stream α) where
  le := IsPrefix
  le_refl _ _ _ h := h
  le_trans _ _ _ hst htu n a ha := htu n a (hst n a ha)
  le_antisymm s t hst hts := by
    apply ext
    intro n
    cases hs : s.get? n with
    | some a => exact (hst n a hs).symm
    | none =>
        cases ht : t.get? n with
        | none => rfl
        | some a => rw [hts n a ht] at hs; contradiction

/-- The order compares positions defined in the left-hand stream. -/
theorem le_iff_get? {s t : Stream α} :
    s ≤ t ↔ ∀ n a, s.get? n = some a → t.get? n = some a := Iff.rfl

instance : OrderBot (Stream α) where
  bot := Stream'.Seq.nil
  bot_le _ _ _ h := by cases h

@[simp]
theorem get?_bot (n : ℕ) : (⊥ : Stream α).get? n = none := rfl

@[simp]
theorem ofList_nil : ofList ([] : List α) = ⊥ := rfl

/-- **Finite prefixes.** The stream order on embedded lists is exactly the list prefix
relation, not the subsequence relation. -/
@[simp]
theorem ofList_le_ofList_iff {xs ys : List α} : ofList xs ≤ ofList ys ↔ xs <+: ys := by
  rw [le_iff_get?, List.prefix_iff_getElem?]
  simp only [get?_ofList]
  constructor
  · intro h i hi
    exact h i xs[i] (List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩)
  · intro h i a ha
    obtain ⟨hi, hia⟩ := List.getElem?_eq_some_iff.mp ha
    rw [h i hi, hia]

/-- An infinite stream has no strict extension, since every position is already defined. -/
theorem eq_of_ofStream_le {xs : Stream' α} {t : Stream α} (h : ofStream xs ≤ t) :
    ofStream xs = t := by
  apply ext
  intro n
  exact ((le_iff_get?.mp h) n (xs n) rfl).symm

end Stream
end Cslib.Foundations.Semantics.Kahn
