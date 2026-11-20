/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.MergeState

/-!
# Stable binary insertion transcription

Invalid inputs from C's assertion domain and failed modeled array accesses
return `none`.  Fuel exhaustion remains distinct.  A comparator-false result
(including equality for a strict comparator) follows the right-hand branch of
the binary search; stability is therefore obtained for strict comparators.
-/

namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- `Option.bind` written as the explicit source-order combinator used by the
binarysort transcription.  This is public so the traced assembly evaluator can
state and prove exact erasure without referring to a private generated name. -/
def binarysortBindOptionAcross {α : Type w} {β : Type x}
    (value : Option α) (next : α → Option β) : Option β :=
  match value with
  | none => none
  | some value => next value

/-- Result of the fuel-bounded binary-search phase of `binarysort`. -/
structure BinarySearchResult where
  position : Nat
  fuelExhausted : Bool

/-- Fuel-bounded binary-search phase of `binarysort`, exported for exact traced
erasure and safety proofs. -/
def binarysortSearch? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → SortSliceEntry κ ν →
      Nat → Nat → Option BinarySearchResult
  | 0, _, _, _, _, left, right =>
      some { position := left, fuelExhausted := decide (left < right) }
  | fuel + 1, lt, slice, base, pivot, left, right =>
      if left < right then
        let middle := (left + right) / 2
        binarysortBindOptionAcross (slice.read? (base + Int.ofNat middle)) fun entry =>
          if iflt lt pivot.key entry.key then
            binarysortSearch? fuel lt slice base pivot left middle
          else
            binarysortSearch? fuel lt slice base pivot (middle + 1) right
      else
        some { position := left, fuelExhausted := false }

structure BinarysortResult (κ : Type u) (ν : Type v) where
  slice : SortSlice κ ν
  fuelExhausted : Bool
  deriving DecidableEq, Repr

/-- Fuel-bounded outer insertion loop, exported for exact traced erasure and
safety proofs. -/
def binarysortLoop? :
    Nat → MergeState κ ν → SortSlice κ ν → Int → Nat → Nat →
      Option (BinarysortResult κ ν)
  | 0, _, slice, _, n, ok =>
      some { slice := slice, fuelExhausted := decide (ok < n) }
  | fuel + 1, state, slice, base, n, ok =>
      if ok < n then
        binarysortBindOptionAcross (slice.read? (base + Int.ofNat ok)) fun pivot =>
          binarysortBindOptionAcross
              (binarysortSearch? (ok + 1) state.key_compare slice base pivot 0 ok)
              fun search =>
            if search.fuelExhausted then
              some { slice := slice, fuelExhausted := true }
            else do
              let count := ok - search.position
              let slice ← slice.memmove?
                (base + Int.ofNat (search.position + 1))
                (base + Int.ofNat search.position) count
              let slice ← slice.write? (base + Int.ofNat search.position) pivot
              binarysortLoop? fuel state slice base n (ok + 1)
      else
        some { slice := slice, fuelExhausted := false }

/-- Transcription of CPython's stable binary insertion sort. -/
def binarysort? (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (n ok : Nat) : Option (BinarysortResult κ ν) :=
  if 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat then
    let ok := if ok = 0 then 1 else ok
    binarysortLoop? n state slice base n ok
  else
    none

end CPythonListsort
