/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.MergeState

/-!
# Hinted galloping searches

These definitions transcribe CPython's separate `gallop_left` and
`gallop_right` routines.  Keeping the routines separate makes their deliberate
equality asymmetry, and the order of every comparator call, visible.

The searched run starts at the signed index `base`.  Invalid assertion inputs,
failed bounds checks, and failure of the doubling assertion return `none`.
Fuel exhaustion is represented separately in the successful result.
-/

namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Explicit `Option` sequencing used by the gallop transcription.  It is
public so the traced safety evaluator can prove erasure without duplicating
the transcription's control-flow equations. -/
def gallopBindOptionAcross {α : Type w} {β : Type x}
    (value : Option α) (next : α → Option β) : Option β :=
  match value with
  | none => none
  | some value => next value

/-- Observable result of either galloping search. -/
structure GallopResult where
  index : Nat
  fuelExhausted : Bool
  deriving DecidableEq, Repr

/-- Intermediate offsets produced by a gallop's exponential-search phase. -/
structure ExponentialResult where
  lastOffset : Nat
  offset : Nat
  fuelExhausted : Bool

/-! ## `gallop_left` exponential phase -/

/-- The `a[hint] < key` branch of `gallop_left`, probing to the right. -/
def gallopLeftRightExponential? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → κ → Nat → Nat → Nat → Nat →
      Option ExponentialResult
  | 0, _, _, _, _, _, maxOffset, lastOffset, offset =>
      some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, slice, base, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        gallopBindOptionAcross
            (slice.read? (base + Int.ofNat hint + Int.ofNat offset)) fun entry =>
          if iflt lt entry.key key then
            if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
              gallopLeftRightExponential? fuel lt slice base key hint maxOffset
                offset (2 * offset + 1)
            else
              none
          else
            some { lastOffset := lastOffset, offset := offset, fuelExhausted := false }
      else
        some { lastOffset := lastOffset, offset := offset, fuelExhausted := false }

/-- The `key ≤ a[hint]` branch of `gallop_left`, probing to the left. -/
def gallopLeftLeftExponential? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → κ → Nat → Nat → Nat → Nat →
      Option ExponentialResult
  | 0, _, _, _, _, _, maxOffset, lastOffset, offset =>
      some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, slice, base, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        gallopBindOptionAcross
            (slice.read? (base + Int.ofNat hint - Int.ofNat offset)) fun entry =>
          if iflt lt entry.key key then
            some { lastOffset := lastOffset, offset := offset, fuelExhausted := false }
          else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
            gallopLeftLeftExponential? fuel lt slice base key hint maxOffset
              offset (2 * offset + 1)
          else
            none
      else
        some { lastOffset := lastOffset, offset := offset, fuelExhausted := false }

/-- Finishing lower-bound binary search for `gallop_left`. -/
def gallopLeftBinary? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → κ → Nat → Nat →
      Option GallopResult
  | 0, _, _, _, _, lower, upper =>
      some { index := lower, fuelExhausted := decide (lower < upper) }
  | fuel + 1, lt, slice, base, key, lower, upper =>
      if lower < upper then
        let middle := lower + (upper - lower) / 2
        gallopBindOptionAcross (slice.read? (base + Int.ofNat middle)) fun entry =>
          if iflt lt entry.key key then
            gallopLeftBinary? fuel lt slice base key (middle + 1) upper
          else
            gallopLeftBinary? fuel lt slice base key lower middle
      else
        some { index := upper, fuelExhausted := false }

def finishGallopLeft? (fuel : Nat) (lt : BoolComparator κ)
    (slice : SortSlice κ ν) (base : Int) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exponentialFuelExhausted : Bool) :
    Option GallopResult :=
  if -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n then
    let lowerOffset := lastOffset + 1
    if 0 ≤ lowerOffset ∧ 0 ≤ upperOffset then
      let lower := lowerOffset.toNat
      let upper := upperOffset.toNat
      if exponentialFuelExhausted then
        some { index := lower, fuelExhausted := true }
      else
        gallopLeftBinary? fuel lt slice base key lower upper
    else
      none
  else
    none

/-! ## `gallop_right` exponential phase -/

/-- The `key < a[hint]` branch of `gallop_right`, probing to the left. -/
def gallopRightLeftExponential? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → κ → Nat → Nat → Nat → Nat →
      Option ExponentialResult
  | 0, _, _, _, _, _, maxOffset, lastOffset, offset =>
      some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, slice, base, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        gallopBindOptionAcross
            (slice.read? (base + Int.ofNat hint - Int.ofNat offset)) fun entry =>
          if iflt lt key entry.key then
            if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
              gallopRightLeftExponential? fuel lt slice base key hint maxOffset
                offset (2 * offset + 1)
            else
              none
          else
            some { lastOffset := lastOffset, offset := offset, fuelExhausted := false }
      else
        some { lastOffset := lastOffset, offset := offset, fuelExhausted := false }

/-- The `a[hint] ≤ key` branch of `gallop_right`, probing to the right. -/
def gallopRightRightExponential? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → κ → Nat → Nat → Nat → Nat →
      Option ExponentialResult
  | 0, _, _, _, _, _, maxOffset, lastOffset, offset =>
      some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, slice, base, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        gallopBindOptionAcross
            (slice.read? (base + Int.ofNat hint + Int.ofNat offset)) fun entry =>
          if iflt lt key entry.key then
            some { lastOffset := lastOffset, offset := offset, fuelExhausted := false }
          else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
            gallopRightRightExponential? fuel lt slice base key hint maxOffset
              offset (2 * offset + 1)
          else
            none
      else
        some { lastOffset := lastOffset, offset := offset, fuelExhausted := false }

/-- Finishing upper-bound binary search for `gallop_right`. -/
def gallopRightBinary? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → κ → Nat → Nat →
      Option GallopResult
  | 0, _, _, _, _, lower, upper =>
      some { index := lower, fuelExhausted := decide (lower < upper) }
  | fuel + 1, lt, slice, base, key, lower, upper =>
      if lower < upper then
        let middle := lower + (upper - lower) / 2
        gallopBindOptionAcross (slice.read? (base + Int.ofNat middle)) fun entry =>
          if iflt lt key entry.key then
            gallopRightBinary? fuel lt slice base key lower middle
          else
            gallopRightBinary? fuel lt slice base key (middle + 1) upper
      else
        some { index := upper, fuelExhausted := false }

def finishGallopRight? (fuel : Nat) (lt : BoolComparator κ)
    (slice : SortSlice κ ν) (base : Int) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exponentialFuelExhausted : Bool) :
    Option GallopResult :=
  if -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n then
    let lowerOffset := lastOffset + 1
    if 0 ≤ lowerOffset ∧ 0 ≤ upperOffset then
      let lower := lowerOffset.toNat
      let upper := upperOffset.toNat
      if exponentialFuelExhausted then
        some { index := lower, fuelExhausted := true }
      else
        gallopRightBinary? fuel lt slice base key lower upper
    else
      none
  else
    none

/-! ## Public transcriptions -/

/--
Transcription of CPython's `gallop_left`.  Equal keys take the left branch in
both search phases, so the returned position is before the leftmost equal key.
-/
def gallopLeft? (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (key : κ) (n hint : Nat) : Option GallopResult :=
  if 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX then
    gallopBindOptionAcross (slice.read? (base + Int.ofNat hint)) fun hinted =>
      if iflt state.key_compare hinted.key key then do
        let maxOffset := n - hint
        let exponential ← gallopLeftRightExponential? (n + 1) state.key_compare
          slice base key hint maxOffset 0 1
        let offset := min exponential.offset maxOffset
        finishGallopLeft? (n + 1) state.key_compare slice base key n
          (Int.ofNat exponential.lastOffset + Int.ofNat hint)
          (Int.ofNat offset + Int.ofNat hint)
          exponential.fuelExhausted
      else do
        let maxOffset := hint + 1
        let exponential ← gallopLeftLeftExponential? (n + 1) state.key_compare
          slice base key hint maxOffset 0 1
        let offset := min exponential.offset maxOffset
        finishGallopLeft? (n + 1) state.key_compare slice base key n
          (Int.ofNat hint - Int.ofNat offset)
          (Int.ofNat hint - Int.ofNat exponential.lastOffset)
          exponential.fuelExhausted
  else
    none

/--
Transcription of CPython's `gallop_right`.  Equal keys take the right branch in
both search phases, so the returned position is after the rightmost equal key.
-/
def gallopRight? (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (key : κ) (n hint : Nat) : Option GallopResult :=
  if 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX then
    gallopBindOptionAcross (slice.read? (base + Int.ofNat hint)) fun hinted =>
      if iflt state.key_compare key hinted.key then do
        let maxOffset := hint + 1
        let exponential ← gallopRightLeftExponential? (n + 1) state.key_compare
          slice base key hint maxOffset 0 1
        let offset := min exponential.offset maxOffset
        finishGallopRight? (n + 1) state.key_compare slice base key n
          (Int.ofNat hint - Int.ofNat offset)
          (Int.ofNat hint - Int.ofNat exponential.lastOffset)
          exponential.fuelExhausted
      else do
        let maxOffset := n - hint
        let exponential ← gallopRightRightExponential? (n + 1) state.key_compare
          slice base key hint maxOffset 0 1
        let offset := min exponential.offset maxOffset
        finishGallopRight? (n + 1) state.key_compare slice base key n
          (Int.ofNat exponential.lastOffset + Int.ofNat hint)
          (Int.ofNat offset + Int.ofNat hint)
          exponential.fuelExhausted
  else
    none

end CPythonListsort
