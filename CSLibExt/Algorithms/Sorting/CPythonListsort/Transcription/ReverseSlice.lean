/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.SortSlice

/-!
# Slice reversal transcription

The endpoints are signed pointer-like indices and `hi` is exclusive at the
public boundary.  Bounds failures return `none`; bounded-loop exhaustion is a
separate observable flag for later adequacy proofs.  Because a `SortSliceEntry`
contains its optional payload, each swap synchronizes keys and values.
-/

namespace CPythonListsort

universe u v

structure ReverseSliceResult (κ : Type u) (ν : Type v) where
  slice : SortSlice κ ν
  fuelExhausted : Bool
  deriving DecidableEq, Repr

/-- Fuel-bounded inclusive-endpoint loop underlying `reverseSlice?`, exported
so the traced assembly evaluator can prove exact erasure to the reviewed
transcription. -/
def reverseSliceLoop? :
    Nat → SortSlice κ ν → Int → Int → Option (ReverseSliceResult κ ν)
  | 0, slice, lo, hi =>
      some { slice := slice, fuelExhausted := decide (lo < hi) }
  | fuel + 1, slice, lo, hi =>
      if lo < hi then do
        let left ← slice.read? lo
        let right ← slice.read? hi
        let slice ← slice.write? lo right
        let slice ← slice.write? hi left
        reverseSliceLoop? fuel slice (lo + 1) (hi - 1)
      else
        some { slice := slice, fuelExhausted := false }

/-- Transcription of `reverse_slice(lo, hi)` with a half-open interval. -/
def reverseSlice? (slice : SortSlice κ ν) (lo hi : Int) :
    Option (ReverseSliceResult κ ν) :=
  if lo ≤ hi then
    if lo < hi then
      reverseSliceLoop? (hi - lo).toNat slice lo (hi - 1)
    else
      some { slice := slice, fuelExhausted := false }
  else
    none

/-- Transcription of `sortslice_reverse`: reverse `n` synchronized entries
starting at the supplied pointer-like base. -/
def sortsliceReverse? (slice : SortSlice κ ν) (base : Int) (n : Nat) :
    Option (ReverseSliceResult κ ν) :=
  reverseSlice? slice base (base + Int.ofNat n)

end CPythonListsort
