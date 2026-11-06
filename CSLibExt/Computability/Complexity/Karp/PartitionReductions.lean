/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Partition
public import CSLibExt.Computability.Complexity.Karp.SubsetSumVerify
public import CSLibExt.Computability.Complexity.Karp.SubsetSumCorrect

/-!
# Encoded reductions for PARTITION

Both maps are total on bitstrings. The SUBSET-SUM side requires canonical
binary payloads, whereas the PARTITION side uses the generic Nat decoder,
which accepts false-ended payloads with Mathlib's exact `decodeNat` value.
These are deliberately distinct.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Partition

open Cslib.Complexity.Karp BitstringEncoding

/-- **Encoded reduction from SUBSET-SUM to PARTITION.**
SUBSET-SUM to PARTITION, with malformed inputs sent to `[1]`. -/
def reduceFromSubsetSum (x : List Bool) : List Bool :=
  match SSVerify.decodeSS x with
  | some (as, t) => bitEncode (fromSubsetSum as t)
  | none => bitEncode ([1] : List ℕ)

/-- **Encoded reduction from PARTITION to SUBSET-SUM.**
PARTITION to SUBSET-SUM, preserving the generic decoder's semantics. -/
def reduceToSubsetSum (x : List Bool) : List Bool :=
  match bitDecode (α := List ℕ) x with
  | some as => encodeSS (as.map (· * 2)) as.sum
  | none => noSS

/-- **Correctness of the encoded SUBSET-SUM to PARTITION reduction.**
The encoded reduction preserves every yes/no answer, including
malformed source strings. This is the semantic, not the time, theorem. -/
theorem reduceFromSubsetSum_correct (x : List Bool) :
    subsetSumDec x = partitionDec (reduceFromSubsetSum x) := by
  classical
  cases hd : SSVerify.decodeSS x with
  | none =>
    have hs : subsetSumDec x = false := by
      rw [Bool.eq_false_iff, ne_eq, subsetSumDec, decide_eq_true_eq]
      rintro ⟨as, t, he, _⟩
      have := SSVerify.decodeSS_eq_some.mpr he
      rw [hd] at this
      contradiction
    rw [hs, reduceFromSubsetSum, hd]
    symm
    rw [Bool.eq_false_iff, ne_eq, partitionDec_bitEncode]
    rintro ⟨s, _, he⟩
    simp only [List.sum_cons, List.sum_nil] at he
    omega
  | some p =>
    obtain ⟨as, t⟩ := p
    rw [reduceFromSubsetSum, hd, Bool.eq_iff_iff,
      partitionDec_bitEncode, fromSubsetSum_feasible,
      ← SSVerify.decodeSS_eq_some.mp hd, subsetSumDec_encodeSS_eq_true]

/-- **Correctness of the encoded PARTITION to SUBSET-SUM reduction.**
The membership map preserves the generic decoder, including accepted
noncanonical payloads and rejected malformed framing. -/
theorem reduceToSubsetSum_correct (x : List Bool) :
    partitionDec x = subsetSumDec (reduceToSubsetSum x) := by
  classical
  cases hd : bitDecode (α := List ℕ) x with
  | none => simp [partitionDec, reduceToSubsetSum, hd, subsetSumDec_noSS]
  | some as =>
    rw [partitionDec, reduceToSubsetSum, hd, Bool.eq_iff_iff,
      decide_eq_true_eq, subsetSumDec_encodeSS_eq_true]
    exact feasible_iff_doubled_sublist as

end MetaMathlibExt.Complexity.NPComplete.Partition
