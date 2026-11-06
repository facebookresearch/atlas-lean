/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.PartitionReductions

/-!
# Bitlength bounds for the PARTITION reductions

These bounds use the length of binary payloads, never the represented value.
They are output-size bounds, not substitutes for the machine-time proofs.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Partition

open Cslib.Complexity.Karp BitstringEncoding Computability

private theorem encoded_list (as : List ℕ) :
    bitEncode as = as.flatMap (fun a => delimit (encodeNat a)) := by
  change ((as.map encodeNat).map delimit).flatten = _
  simp only [List.map_map, List.flatMap_def, Function.comp_def]

/-- **Bitlength of a PARTITION sum is at most the encoded length.**
Summing a binary PARTITION instance cannot exceed its encoded length. -/
theorem sum_encoding_length_le (as : List ℕ) :
    (encodeNat as.sum).length ≤ (bitEncode as).length := by
  induction as with
  | nil => simp [encoded_list, TM2Recursive.encodeNat_zero]
  | cons a as ih =>
    have h := SSVerify.length_addB false (encodeNat a) (encodeNat as.sum)
    rw [SSVerify.addB_encodeNat] at h
    simp only [Bool.toNat_false, Nat.add_zero] at h
    simp only [encoded_list, List.flatMap_cons, List.length_append,
      length_delimit, List.sum_cons] at ih ⊢
    omega

/-- **Padding reduction has linear output length.**
The padding reduction has linear output length in its encoded input. -/
theorem fromSubsetSum_length (as : List ℕ) (t : ℕ) :
    (bitEncode (fromSubsetSum as t)).length ≤
      3 * (encodeSS as t).length + 1 := by
  have hs := sum_encoding_length_le as
  have ht := SSVerify.length_addB false (encodeNat t) (encodeNat t)
  rw [SSVerify.addB_encodeNat] at ht
  simp only [Bool.toNat_false, Nat.add_zero, ← two_mul] at ht
  simp only [fromSubsetSum, encoded_list, List.flatMap_cons,
    List.length_append, length_delimit, encodeSS] at hs ⊢
  omega

/-- **Encoded SUBSET-SUM to PARTITION map has linear output length.**
Linear output bound on all strings, including malformed encodings. -/
theorem reduceFromSubsetSum_length (x : List Bool) :
    (reduceFromSubsetSum x).length ≤ 3 * x.length + 3 := by
  cases hd : SSVerify.decodeSS x with
  | none =>
    simp only [reduceFromSubsetSum, hd]
    change 3 ≤ 3 * x.length + 3
    omega
  | some p =>
    obtain ⟨as, t⟩ := p
    have h := fromSubsetSum_length as t
    rw [SSVerify.decodeSS_eq_some.mp hd] at h
    simpa only [reduceFromSubsetSum, hd] using
      h.trans (by omega : 3 * x.length + 1 ≤ 3 * x.length + 3)

private theorem doubled_bits_le (as : List ℕ) :
    (bitEncode (as.map (· * 2))).length ≤ 3 * (bitEncode as).length := by
  induction as with
  | nil => simp [encoded_list]
  | cons a as ih =>
    have ha := SSVerify.length_addB false (encodeNat a) (encodeNat a)
    rw [SSVerify.addB_encodeNat] at ha
    simp only [Bool.toNat_false, Nat.add_zero, ← mul_two] at ha
    simp only [encoded_list, List.map_cons, List.flatMap_cons,
      List.length_append, length_delimit] at ih ⊢
    omega

/-- **PARTITION membership instance has linear bitlength.**
Linear bitlength bound for the membership instance. -/
theorem toSubsetSum_length (as : List ℕ) :
    (encodeSS (as.map (· * 2)) as.sum).length ≤
      5 * (bitEncode as).length + 1 := by
  have hs := sum_encoding_length_le as
  have hd := doubled_bits_le as
  rw [encodeSS, List.length_append, length_delimit, ← encoded_list]
  omega

end MetaMathlibExt.Complexity.NPComplete.Partition
