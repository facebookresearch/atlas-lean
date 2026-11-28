/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.CodecMachine
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Represented

/-!
# Polynomial-time computations with a serialized first input
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding

open MetaMathlibExt BitstringEncoding ComplexityTheory Comprehension BitScan

local notation "Bits" => List Bool

private def unbits (w : Bits) := (rowsOf w).flatMap (fun r => [r.headD false])

private theorem polyUnbits : IsPolyTime unbits := by
  have h := polyFlatMap polyWordId (polyConst []) ((polyField true false).comp polyHead)
  unfold unbits
  simpa only [Function.comp_def, hd_pack] using h

private theorem unbits_encode (a : Bits) : unbits (bitEncode a) = a := by
  change (rowsOf ((a.map bitEncode).flatMap delimit)).flatMap (fun r => [r.headD false]) = a
  rw [rowsOf_frames, List.flatMap_map]
  induction a with
  | nil => rfl
  | cons b a ih => exact congrArg (b :: ·) ih

/-- Run a represented algorithm on the decoded first field of a product. Invalid
serializations take the supplied default. The product's second field is preserved
as canonical input for the algorithm, and both input and output I/O are charged. -/
theorem CodecMachine.isPolyTime_decodeFirst {α β γ : Type}
    [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ] (cm : CodecMachine α)
    (f : α × β → γ) (bad : γ) (hf : Represented (pair bitEncode bitEncode)
      (fun p => bitEncode (f p))) :
    IsPolyTime (fun p : Bits × β =>
      match bitDecode (α := α) p.1 with
      | none => bad
      | some a => f (a, p.2)) := by
  obtain ⟨run, hr, he⟩ := hf
  let raw (w : Bits) := unbits (hd w)
  have hraw : IsPolyTime raw := (polyField true false).comp polyUnbits
  have prep := polyPack (hraw.comp cm.polyNormalize) (polyField false true)
  have main := polyIf (hraw.comp cm.polyValid) (prep.comp hr) (polyConst (bitEncode bad))
  apply polyEncoded main
  rintro ⟨x,k⟩
  have fread : raw (bitEncode (x,k)) = x := by
    change unbits (hd (pack (bitEncode x) (bitEncode k))) = x
    rw [hd_pack, unbits_encode]
  have sk : tl (bitEncode (x,k)) = bitEncode k := tl_pack _ _
  change (if cm.valid (raw (bitEncode (x,k))) then
    run (pack (cm.normalize (raw (bitEncode (x,k)))) (tl (bitEncode (x,k)))) else _) = _
  rw [fread, sk, cm.valid_eq]
  cases h : bitDecode (α := α) x with
  | none => rfl
  | some a =>
    rw [cm.normalize_eq h]
    exact he (a,k)

end Cslib.Complexity.PolynomialEncoding
