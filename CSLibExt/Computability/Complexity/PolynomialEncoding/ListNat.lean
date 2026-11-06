/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.Bounds
public import CSLibExt.Computability.Complexity.FramedCNF.Normalize
import CSLibExt.Computability.CookLevin

/-!
# Canonicalization of the concrete binary List Nat codec

This module relates the existing decoder to its raw framed payloads.
It neither changes the codec nor assumes canonicality of accepted input.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding

open MetaMathlibExt BitstringEncoding Computability FramedCNF

/-- **Successful block parsing reconstructs the input.**
Successful block parsing reconstructs the entire input. -/
theorem blocks_decode_sound {fuel : Nat} {x : List Bool}
    {bs : List (List Bool)} (h : undelimitBlocksAux fuel x = some bs) :
    x = (bs.map delimit).flatten := by
  induction fuel generalizing x bs with
  | zero => cases x <;> simp_all [undelimitBlocksAux]
  | succ fuel ih =>
    cases x with
    | nil => simp_all [undelimitBlocksAux]
    | cons b xs =>
      change ((undelimit (b :: xs)).bind fun p =>
        (undelimitBlocksAux fuel p.2).map (p.1 :: ·)) = _ at h
      obtain ⟨⟨p, r⟩, hp, hs⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨bs, hb, rfl⟩ := Option.map_eq_some_iff.mp hs
      have hr : r = (bs.map delimit).flatten := ih hb
      rw [(Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hp, hr]
      rfl

/-- **Decoding natural-number payloads never fails.**
Nat payload decoding never fails, including on noncanonical bits. -/
theorem mapM_decode_nat (bs : List (List Bool)) :
    bs.mapM (bitDecode (α := Nat)) = some (bs.map decodeNat) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.mapM_cons]
    change (some (decodeNat b)).bind (fun n =>
      (bs.mapM (bitDecode (α := Nat))).bind (fun ns => some (n :: ns))) = _
    simp [ih]

/-- **Decoding a list of naturals is block parsing then number decoding.**
List Nat decoding is precisely framed-payload parsing followed by
the existing total Nat decoder. -/
theorem decode_list_nat (x : List Bool) :
    bitDecode (α := List Nat) x =
      (undelimitBlocks x).map (List.map decodeNat) := by
  change (undelimitBlocks x).bind (List.mapM bitDecode) = _
  cases h : undelimitBlocks x with
  | none => rfl
  | some bs => exact mapM_decode_nat bs

/-- **Re-encoding decoded payloads normalizes each one.**
Canonical re-encoding normalizes each payload without changing
list order or multiplicity. -/
theorem encode_decoded_nat_blocks (bs : List (List Bool)) :
    bitEncode (bs.map decodeNat) =
      (bs.map (fun p => delimit (normalizeNat p))).flatten := by
  change ((bs.map decodeNat).map bitEncode |>.map delimit |>.flatten) = _
  simp only [List.map_map, Function.comp_def,
    BinaryNatEncoding.bitEncode_nat, normalizeNat_eq_encode_decode]

/-- **Normalizing framed number payloads at most triples the length.**
Normalizing every framed Nat payload increases length by at most
threefold, even for noncanonical input. -/
theorem normalized_nat_blocks_length_le (bs : List (List Bool)) :
    ((bs.map (fun p => delimit (normalizeNat p))).flatten).length ≤
      3 * ((bs.map delimit).flatten).length := by
  induction bs with
  | nil => simp
  | cons p bs ih =>
    have hp := length_normalizeNat_le p
    simp only [List.map_cons, List.flatten_cons, List.length_append,
      length_delimit] at ih ⊢
    omega

/-- **Re-encoded decoded list of naturals is linear in raw input.**
Re-encoding a successfully decoded List Nat is linear in the raw
input, not in the decoded numeric values. -/
theorem decoded_list_nat_encode_length_le {x : List Bool} {as : List Nat}
    (h : bitDecode x = some as) : (bitEncode as).length ≤ 3 * x.length := by
  rw [decode_list_nat] at h
  obtain ⟨bs, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [encode_decoded_nat_blocks, blocks_decode_sound hb]
  exact normalized_nat_blocks_length_le bs

end Cslib.Complexity.PolynomialEncoding
