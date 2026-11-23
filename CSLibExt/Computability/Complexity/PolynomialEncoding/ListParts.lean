/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Computability.Complexity
import CSLibExt.Computability.CookLevin

/-!
# Structural laws for the existing framed list decoder

These are equations for the canonical decoder, not runtime assumptions about
arbitrary element codecs. Concrete nested codec machines use them to connect
one actual block-reading iteration with one list element.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding

open MetaMathlibExt.BitstringEncoding

private theorem blocks_fuel_eq (x : List Bool) (f g : Nat)
    (hf : x.length ≤ f) (hg : x.length ≤ g) :
    undelimitBlocksAux f x = undelimitBlocksAux g x := by
  induction f generalizing x g with
  | zero =>
    cases x with
    | nil => cases g <;> rfl
    | cons b xs => simp at hf
  | succ f ih =>
    cases x with
    | nil => cases g <;> rfl
    | cons b xs =>
      cases g with
      | zero => simp at hg
      | succ g =>
        simp only [undelimitBlocksAux]
        cases h : undelimit (b :: xs) with
        | none => rfl
        | some pr =>
          obtain ⟨p, r⟩ := pr
          have he := congrArg List.length
            ((Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h)
          simp only [List.length_cons, List.length_append, length_delimit]
            at he hf hg
          change (undelimitBlocksAux f r).map (p :: ·) =
            (undelimitBlocksAux g r).map (p :: ·)
          rw [ih r g (by omega) (by omega)]

/-- Parsing a framed head leaves exactly the raw remainder, including
any later framing failure. The decoder's fuel does not alter this law. -/
theorem blocks_delimit (p r : List Bool) :
    undelimitBlocks (delimit p ++ r) =
      (undelimitBlocks r).map (p :: ·) := by
  unfold undelimitBlocks
  have hl : (delimit p ++ r).length = (2 * p.length + r.length) + 1 := by
    simp only [List.length_append, length_delimit]
    omega
  rw [hl]
  have hs : undelimitBlocksAux (2 * p.length + r.length + 1)
      (delimit p ++ r) = (undelimit (delimit p ++ r)).bind
      (fun q => (undelimitBlocksAux (2 * p.length + r.length) q.2).map
        (q.1 :: ·)) := by
    cases p <;> rfl
  rw [hs, undelimit_delimit]
  change (undelimitBlocksAux (2 * p.length + r.length) r).map (p :: ·) = _
  rw [blocks_fuel_eq r (2 * p.length + r.length) r.length (by omega) le_rfl]

/-- The canonical list decoder consumes one raw payload at a time.
Both element failure and later framing failure are retained exactly. -/
theorem decode_list_delimit {α : Type} [MetaMathlibExt.BitstringEncoding α]
    (p r : List Bool) :
    bitDecode (α := List α) (delimit p ++ r) =
      (bitDecode (α := α) p).bind (fun a =>
        (bitDecode (α := List α) r).map (a :: ·)) := by
  change (undelimitBlocks (delimit p ++ r)).bind
      (List.mapM (bitDecode (α := α))) =
    (bitDecode (α := α) p).bind (fun a =>
      ((undelimitBlocks r).bind (List.mapM (bitDecode (α := α)))).map (a :: ·))
  rw [blocks_delimit]
  cases hb : undelimitBlocks r with
  | none =>
    cases bitDecode (α := α) p <;> rfl
  | some bs =>
    change (p :: bs).mapM (bitDecode (α := α)) =
      (bitDecode (α := α) p).bind (fun a =>
        (bs.mapM (bitDecode (α := α))).map (a :: ·))
    rw [List.mapM_cons]
    cases bitDecode (α := α) p <;>
      cases bs.mapM (bitDecode (α := α)) <;> rfl

/-- A nonempty input with a malformed first frame fails list decoding.
Empty input is excluded because it is the valid empty list. -/
theorem decode_list_none_of_undelimit_none {α : Type}
    [MetaMathlibExt.BitstringEncoding α] {x : List Bool}
    (hx : x ≠ []) (h : undelimit x = none) :
    bitDecode (α := List α) x = none := by
  cases x with
  | nil => exact (hx rfl).elim
  | cons b xs =>
    change (undelimitBlocksAux (xs.length + 1) (b :: xs)).bind
      (List.mapM (bitDecode (α := α))) = none
    simp [undelimitBlocksAux, h]

end Cslib.Complexity.PolynomialEncoding
