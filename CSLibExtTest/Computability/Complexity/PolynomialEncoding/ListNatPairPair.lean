/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNatPairPair

open Turing MetaMathlibExt.BitstringEncoding
open Cslib.Complexity.PolynomialEncoding
open ListNatPairPair

set_option maxRecDepth 10000

private def drive {J : Type} [DecidableEq J]
    (P : Lab → TM2.Stmt (fun _ : J => Bool) Lab Bool) :
    Nat → TM2.Cfg (fun _ : J => Bool) Lab Bool →
      Option (TM2.Cfg (fun _ : J => Bool) Lab Bool)
  | 0, _ => none
  | n + 1, c =>
    if c.l = some .good ∨ c.l = some .bad then some c
    else (TM2.step P c).bind (drive P n)

private def checkGood (x : List Bool) (as : List (Nat × Nat)) (c t : Nat)
    (weights values capacity threshold : List Bool) : Bool :=
  match drive prog (9 * x.length + 3) ⟨some (.split .read), true,
      st [] x weights values capacity threshold⟩ with
  | none => false
  | some result => decide (result.l = some .good ∧
      result.stk = st [] [] (bitEncode (as.map Prod.fst) ++ weights)
        (bitEncode (as.map Prod.snd) ++ values)
        (Computability.encodeNat c ++ capacity)
        (Computability.encodeNat t ++ threshold))

private theorem empty_items_zero_fields :
    checkGood [false, false] [] 0 0
      [true] [false] [true, false] [false] = true := by
  decide

private theorem empty_items_noncanonical_threshold :
    checkGood [false, false, false] [] 0 2 [] [] [] [] = true := by decide

private theorem noncanonical_items_and_both_bounds :
    checkGood (delimit (delimit [false, false]) ++
      delimit [false] ++ [true, false]) [(0, 2)] 2 5 [] [] [] [] = true := by
  decide

private theorem empty_final_nat_payload :
    checkGood [false, true, false, false] [] 2 0 [] [] [] [] = true := by decide

private theorem entire_false_ending_remainder :
    checkGood [false, false, false, false] [] 0 4 [] [] [] [] = true := by
  decide

private theorem canonical_asymmetric_fields :
    checkGood (bitEncode (([(2, 5), (0, 3)], (8, 13)) :
      List (Nat × Nat) × (Nat × Nat))) [(2, 5), (0, 3)] 8 13
      [true] [false] [false, true] [true, false] = true := by
  decide

private theorem duplicate_occurrences_and_order :
    checkGood (bitEncode (([(0, 2), (0, 2), (5, 0)], (2, 7)) :
      List (Nat × Nat) × (Nat × Nat))) [(0, 2), (0, 2), (5, 0)] 2 7
      [] [] [] [] = true := by
  decide

private def checkBad (x : List Bool) : Bool :=
  match drive prog (9 * x.length + 3) ⟨some (.split .read), false,
      st [] x [] [] [] []⟩ with
  | none => false
  | some result => result.l == some .bad

private theorem missing_outer_pair : checkBad [] = true := by decide
private theorem truncated_outer_pair : checkBad [true] = true := by decide
private theorem unterminated_outer_pair :
    checkBad [true, false] = true := by decide
private theorem missing_final_pair : checkBad [false] = true := by decide
private theorem truncated_final_pair :
    checkBad [false, true] = true := by decide
private theorem malformed_item :
    checkBad (delimit [false] ++ [false]) = true := by decide
private theorem malformed_list_tail :
    checkBad (delimit (delimit [false] ++ [true]) ++ [false]) = true := by
  decide
private theorem malformed_inner_pair :
    checkBad (delimit (delimit [true]) ++ [false]) = true := by decide
private theorem malformed_final_pair_after_item :
    checkBad (delimit (delimit [false]) ++ [true]) = true := by decide

private def extension : MetaMathlibExt.TM2Embedding.SEmb
    (fun _ : K => Bool) (fun _ : Option K => Bool) where
  e := some
  inj := fun _ _ h => Option.some.inj h
  ι _ := Equiv.refl Bool

private def checkFrame (x : List Bool) : Bool :=
  let P := fun l => MetaMathlibExt.TM2Embedding.mapS extension id (prog l)
  let S : Option K → List Bool
    | none => [true, false, true]
    | some k => st [] x [true] [false] [false, true] [true, false] k
  match drive P (9 * x.length + 3) ⟨some (.split .read), false, S⟩ with
  | none => false
  | some result => result.stk none == [true, false, true] &&
      result.l == some (if
        (bitDecode (α := List (Nat × Nat) × (Nat × Nat)) x).isSome
        then .good else .bad)

private theorem external_frame_success :
    checkFrame (delimit (delimit [false, false]) ++ [false]) = true := by decide
private theorem external_frame_outer_failure :
    checkFrame [true, false] = true := by decide
private theorem external_frame_items_failure :
    checkFrame (delimit [false] ++ [false]) = true := by decide
private theorem external_frame_final_pair_failure :
    checkFrame (delimit (delimit [false]) ++ [true]) = true := by decide

private def checkRepeated : Bool :=
  let x := delimit (delimit [false, false]) ++ [false, false]
  let y := bitEncode (([(2, 0)], (1, 0)) : List (Nat × Nat) × (Nat × Nat))
  match drive prog (9 * x.length + 3)
      ⟨some (.split .read), true, st [] x [] [] [] []⟩ with
  | none => false
  | some first =>
    if first.l ≠ some .good then false else
    let S := Function.update first.stk (.pair (.pair .input)) y
    match drive prog (9 * y.length + 3) ⟨some (.split .read), false, S⟩ with
    | none => false
    | some second => decide (second.l = some .good ∧
        second.stk = st [] [] (bitEncode ([2, 0] : List Nat))
          (bitEncode ([0, 2] : List Nat)) (Computability.encodeNat 1)
          (Computability.encodeNat 2))

private theorem repeated_calls_reuse_clean_workspace :
    checkRepeated = true := by decide
