/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Circuit.Basic

/-!
# Boolean circuit basis

NOT and positive-arity AND/OR gates, as used in CLRS4 section 34.3,
printed pages 1065-1068. The signature and interpretation use the canonical
CSLib straight-line program and circuit types.
-/

@[expose] public section

namespace Cslib.Circuits

/-- The Boolean source basis: unary NOT and nonempty AND/OR gates. -/
inductive BooleanGate where
  | not
  | and (arityMinusOne : Nat)
  | or (arityMinusOne : Nat)
  deriving Repr, DecidableEq

/-- The Boolean signature, with no zero-input AND or OR gate. -/
def booleanSignature : Signature where
  Op := BooleanGate
  Arity
    | .not => 1
    | .and a => a + 1
    | .or a => a + 1

/-- The usual Boolean interpretation of NOT, AND and OR. -/
def booleanInterpretation : Interpretation booleanSignature Bool
  | .not, f => !(f ⟨0, by decide⟩)
  | .and a, f => Fin.foldl (a + 1) (fun acc k => acc && f k) true
  | .or a, f => Fin.foldl (a + 1) (fun acc k => acc || f k) false

/-- NOT negates its sole input. -/
@[simp] theorem booleanInterpretation_not (f : Fin 1 → Bool) :
    booleanInterpretation .not f = !(f 0) := rfl

/-- AND visits the nonempty argument vector from left to right. -/
theorem booleanInterpretation_and (a : Nat) (f : Fin (a + 1) → Bool) :
    booleanInterpretation (.and a) f =
      Fin.foldl (a + 1) (fun acc k => acc && f k) true := rfl

/-- OR visits the nonempty argument vector from left to right. -/
theorem booleanInterpretation_or (a : Nat) (f : Fin (a + 1) → Bool) :
    booleanInterpretation (.or a) f =
      Fin.foldl (a + 1) (fun acc k => acc || f k) false := rfl

end Cslib.Circuits
