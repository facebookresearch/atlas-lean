/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.Bridge
public meta import CSLibExt.Computability.Machines.Turing.SingleTape.OfRecursive

@[expose] public section

/-!
# Tests for the bridge between single-tape machines and recursion theory

The input adapter (`consComputer`, `OfTM2.inputCode`, `OfTM2.inputDecode`) on concrete words, and the class
equalities on concrete predicates: evenness is decided by a single-tape machine, the halting
problem is recognized but not decided, and Post's theorem in both directions.
-/

set_option autoImplicit false

open Computability Cslib.Turing Cslib.Turing.SingleTapeTM.OfTM2 Cslib.Decidability Nat.Partrec

namespace CSLibExtTest.Computability.Machines.Turing.SingleTape

/-- Prepending a symbol takes two steps. -/
example : (SingleTapeTM.consComputer true).OutputsWithinTime [false, false] [true, false, false] 2 :=
  SingleTapeTM.consComputer_outputsWithinTime _ _

example : (SingleTapeTM.consComputer (3 : Fin 4)).Outputs [] [3] :=
  SingleTapeTM.consComputer_outputs _ _

/-! The input stack of the emulation: `w.reverse ++ [true]` as a number, and back. -/

#guard inputCode [true, false] = 6
#guard encodeNat (inputCode [true, false]) = [false, true, true]
#guard encodeNat (inputCode []) = [true]
#guard inputDecode (inputCode (encodeNat 13)) = 13
#guard (List.range 40).all fun n ↦ inputDecode (inputCode (encodeNat n)) == n
#guard (List.range 40).all fun n ↦
  encodeNat (inputCode (encodeNat n)) == (encodeNat n).reverse ++ [true]

/-- Evenness is computable, so a single-tape machine decides it. -/
theorem even_singleTapeDecidable : SingleTapeDecidable fun n : ℕ ↦ Even n := by
  refine singleTapeDecidable_iff_computablePred.mpr
    (ComputablePred.computable_iff.mpr ⟨fun n ↦ n % 2 == 0, ?_, ?_⟩)
  · exact (Primrec.beq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0)).to_comp
  · funext n
    simp [Nat.even_iff]

/-- Hence oddness is decidable. -/
example : SingleTapeDecidable fun n : ℕ ↦ ¬Even n := even_singleTapeDecidable.not

/-- Evenness is recognizable and co-recognizable (Post's theorem, left to right). -/
example : SingleTapeRecognizable (fun n : ℕ ↦ Even n) ∧
    SingleTapeCoRecognizable fun n : ℕ ↦ Even n :=
  singleTapeDecidable_iff_singleTapeRecognizable_and_singleTapeCoRecognizable.mp
    even_singleTapeDecidable

/-- Co-recognizability of evenness is r.e.-ness of oddness. -/
example : REPred fun n : ℕ ↦ ¬Even n :=
  singleTapeCoRecognizable_iff_rePred_not.mp even_singleTapeDecidable.singleTapeCoRecognizable

/-- The same predicate is decided by a multi-stack machine. -/
example : TM2Decidable fun n : ℕ ↦ Even n :=
  singleTapeDecidable_iff_tm2Decidable.mp even_singleTapeDecidable

/-- The halting problem on input `0` is recognizable. -/
example : SingleTapeRecognizable fun c : Code ↦ (c.eval 0).Dom :=
  singleTapeRecognizable_halting 0

/-- The halting problem on input `0` is not decidable. -/
example : ¬SingleTapeDecidable fun c : Code ↦ (c.eval 0).Dom :=
  not_singleTapeDecidable_halting 0

/-- Post's theorem rebuilds undecidability from non-co-recognizability. -/
example : ¬SingleTapeDecidable fun c : Code ↦ (c.eval 0).Dom := fun h ↦
  not_singleTapeCoRecognizable_halting 0 h.singleTapeCoRecognizable

/-- Recognizability of the halting set, unfolded: a single-tape machine over some finite alphabet
with an injective copy of the input bits halts exactly on the codes of halting programs. -/
example : ∃ (Symbol : Type) (_ : Inhabited Symbol) (_ : Fintype Symbol) (ι : Bool → Symbol),
    Function.Injective ι ∧ ∃ tm : SingleTapeTM Symbol,
      ∀ c : Code, tm.HaltsOn ((encodeNat (Encodable.encode c)).map ι) ↔ (c.eval 0).Dom :=
  singleTapeRecognizable_halting 0

end CSLibExtTest.Computability.Machines.Turing.SingleTape
