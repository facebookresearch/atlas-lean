/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.PolyTime
public import CSLibExt.Computability.Complexity.PathInP
public meta import CSLibExt.Computability.Machines.Turing.SingleTape.PolyTime

@[expose] public section

/-!
# Tests for polynomial time on single-tape machines

The reversal component is run step by step on a concrete input, and the transfer theorem is
applied to the s-t path problem, which is in `P` (`Cslib.Complexity.Path.pathDec_mem_P`).
-/

set_option autoImplicit false

open Turing MetaMathlibExt.ComplexityTheory Cslib.Turing Cslib.Complexity

namespace CSLibExtTest.Computability.Machines.Turing.SingleTape.PolyTime

/-- Run the reversal program for `k` steps, or until it halts. -/
def runRev : ℕ → TM2.Cfg (fun _ : RevTail.K ↦ Bool) RevTail.L Bool →
    TM2.Cfg (fun _ : RevTail.K ↦ Bool) RevTail.L Bool
  | 0, c => c
  | k + 1, c => (TM2.step RevTail.prog c).elim c (runRev k)

/-- The reversal program's start configuration on `x`. -/
def revInit (x : List Bool) : TM2.Cfg (fun _ : RevTail.K ↦ Bool) RevTail.L Bool :=
  ⟨some .mv, false, Function.update (fun _ ↦ []) RevTail.K.X x⟩

/-! On `true true false`, the program reaches `done` after `|x| + 2 = 5` steps with
`(x.reverse).tail = true true` on the output stack and an empty input stack. -/

#guard (runRev 5 (revInit [true, true, false])).l == some .done

#guard (runRev 5 (revInit [true, true, false])).stk .O == [true, true]

#guard (runRev 5 (revInit [true, true, false])).stk .X == []

#guard (runRev 4 (revInit [true, true, false])).l == some .drop

/-! On the empty input, the output is the tail of the empty list. -/

#guard (runRev 2 (revInit [])).l == some .done && (runRev 2 (revInit [])).stk .O == []

/-- The reversal theorem on a concrete input. -/
example : ∃ v S', MetaMathlibExt.TM2Program.RunLe RevTail.comp.prog 5
    ⟨some RevTail.L.mv, false,
      Function.update (fun _ ↦ []) RevTail.K.X ([true, true, false].map id)⟩
    ⟨some RevTail.L.done, v, S'⟩ ∧ S' RevTail.K.O = [true, true] :=
  RevTail.run [true, true, false]

/-- The s-t path problem is decided in polynomial time by a single-tape machine. -/
example : Path.pathDec ∈ SingleTapeP := P_subset_singleTapeP Path.pathDec_mem_P

/-- Unfolded: a single-tape decider for the s-t path problem with a polynomial time bound. -/
example : ∃ (Symbol : Type) (_ : Inhabited Symbol) (_ : Fintype Symbol) (ι : Bool → Symbol),
    Function.Injective ι ∧ ∃ (tm : SingleTapeTM Symbol) (p : Polynomial ℕ),
      ∀ w : List Bool, tm.OutputsWithinTime (w.map ι) [ι (Path.pathDec w)] (p.eval w.length) :=
  P_subset_singleTapeP Path.pathDec_mem_P

end CSLibExtTest.Computability.Machines.Turing.SingleTape.PolyTime
