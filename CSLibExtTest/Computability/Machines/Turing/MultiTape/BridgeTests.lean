/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.Bridge

/-!
# Tests for the multi-tape to recursion-theory bridge

The proved bridge composes: a multi-tape decider yields a computable
predicate and a multi-stack decider, and a multi-tape recognizer yields
an r.e. predicate and a multi-stack recognizer.
-/

public section

set_option autoImplicit false

open Computability

namespace Cslib.Decidability.MultiTapeBridgeTests

/-- A multi-tape decider yields a computable predicate and a multi-stack
decider. -/
example {p : ℕ → Prop} (h : MultiTapeDecidable p) :
    ComputablePred p ∧ TM2Decidable p :=
  ⟨h.computablePred, multiTapeDecidable_implies_tm2Decidable h⟩

/-- A multi-tape recognizer yields an r.e. predicate and a multi-stack
recognizer. -/
example {p : ℕ → Prop} (h : MultiTapeRecognizable p) :
    REPred p ∧ TM2Recognizable p :=
  ⟨h.rePred, multiTapeRecognizable_implies_tm2Recognizable h⟩

#print axioms Cslib.Decidability.MultiTapeDecidable.computablePred
#print axioms Cslib.Decidability.multiTapeDecidable_implies_tm2Decidable
#print axioms Cslib.Decidability.multiTapeRecognizable_implies_tm2Recognizable

end Cslib.Decidability.MultiTapeBridgeTests
