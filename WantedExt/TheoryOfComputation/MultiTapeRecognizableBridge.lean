/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Machines.Turing.MultiTape.Bridge

@[expose] public section

set_option autoImplicit false

namespace Cslib.MultiTapeRecognizableBridgeWanted

/-- **Recursion theory to multi-tape machines, recognizers**: every
r.e. predicate is recognizable by a multi-tape machine. This is the
converse of the proved direction in
`CSLibExt/Computability/Machines/Turing/MultiTape/Bridge.lean`
(`multiTapeRecognizable_implies_tm2Recognizable`): it needs a
multi-tape machine simulating a `FinTM2` machine (or a partial
recursive function), which is a separate construction. Source: Sipser,
*Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013,
Corollary 3.15; Hopcroft-Motwani-Ullman, *Introduction to Automata
Theory, Languages, and Computation*, 3rd ed., Pearson, 2007, §8.4. -/
theorem_wanted tm2Recognizable_implies_multiTapeRecognizable :
  ∀ {α : Type*} [Primcodable α] {p : α → Prop},
    Cslib.Decidability.TM2Recognizable p → Cslib.Decidability.MultiTapeRecognizable p

end Cslib.MultiTapeRecognizableBridgeWanted
