/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Machines.Turing.MultiTape.TimeSpace
public import MathlibExt.Computability.Complexity

@[expose] public section

set_option autoImplicit false

namespace Cslib.MultiTapeComplexityBridgeWanted

open scoped Classical

/-- **The time/space form of the multi-tape bridge**: a language over
`Bool` is in multi-tape deterministic polynomial time iff its
characteristic function is in the canonical class `P`. The
language-level bridge in
`CSLibExt/Computability/Machines/Turing/MultiTape/Bridge.lean` erases
the time/space bounds, so it says nothing about polynomial blowups;
this is the polynomial form (BACKLOG MT5). The characteristic function
is written with `if` under the classical decidability instance.
Source: Sipser, *Introduction to the Theory of Computation*,
3rd ed., Cengage, 2013, Theorem 7.8 (multi-tape to single-tape
quadratic simulation) and §7.1; Hopcroft-Motwani-Ullman, *Introduction
to Automata Theory, Languages, and Computation*, 3rd ed., Pearson,
2007, §8.4 and §10.1. -/
theorem_wanted multiTape_P_eq_canonical_P :
  ∀ L : Set (List Bool),
    L ∈ Cslib.Turing.MultiTapeTM.Classes.P ↔
      (fun w ↦ if w ∈ L then true else false) ∈
        MetaMathlibExt.ComplexityTheory.P

end Cslib.MultiTapeComplexityBridgeWanted
