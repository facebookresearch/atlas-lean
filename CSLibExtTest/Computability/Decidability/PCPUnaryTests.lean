/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.PCPUnary

@[expose] public section

/-!
# Tests for unary PCP

The criterion decides concrete instances in both directions, and the problem is decidable by a
multi-stack machine.
-/

set_option autoImplicit false

open Cslib.Decidability Cslib.Decidability.Post

namespace CSLibExtTest.Computability.Decidability.PCPUnary

/-- One domino short on top, one short on the bottom: solvable. -/
example : PCP ([([()], [(), ()]), ([(), ()], [()])] : List (Domino Unit)) :=
  (unaryTest_iff _).mp (by decide)

/-- Every domino longer on top: unsolvable. -/
example : ¬PCP ([([(), ()], [()]), ([()], [])] : List (Domino Unit)) := fun h ↦
  absurd ((unaryTest_iff _).mpr h) (by decide)

/-- A balanced domino alone is a solution. -/
example : PCP ([([(), (), ()], [(), (), ()])] : List (Domino Unit)) :=
  (unaryTest_iff _).mp (by decide)

example : TM2Decidable (PCP (α := Unit)) := tm2Decidable_pcp_of_subsingleton

end CSLibExtTest.Computability.Decidability.PCPUnary
