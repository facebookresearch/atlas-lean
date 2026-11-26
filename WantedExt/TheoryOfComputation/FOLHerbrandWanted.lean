/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Herbrand's theorem for first-order logic
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.FirstOrder.Syntax
public import Mathlib.ModelTheory.Semantics
public import CSLibExt.TheoryOfComputation.FOLHerbrand

@[expose] public section

namespace Cslib.Logic.FOLHerbrandWanted

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

variable {L : FirstOrder.Language} {α : Type*}

end Cslib.Logic.FOLHerbrandWanted
