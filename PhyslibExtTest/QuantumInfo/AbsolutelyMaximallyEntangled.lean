/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/OpenQuantumProblems/35.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import PhyslibExt.QuantumInfo.AbsolutelyMaximallyEntangled

@[expose] public section

/-!
# Tests for `PhyslibExt.QuantumInfo.AbsolutelyMaximallyEntangled`
-/

namespace PhyslibExtTest.QuantumInfo.AbsolutelyMaximallyEntangled

open OpenQuantumProblem35

-- Source faithfulness: the Formal Conjectures statement
-- `OpenQuantumProblem35.ame_9_10_open`, verbatim.
example : ExistsAME 9 10 := ame_9_10_open

-- The `Prop` abbreviation really is that statement.
example : ame_9_10_open_statement = ExistsAME 9 10 := rfl

-- Sanity checks carried by the Formal Conjectures file.
example (ψ : Config 2 3 → ℂ) (x : Config 2 3) : mkStateVector ψ x = ψ x := rfl

-- The witness is normalized, and it is the state that witnesses `ExistsAME 9 10`.
example : IsNormalized ameState := ameState_normalized

example : IsAME ameState := ⟨ameState_normalized, ameState_reduction_permuted⟩

-- The local splitting `Fin 10 ≃ ZMod 2 × ZMod 5` is a bijection on letters.
example (x : Fin 10) : localPartsEquiv x = (bitPart x, quintPart x) := rfl

-- The nine-cycle graph is symmetric with zero diagonal.
example (i j : Fin 9) : q2Cycle i j = q2Cycle j i := q2Cycle_symm i j
example (i : Fin 9) : q2Cycle i i = 0 := q2Cycle_diag i

-- The `ZMod 5` circulant graph is symmetric with zero diagonal.
example (i j : Fin 10) : q5Graph i j = q5Graph j i := q5Graph_symm i j
example (i : Fin 10) : q5Graph i i = 0 := q5Graph_diag i

-- `q5Select` accepts an unbalanced mask: with no `true` entry, it returns the fallback vertex.
example : q5Select (fun _ => false) true 0 = 0 := by decide

end PhyslibExtTest.QuantumInfo.AbsolutelyMaximallyEntangled
