/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.AssignmentDual

@[expose] public section

/-- With zero potentials and constant costs, every assignment ties. -/
example : ∑ i : Fin 2, (1 : ℚ) ≤ ∑ i : Fin 2, (1 : ℚ) := le_refl _

end
