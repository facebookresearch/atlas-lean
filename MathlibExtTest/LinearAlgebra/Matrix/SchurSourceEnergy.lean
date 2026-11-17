/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy

@[expose] public section

open MathlibExt.LinearAlgebra.Matrix.SchurSourceEnergy Matrix

namespace MathlibExtTest.LinearAlgebra.Matrix.SchurSourceEnergy

/-- The corrected identity holds on the singleton fixture and
the uncorrected one fails there. -/
example :
    (!![(-1 : ℝ)])ᵀ *ᵥ ![1] + !![(2 : ℝ)] *ᵥ ![1] = ![1] ∧
      (![(1 : ℝ)] ⊕ᵥ ![1]) ⬝ᵥ
          (fromBlocks !![(2 : ℝ)] !![-1] (!![(-1 : ℝ)])ᵀ !![2] *ᵥ (![1] ⊕ᵥ ![1])) = 2 ∧
      ![(1 : ℝ)] ⬝ᵥ ((!![(2 : ℝ)] - !![(-1 : ℝ)] * (!![(2 : ℝ)])⁻¹ * (!![(-1 : ℝ)])ᵀ) *ᵥ
          ![1]) = 3 / 2 ∧
      ![(1 : ℝ)] ⬝ᵥ ((!![(2 : ℝ)])⁻¹ *ᵥ ![1]) = 1 / 2 :=
  ⟨singleton_fixture_values.1, singleton_fixture_values.2.1, singleton_fixture_values.2.2.1,
    singleton_fixture_values.2.2.2.1⟩

end MathlibExtTest.LinearAlgebra.Matrix.SchurSourceEnergy
