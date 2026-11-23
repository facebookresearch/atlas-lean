/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.DivisorDynamics

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.DivisorDynamics

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u

variable {k : Type u} [Field k] {X : Over (Spec (.of k))}

-- Iterates: `f^0 = 𝟙` and `f^{n+1} = f^n ≫ f`.
example (f : X ⟶ X) : iterateMap f 0 = 𝟙 X := rfl

example (f : X ⟶ X) (n : ℕ) : iterateMap f (n + 1) = iterateMap f n ≫ f := rfl

-- The empty tensor product is the structure sheaf.
example {d : ℕ} (L : Fin d → X.left.Modules) :
    selectedTensor L ∅ = structureModule X.left := by
  simp [selectedTensor]

variable [IsProper X.hom]

-- `d = 0`: the intersection number of no line bundles is `χ(𝒪_X)`.
example (hd : topologicalKrullDim X.left ≤ (0 : ℕ)) (L : Fin 0 → X.left.Modules) :
    mixedIntersection X 0 hd L = eulerCharacteristic X 0 hd (structureModule X.left) := by
  simp [mixedIntersection, selectedTensor]

-- `d = 1`: the intersection number of one line bundle is `χ(L) - χ(𝒪_X)`, its degree.
example (hd : topologicalKrullDim X.left ≤ (1 : ℕ)) (L : Fin 1 → X.left.Modules) :
    mixedIntersection X 1 hd L =
      eulerCharacteristic X 1 hd (selectedTensor L {0}) -
        eulerCharacteristic X 1 hd (structureModule X.left) := by
  have h : (Finset.univ : Finset (Fin 1)).powerset = {∅, {0}} := by decide
  rw [mixedIntersection, h, Finset.sum_pair (by simp)]
  simp [selectedTensor]
  ring

end MathlibExt.AlgebraicGeometry.DivisorDynamics
