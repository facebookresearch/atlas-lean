/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatchingTerminal
public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyModelCategory

/-!
# Absolute matching maps and Reedy fibrancy

The established generic Reedy fibrancy criterion is extracted here from
the Ordered JFS application. It uses the actual terminal comparison at
every degree and retains its existing public name and hypotheses.
-/

@[expose] public section

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial

namespace CategoryTheory.SimplicialObject
variable {C : Type u} [Category.{v} C]

namespace reedyModelCategory
section
variable [ModelCategory C]
open scoped CategoryTheory.SimplicialObject.reedyModelCategory

/-- In the native Reedy model, fibrancy is equivalent to absolute matching fibrations.
This reduces the actual terminal arrow at every degree, including degree zero. -/
theorem isFibrant_iff_matchingMaps (X : SimplicialObject C) :
    IsFibrant X ↔ ∀ n : ℕ, fibrations C (matchingMap X n) := by
  rw [HomotopicalAlgebra.isFibrant_iff, HomotopicalAlgebra.fibration_iff]
  change reedyRight (fibrations C) (terminal.from X) ↔
    ∀ n : ℕ, fibrations C (matchingMap X n)
  constructor
  · intro h n
    exact (relativeMatchingMap_terminal_mem_iff (fibrations C) X n).mp (h n)
  · intro h n
    exact (relativeMatchingMap_terminal_mem_iff (fibrations C) X n).mpr (h n)
end
end reedyModelCategory

end CategoryTheory.SimplicialObject
