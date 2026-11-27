/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicCoefficientSheafCondition
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Tests for the holomorphic coefficient sheaf condition

The theorem yields a ring sheaf and unique gluing on the complex model space.

Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 2, printed pages 9--11.
-/

namespace MathlibExtTest.AlgebraicGeometry
namespace HarmonicHolomorphicModulesHolomorphicCoefficientSheafCondition

open CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry

example : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology (Coordinates 1))
    (ringPresheaf (Coordinates 1) (Coordinates 1)) :=
  (holomorphic_coefficient_sheaf_condition (n := 1) (M := Coordinates 1)).isSheaf

example {ι : Type} (U : ι → Opens (Coordinates 1))
    (f : ∀ i, holomorphicAlgebra (Coordinates 1) (Coordinates 1) (U i))
    (h : TopCat.Presheaf.IsCompatible (X := TopCat.of (Coordinates 1))
      (ringPresheaf (Coordinates 1) (Coordinates 1)) U f) :
    ∃! g : holomorphicAlgebra (Coordinates 1) (Coordinates 1) (iSup U),
      TopCat.Presheaf.IsGluing (X := TopCat.of (Coordinates 1))
        (ringPresheaf (Coordinates 1) (Coordinates 1)) U f g := by
  exact TopCat.Presheaf.IsSheaf.isSheafUniqueGluing (X := TopCat.of (Coordinates 1))
    (F := ringPresheaf (Coordinates 1) (Coordinates 1))
    (holomorphic_coefficient_sheaf_condition (n := 1) (M := Coordinates 1)).isSheaf U f h

end HarmonicHolomorphicModulesHolomorphicCoefficientSheafCondition
end MathlibExtTest.AlgebraicGeometry
