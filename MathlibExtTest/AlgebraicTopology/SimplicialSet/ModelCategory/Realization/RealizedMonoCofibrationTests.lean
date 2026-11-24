/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedMonoCofibration

/-!
# Realized simplicial monomorphism boundary-LLP tests

The focused client below applies the property-level adapter to a horn
inclusion, which is a monomorphism but not one of the boundary generators.
-/

open CategoryTheory MorphismProperty

open scoped Simplicial

universe u

namespace MathlibExtTest.RealizedMonoCofibration

/-- The property-level adapter has the exact symbolic-universe target. -/
example {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    TopCat.realizedBoundaryInclusions.{u}.rlp.llp
      (SSet.toTop.{u}.map f) :=
  SSet.toTop_map_mem_realizedBoundaryLLP f

/-- Identity monomorphisms are accepted in every universe. -/
example (X : SSet.{u}) :
    TopCat.realizedBoundaryInclusions.{u}.rlp.llp
      (SSet.toTop.{u}.map (𝟙 X)) :=
  SSet.toTop_map_mem_realizedBoundaryLLP (𝟙 X)

/-- A symbolic-universe horn inclusion is a representative nonidentity
monomorphism outside the boundary-generator family itself. -/
example :
    TopCat.realizedBoundaryInclusions.{u}.rlp.llp
      (SSet.toTop.{u}.map (SSet.horn.{u} 2 (0 : Fin 3)).ι) :=
  SSet.toTop_map_mem_realizedBoundaryLLP
    (SSet.horn.{u} 2 (0 : Fin 3)).ι

/-- Concrete universe-one client. -/
example :
    TopCat.realizedBoundaryInclusions.{1}.rlp.llp
      (SSet.toTop.{1}.map (SSet.horn.{1} 1 (0 : Fin 2)).ι) :=
  SSet.toTop_map_mem_realizedBoundaryLLP
    (SSet.horn.{1} 1 (0 : Fin 2)).ι

/-- Retained universe-zero source-compatible client. -/
example :
    TopCat.realizedBoundaryInclusions.{0}.rlp.llp
      (SSet.toTop.{0}.map (SSet.horn.{0} 2 (0 : Fin 3)).ι) :=
  SSet.toTop_map_mem_realizedBoundaryLLP
    (SSet.horn.{0} 2 (0 : Fin 3)).ι

#print axioms SSet.toTop_map_mem_realizedBoundaryLLP

end MathlibExtTest.RealizedMonoCofibration
