/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeNerveUnitComparison
import MathlibExt.Topology.Homotopy.HSpaceNerveBaseComparison

open CategoryTheory Opposite
open scoped Simplicial

universe u

#check SSet.KanComplex.nativeCoverUnit_nerve_comp_counit
#print axioms SSet.KanComplex.nativeCoverUnit_nerve_comp_counit
#check SSet.KanComplex.nativeCoverUnit_nerve_isIso
#print axioms SSet.KanComplex.nativeCoverUnit_nerve_isIso
#check SSet.KanComplex.nativeCoverUnderProjection_nerve_isIso
#print axioms SSet.KanComplex.nativeCoverUnderProjection_nerve_isIso
#check SSet.KanComplex.nativeCover_nerve_to_point_mem_realizationWeakEquivalences
#print axioms SSet.KanComplex.nativeCover_nerve_to_point_mem_realizationWeakEquivalences
#check TopCat.HSpaceHomologyOne.isEquivalence_singularFundamentalGroupoid_of_integralHomologyOne_isIso
#print axioms TopCat.HSpaceHomologyOne.isEquivalence_singularFundamentalGroupoid_of_integralHomologyOne_isIso
#check TopCat.HSpaceHomologyOne.nerveBaseMap_mem_realizationWeakEquivalences_of_integralHomologyOne_isIso
#print axioms TopCat.HSpaceHomologyOne.nerveBaseMap_mem_realizationWeakEquivalences_of_integralHomologyOne_isIso

namespace HSpaceNerveBaseComparisonTests

example (X : SSet.{u}) :
    SSet.KanComplex.nativeCoverUnit (CategoryTheory.nerve (SSet.FundamentalGroupoid X)) ≫
      CategoryTheory.nerveMap (SSet.fundamentalGroupoidNerveCounit (SSet.FundamentalGroupoid X)) =
        𝟙 (CategoryTheory.nerve (SSet.FundamentalGroupoid X)) :=
  SSet.KanComplex.nativeCoverUnit_nerve_comp_counit (SSet.FundamentalGroupoid X)

example (X : SSet.{u}) (x : X _⦋0⦌) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.KanComplex.nativeCover (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
        (ComposableArrows.mk₀ (SSet.FundamentalGroupoid.mk x)))) :=
  SSet.KanComplex.nativeCover_nerve_to_point_mem_realizationWeakEquivalences
    (SSet.FundamentalGroupoid X) _

example {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (hf : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) :
    (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).IsEquivalence :=
  TopCat.HSpaceHomologyOne.isEquivalence_singularFundamentalGroupoid_of_integralHomologyOne_isIso f hf

example {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (hf : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) :
    SSet.realizationWeakEquivalences
      (CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f))) ∧
      TopCat.toSSet.map f ≫ SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y) =
        SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X) ≫
          CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)) :=
  ⟨TopCat.HSpaceHomologyOne.nerveBaseMap_mem_realizationWeakEquivalences_of_integralHomologyOne_isIso f hf,
    SSet.KanComplex.nativeCoverUnit_naturality (TopCat.toSSet.map f)⟩

end HSpaceNerveBaseComparisonTests
