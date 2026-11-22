/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHoEssentialSurjectivity
import MathlibExt.AlgebraicTopology.SimplicialSpace.IntrinsicDKComposition
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingFaithfulness
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyMappingFibreWeakEquivalence

/-!
# Intrinsic Dwyer–Kan equivalences from the first two levels

A map between Segal spaces is an intrinsic Dwyer–Kan equivalence when its maps in outer degrees
zero and one are realization weak equivalences. These hypotheses give weakness on every mapping
fibre and essential surjectivity on homotopy categories; levelwise weak maps are a special case.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
attribute [local instance] SSet.modelCategoryQuillen.modelCategory
attribute [local instance] SimplicialSpace.ReedyModel.modelCategory
namespace SimplicialSpace

/-- Weakness in original degrees zero and one gives every original mapping-space weak map. -/
theorem mappingFibresWeak_of_zero_one_weak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (h0 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋0⦌)))
    (h1 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋1⦌))) :
    ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
      SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl) :=
  ReedyModel.mappingFibresWeak_of_zero_one_weak f hW.1 hV.1 h0 h1

namespace IntrinsicDK
/-- The actual RF-Segal map is intrinsically DK from weakness of its original first two levels. -/
theorem of_zero_one_weak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (h0 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋0⦌)))
    (h1 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋1⦌))) :
    isEquivalence f hW hV :=
  ⟨mappingFibresWeak_of_zero_one_weak f hW hV h0 h1,
    SegalHomotopy.map_essSurj_of_componentSurjective f hW hV
      (SSet.realizationWeakEquivalences.bijective_mapπ₀ h0).2⟩

/-- Every original levelwise weak map between RF-Segal endpoints is intrinsically DK. -/
theorem of_levelwiseWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (hf : ∀ n : ℕ, SSet.realizationWeakEquivalences (f.hom.app (op ⦋n⦌))) :
    isEquivalence f hW hV :=
  of_zero_one_weak f hW hV (hf 0) (hf 1)
end IntrinsicDK
end SimplicialSpace
