/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceAllMaps

/-!
# All actual original flagged-necklace maps

Every whole native simplicial necklace map retaining its actual original
endpoints, input and complete flags is a unique morphism of the same
original flagged category. The full native map readback is exact.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
variable {T U : Object K x y q}

/-- The whole original flagged morphism of an actual native simplicial map. -/
def homOfNativeMap (f : T.necklace.object.{u} ⟶ U.necklace.object.{u})
    (h₀ : T.necklace.source ≫ f = U.necklace.source)
    (h₁ : T.necklace.target ≫ f = U.necklace.target)
    (hi : f ≫ U.input = T.input)
    (hc : (OriginalBead.OuterOperator.map (Morphism.ofMap f h₀ h₁).operator
      (Morphism.ofMap f h₀ h₁).source (Morphism.ofMap f h₀ h₁).target).app q
        T.coefficient = U.coefficient) : T ⟶ U where
  necklaceMap := Morphism.ofMap f h₀ h₁
  over := (congrArg (fun a => a ≫ U.input) (Morphism.ofMap_map f h₀ h₁)).trans hi
  flags := hc

/-- The full underlying native map is literally the same supplied original simplicial map. -/
theorem homOfNativeMap_map
    (f : T.necklace.object.{u} ⟶ U.necklace.object.{u})
    (h₀ : T.necklace.source ≫ f = U.necklace.source)
    (h₁ : T.necklace.target ≫ f = U.necklace.target)
    (hi : f ≫ U.input = T.input)
    (hc : (OriginalBead.OuterOperator.map (Morphism.ofMap f h₀ h₁).operator
      (Morphism.ofMap f h₀ h₁).source (Morphism.ofMap f h₀ h₁).target).app q
        T.coefficient = U.coefficient) :
    (homOfNativeMap f h₀ h₁ hi hc).necklaceMap.map.{u} = f :=
  Morphism.ofMap_map f h₀ h₁

/-- Every complete actual native flagged map is retained by one same original morphism. -/
theorem existsUnique_homOfNativeMap
    (f : T.necklace.object.{u} ⟶ U.necklace.object.{u})
    (h₀ : T.necklace.source ≫ f = U.necklace.source)
    (h₁ : T.necklace.target ≫ f = U.necklace.target)
    (hi : f ≫ U.input = T.input)
    (hc : (OriginalBead.OuterOperator.map (Morphism.ofMap f h₀ h₁).operator
      (Morphism.ofMap f h₀ h₁).source (Morphism.ofMap f h₀ h₁).target).app q
        T.coefficient = U.coefficient) :
    ∃! h : T ⟶ U, h.necklaceMap.map.{u} = f := by
  refine ⟨homOfNativeMap f h₀ h₁ hi hc, homOfNativeMap_map f h₀ h₁ hi hc, ?_⟩
  intro h hh
  apply Hom.ext
  exact Morphism.map_injective (hh.trans (homOfNativeMap_map f h₀ h₁ hi hc).symm)

/-- The actual original flagged map type is faithful to its whole original native simplicial maps. -/
theorem hom_nativeMap_injective :
    Function.Injective (fun h : T ⟶ U => h.necklaceMap.map.{u}) := by
  intro f g h
  exact Hom.ext (Morphism.map_injective h)

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
