/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ConeCylinderSection
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ConeSliceMate
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeConnectedColimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeVertices

/-!
# Focused clients for fat cones and the cone cylinder

The clients evaluate the ordinal section of the cone collapse at small values and
check that the collapse itself is not injective, so the section is a genuine
one-sided inverse. The fat cone of the empty boundary `∂Δ[0]` has only its apex
as a vertex. Fat cones preserve monomorphisms, connected colimits and pushouts,
and the cone-slice mate is used at the point `Δ[0]`.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeClientsTest

open SSet SSet.WalkingAdjunction

/-- The section sends the final vertex to the apex in the final row. -/
example : ConeCylinder.sectionOrder 1 (Fin.last 2) = (Fin.last 1, 1) := by decide

/-- The section keeps a base vertex in the zero row. -/
example : ConeCylinder.sectionOrder 2 1 = (1, 0) := by decide

/-- The collapse identifies the final row, so it has no left inverse. -/
example : ¬ Function.Injective (ConeCylinder.collapseOrder 1) := fun h ↦
  absurd (h (a₁ := ((0 : Fin 2), (1 : Fin 2))) (a₂ := ((1 : Fin 2), (1 : Fin 2))) (by decide))
    (by decide)

/-- The section is a right inverse of the collapse at every vertex. -/
example (k : Fin 4) :
    ConeCylinder.collapseOrder 2 (ConeCylinder.sectionOrder 2 k) = k :=
  ConeCylinder.sectionOrder_collapse 2 k

/-- The whole simplex section is a right inverse of the simplex collapse. -/
example :
    ConeCylinder.simplexSection.{u} 2 ≫ ConeCylinder.simplexCollapse 2 = 𝟙 Δ[3] :=
  ConeCylinder.simplexSection_collapse 2

/-- The cone cylinder of a standard simplex is an epimorphism. -/
example : Epi (ConeCylinder.coneCylinder (Δ[2] : SSet.{u})) := inferInstance

/-- The fat cone of the empty boundary `∂Δ[0]` has only apex vertices. -/
example (x : (FatCone.obj (∂Δ[0] : SSet.{u})) _⦋0⦌) :
    ∃ z : (Δ[0] : SSet.{u}) _⦋0⦌, (FatCone.apex _).app _ z = x := by
  rcases FatCone.vertex_base_or_apex _ x with ⟨a, -⟩ | h
  · have ha := a.2
    simp [boundary_zero] at ha
  · exact h

/-- The fat cone of a boundary inclusion is a monomorphism. -/
example : Mono (FatCone.map (boundary.{u} 2).ι) := inferInstance

/-- Transport of fat-cone components along a boundary inclusion is injective. -/
example (n : ℕ) : Function.Injective (FatCone.componentMap (boundary.{u} 2).ι n) :=
  FatCone.componentMap_injective _ n
    ((mono_iff_injective _).1 (inferInstance : Mono ((boundary.{u} 2).ι.app _)))

/-- Fat cones preserve coequalizers, a connected colimit shape. -/
example : PreservesColimitsOfShape WalkingParallelPair FatCone.underlyingFunctor.{u} :=
  FatCone.underlying_preservesColimitsOfShape _

/-- The join cone also preserves coequalizers. -/
example : PreservesColimitsOfShape WalkingParallelPair FatCone.joinFunctor.{u} :=
  FatCone.join_preservesColimitsOfShape _

/-- Fat cones send the chosen pushout of a span to a pushout square. -/
example {A B C : SSet.{u}} (f : A ⟶ B) (g : A ⟶ C) :
    IsPushout (FatCone.map f) (FatCone.map g) (FatCone.map (pushout.inl f g))
      (FatCone.map (pushout.inr f g)) :=
  FatCone.map_isPushout (IsPushout.of_hasPushout f g)

/-- The comparison from fat cones to join cones is the original map at `Δ[1]`. -/
example :
    FatCone.underlyingComparison.app (Δ[1] : SSet.{u}) = FatCone.toJoin Δ[1] :=
  FatCone.underlyingComparison_app _

/-- The cone-slice mate at the point `Δ[0]` is compatible with both projections. -/
example :
    ConeSliceMate.comparison.app (Under.mk (𝟙 (Δ[0] : SSet.{u}))) ≫
        pathSliceOver.proj (𝟙 (Δ[0] : SSet.{u})) =
      sliceOver.proj (Δ[0] : SSet.{u}) (𝟙 Δ[0]) :=
  ConeSliceMate.comparison_proj _

end MathlibExtTest.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeClientsTest
