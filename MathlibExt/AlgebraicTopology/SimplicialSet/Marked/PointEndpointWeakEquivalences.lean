/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntervalContraction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingHomotopyWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.PointRelativeMapping
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalPointFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianWeakEquivalences

/-!
# Original vertical interval endpoints are mapping weak equivalences

The original fully marked ordered interval contracts by its actual
pointwise minimum map. Its maximal precomposition mapping maps have
native homotopy inverses. Every original intrinsic point target has Kan
mapping complexes, and the actual relative first-projection isomorphisms
retain those same maps. Both original vertical endpoints and their
strict projection are therefore mapping weak equivalences. No marked
model structure is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

private theorem sourceEndpoint_absolute_weak (Y : Marked.{u})
    [KanComplex (mappingComplex .maximal (max (Δ[0] : SSet.{u})) Y)]
    [KanComplex (mappingComplex .maximal (max (Δ[1] : SSet.{u})) Y)] :
    realizationWeakEquivalences (mappingComplexPre .maximal (maximal.map (SSet.stdSimplex.δ (1 : Fin 2))) Y) := by
  let f : max (Δ[0] : SSet.{u}) ⟶ max (Δ[1] : SSet.{u}) := maximal.map (SSet.stdSimplex.δ 1)
  let g : max (Δ[1] : SSet.{u}) ⟶ max (Δ[0] : SSet.{u}) := maximal.map (SSet.stdSimplex.σ (0 : Fin 1))
  have hfg : f ≫ g = 𝟙 (max (Δ[0] : SSet.{u})) := by
    apply Hom.ext
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have h₀ : prodMap (maximal.map (SSet.stdSimplex.δ (1 : Fin 2))) (𝟙 (max (Δ[1] : SSet.{u}))) ≫
      markedIntervalMinimum = (zeroParameterUnitIso .maximal (max (Δ[1] : SSet.{u}))).hom ≫ (g ≫ f) :=
    markedIntervalMinimum_source.trans (congrArg (fun q => (zeroParameterUnitIso .maximal (max (Δ[1] :
      SSet.{u}))).hom ≫ q)
      (CategoryTheory.Functor.map_comp maximal (SSet.stdSimplex.σ (0 : Fin 1)) (SSet.stdSimplex.δ 1)))
  exact mappingComplexPre_realizationWeakEquivalence_of_contraction f g hfg markedIntervalMinimum h₀
    markedIntervalMinimum_target

/-- The original vertical source endpoint is weak for every actual cartesian target mapping test over the point. -/
theorem pointSourceEndpoint_cartesian_weak :
    cartesianWeakEquivalences (Δ[0] : SSet.{u}) (pointEndpoint.{u} (1 : Fin 2)) := by
  apply (cartesianWeakEquivalences_iff _).mpr
  intro Y
  let _ : KanComplex (mappingComplex .maximal (max (Δ[0] : SSet.{u})) Y.obj.left) :=
    maximalMapping_cartesianPoint_kan _ Y
  let _ : KanComplex (mappingComplex .maximal (max (Δ[1] : SSet.{u})) Y.obj.left) :=
    maximalMapping_cartesianPoint_kan _ Y
  have h : realizationWeakEquivalences (mappingComplexPre .maximal (pointEndpoint.{u} 1).left Y.obj.left) :=
    sourceEndpoint_absolute_weak Y.obj.left
  exact (realizationWeakEquivalences.arrow_iso_iff (overPointMappingRestrictionIso (pointEndpoint.{u} 1))).mpr h

/-- The same original strict interval projection is cartesian mapping weak over the point. -/
theorem pointIntervalProjection_cartesian_weak :
    cartesianWeakEquivalences (Δ[0] : SSet.{u}) pointIntervalProjection.{u} := by
  let _ := cartesianWeakEquivalences_hasTwoOutOfThreeProperty (Δ[0] : SSet.{u})
  let _ := cartesianWeakEquivalences_containsIdentities (Δ[0] : SSet.{u})
  have h : cartesianWeakEquivalences (Δ[0] : SSet.{u}) (pointEndpoint.{u} 1 ≫ pointIntervalProjection) :=
    (pointEndpoint_projection.{u} 1).symm ▸ MorphismProperty.id_mem _ _
  exact (cartesianWeakEquivalences (Δ[0] : SSet.{u})).of_precomp _ _ pointSourceEndpoint_cartesian_weak h

/-- The other whole original vertical endpoint is also cartesian mapping weak. -/
theorem pointTargetEndpoint_cartesian_weak :
    cartesianWeakEquivalences (Δ[0] : SSet.{u}) (pointEndpoint.{u} (0 : Fin 2)) := by
  let _ := cartesianWeakEquivalences_hasTwoOutOfThreeProperty (Δ[0] : SSet.{u})
  let _ := cartesianWeakEquivalences_containsIdentities (Δ[0] : SSet.{u})
  have h : cartesianWeakEquivalences (Δ[0] : SSet.{u}) (pointEndpoint.{u} 0 ≫ pointIntervalProjection) :=
    (pointEndpoint_projection.{u} 0).symm ▸ MorphismProperty.id_mem _ _
  exact (cartesianWeakEquivalences (Δ[0] : SSet.{u})).of_postcomp _ _ pointIntervalProjection_cartesian_weak h

/-- The original vertical source endpoint is weak for every actual cocartesian target mapping test over the point. -/
theorem pointSourceEndpoint_cocartesian_weak :
    cocartesianWeakEquivalences (Δ[0] : SSet.{u}) (pointEndpoint.{u} (1 : Fin 2)) := by
  apply (cocartesianWeakEquivalences_iff _).mpr
  intro Y
  let _ : KanComplex (mappingComplex .maximal (max (Δ[0] : SSet.{u})) Y.obj.left) :=
    maximalMapping_cocartesianPoint_kan _ Y
  let _ : KanComplex (mappingComplex .maximal (max (Δ[1] : SSet.{u})) Y.obj.left) :=
    maximalMapping_cocartesianPoint_kan _ Y
  have h : realizationWeakEquivalences (mappingComplexPre .maximal (pointEndpoint.{u} 1).left Y.obj.left) :=
    sourceEndpoint_absolute_weak Y.obj.left
  exact (realizationWeakEquivalences.arrow_iso_iff (overPointMappingRestrictionIso (pointEndpoint.{u} 1))).mpr h

/-- The same original strict interval projection is cocartesian mapping weak over the point. -/
theorem pointIntervalProjection_cocartesian_weak :
    cocartesianWeakEquivalences (Δ[0] : SSet.{u}) pointIntervalProjection.{u} := by
  let _ := cocartesianWeakEquivalences_hasTwoOutOfThreeProperty (Δ[0] : SSet.{u})
  let _ := cocartesianWeakEquivalences_containsIdentities (Δ[0] : SSet.{u})
  have h : cocartesianWeakEquivalences (Δ[0] : SSet.{u}) (pointEndpoint.{u} 1 ≫ pointIntervalProjection) :=
    (pointEndpoint_projection.{u} 1).symm ▸ MorphismProperty.id_mem _ _
  exact (cocartesianWeakEquivalences (Δ[0] : SSet.{u})).of_precomp _ _ pointSourceEndpoint_cocartesian_weak h

/-- The other whole original vertical endpoint is also cocartesian mapping weak. -/
theorem pointTargetEndpoint_cocartesian_weak :
    cocartesianWeakEquivalences (Δ[0] : SSet.{u}) (pointEndpoint.{u} (0 : Fin 2)) := by
  let _ := cocartesianWeakEquivalences_hasTwoOutOfThreeProperty (Δ[0] : SSet.{u})
  let _ := cocartesianWeakEquivalences_containsIdentities (Δ[0] : SSet.{u})
  have h : cocartesianWeakEquivalences (Δ[0] : SSet.{u}) (pointEndpoint.{u} 0 ≫ pointIntervalProjection) :=
    (pointEndpoint_projection.{u} 0).symm ▸ MorphismProperty.id_mem _ _
  exact (cocartesianWeakEquivalences (Δ[0] : SSet.{u})).of_postcomp _ _ pointIntervalProjection_cocartesian_weak h

end SSet.Marked
