/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingFibrancy
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexQuasicategory

/-!
# Original marked postcomposition and fixed-base mapping fibres

Postcomposition through an original inner fibration is inner on the actual
minimal marked mapping complexes. The unmarked lift lands in the original
full vertex subcomplex because all vertices already occur in the horn.
The literal fixed-base fibre is therefore a quasicategory, with its whole
original projection and base-map condition retained.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalClosed Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Actual marked postcomposition retains native inner horn lifting of the original target map. -/
theorem mappingComplexPost_min_innerFibration (X : Marked.{u}) {Y Z : Marked.{u}}
    (p : Y ⟶ Z) [InnerFibration p.hom] :
    InnerFibration (mappingComplexPost .minimal X p) := by
  let _ : InnerFibration ((ihom X.toSSet).map p.hom) :=
    innerFibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsInitial
      MonoidalClosed.internalHom (initial.to X.toSSet) p.hom initialIsInitial)
  let _ : InnerFibration (mappingComplexForget .minimal X Y) :=
    mappingComplexForget_min_innerFibration X Y
  let _ : Mono (mappingComplexForget .minimal X Z) := mappingComplexForget_min_mono X Z
  refine ⟨fun A B i hi => ?_⟩
  let _ : HasLiftingProperty i ((ihom X.toSSet).map p.hom) := InnerFibration.mem _ hi
  let _ : HasLiftingProperty i (mappingComplexForget .minimal X Y) := InnerFibration.mem _ hi
  refine ⟨fun {a b} sq => ?_⟩
  have hs : CommSq (a ≫ mappingComplexForget .minimal X Y) i
      ((ihom X.toSSet).map p.hom) (b ≫ mappingComplexForget .minimal X Z) := by
    constructor
    rw [Category.assoc, ← mappingComplexForget_post X p, ← Category.assoc, sq.w, Category.assoc]
  have hs' : CommSq a i (mappingComplexForget .minimal X Y) hs.lift :=
    ⟨hs.fac_left.symm⟩
  refine CommSq.HasLift.mk' ⟨hs'.lift, hs'.fac_left, ?_⟩
  apply (cancel_mono (mappingComplexForget .minimal X Z)).mp
  rw [Category.assoc, mappingComplexForget_post X p, ← Category.assoc,
    hs'.fac_right, hs.fac_right]

/-- The actual constant mapping simplex determined by the original marked base map. -/
def mappingBasePoint (k : ParameterMarking) {X Z : Marked.{u}} (r : X ⟶ Z) :
    (Δ[0] : SSet.{u}) ⟶ mappingComplex k X Z :=
  SSet.yonedaEquiv.symm ((mappingComplexZeroEquiv k X Z).symm r)

/-- The actual fixed-base mapping complex is the original postcomposition pullback over that point. -/
def relativeMappingComplex (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) : SSet.{u} :=
  pullback (mappingComplexPost k X p) (mappingBasePoint k r)

/-- The actual minimally parameter-marked fixed-base mapping complex is a quasicategory. -/
theorem relativeMappingComplex_min_quasicategory {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) [InnerFibration p.hom] :
    Quasicategory (relativeMappingComplex .minimal r p) := by
  let _ : InnerFibration (mappingComplexPost .minimal X p) :=
    mappingComplexPost_min_innerFibration X p
  let q : relativeMappingComplex .minimal r p ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost .minimal X p) (mappingBasePoint .minimal r)
  let _ : InnerFibration q :=
    ⟨innerFibrations.pullback_snd _ _ InnerFibration.mem⟩
  exact quasicategory_of_innerFibration q

end SSet.Marked
