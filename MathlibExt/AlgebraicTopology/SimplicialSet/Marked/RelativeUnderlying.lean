/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingPostLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterForget
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Original unmarked fixed-base prisms and their marked inclusion

The unmarked fixed-base mapping complex is the native postcomposition
pullback over the original base-map point. Forgetting either parameter
marking maps into this same pullback, retaining both actual projections.
The map is monic. Its unmarked target is a quasicategory when the original
total-space map is inner; no fibrancy of the source or common base is used.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Postcomposition retains every original unmarked parameter prism. -/
def parameterMappingPost (X : SSet.{u}) {Y Z : SSet.{u}} (p : Y ⟶ Z) :
    parameterMapping X Y ⟶ parameterMapping X Z :=
  Functor.whiskerLeft (SSet.stdSimplex ⋙ tensorRight X).op (CategoryTheory.yoneda.map p)

/-- Marked postcomposition and forgetting retain the same whole original prism. -/
theorem mappingComplexUnderlying_post (k : ParameterMarking) (X : Marked.{u})
    {Y Z : Marked.{u}} (p : Y ⟶ Z) :
    mappingComplexPost k X p ≫ mappingComplexUnderlying k X Z =
      mappingComplexUnderlying k X Y ≫ parameterMappingPost X.toSSet p.hom := by
  cases k <;> ext n f <;> rfl

/-- Every original marked simplex has a distinct underlying complete prism. -/
theorem mappingComplexUnderlying_mono (k : ParameterMarking) (X Y : Marked.{u}) :
    Mono (mappingComplexUnderlying k X Y) := by
  let _ : ∀ n : SimplexCategoryᵒᵖ, Mono ((mappingComplexUnderlying k X Y).app n) := fun n =>
    (CategoryTheory.mono_iff_injective _).mpr (mappingComplexUnderlying_app_injective k X Y n)
  exact NatTrans.mono_of_mono_app _

/-- The unmarked base point is the original marked map with only its marking forgotten. -/
def parameterBasePoint {X Z : Marked.{u}} (r : X ⟶ Z) :
    (Δ[0] : SSet.{u}) ⟶ parameterMapping X.toSSet Z.toSSet :=
  mappingBasePoint .minimal r ≫ mappingComplexUnderlying .minimal X Z

/-- Both original zero-parameter markings give precisely the same unmarked base point. -/
theorem mappingBasePoint_underlying (k : ParameterMarking) {X Z : Marked.{u}} (r : X ⟶ Z) :
    mappingBasePoint k r ≫ mappingComplexUnderlying k X Z = parameterBasePoint r := by
  cases k
  · rfl
  · apply SSet.yonedaEquiv.injective
    dsimp only [mappingBasePoint, parameterBasePoint]
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl

/-- The original unmarked fixed-base prism complex is the actual postcomposition pullback. -/
def parameterRelative {X Y Z : Marked.{u}} (r : X ⟶ Z) (p : Y ⟶ Z) : SSet.{u} :=
  pullback (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)

/-- Forgetting marks retains both original projections of the fixed-base mapping complex. -/
def relativeMappingForget (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) :
    relativeMappingComplex k r p ⟶ parameterRelative r p :=
  let a : relativeMappingComplex k r p ⟶ mappingComplex k X Y :=
    pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)
  let b : relativeMappingComplex k r p ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r)
  pullback.lift
    (a ≫ mappingComplexUnderlying k X Y) b (by
      rw [Category.assoc, ← mappingComplexUnderlying_post, ← Category.assoc]
      have h : a ≫ mappingComplexPost k X p = b ≫ mappingBasePoint k r := pullback.condition
      rw [h, Category.assoc, mappingBasePoint_underlying])

/-- The original whole prism is the first projection after forgetting. -/
@[reassoc]
theorem relativeMappingForget_fst (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) :
    relativeMappingForget k r p ≫
        pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r) =
      pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r) ≫
        mappingComplexUnderlying k X Y := pullback.lift_fst _ _ _

/-- The original fixed-base point coordinate is unchanged. -/
@[reassoc]
theorem relativeMappingForget_snd (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) :
    relativeMappingForget k r p ≫
        pullback.snd (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r) =
      pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r) :=
  pullback.lift_snd _ _ _

/-- Forgetting the original relative marks identifies no original mapping simplex. -/
theorem relativeMappingForget_mono (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) : Mono (relativeMappingForget k r p) := by
  let _ : Mono (mappingComplexUnderlying k X Y) := mappingComplexUnderlying_mono k X Y
  refine ⟨fun {W} f g h => ?_⟩
  apply pullback.hom_ext
  · apply (cancel_mono (mappingComplexUnderlying k X Y)).mp
    have h' := congrArg (fun a => a ≫
      pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)) h
    change f ≫ (relativeMappingForget k r p ≫
        pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)) =
      g ≫ (relativeMappingForget k r p ≫
        pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)) at h'
    rw [relativeMappingForget_fst] at h'
    exact h'
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The native internal-Hom prism dictionary commutes with the same actual target map. -/
theorem parameterMappingIsoIhom_post (X : SSet.{u}) {Y Z : SSet.{u}} (p : Y ⟶ Z) :
    parameterMappingPost X p ≫ (parameterMappingIsoIhom X Z).hom =
      (parameterMappingIsoIhom X Y).hom ≫ (ihom X).map p := by
  ext n F
  exact (leftIhomSimplexOfPrism_post F p).symm

/-- Original unmarked postcomposition preserves the native inner-fibration lifting condition. -/
theorem parameterMappingPost_innerFibration (X : SSet.{u}) {Y Z : SSet.{u}}
    (p : Y ⟶ Z) [InnerFibration p] : InnerFibration (parameterMappingPost X p) := by
  let _ : InnerFibration ((ihom X).map p) :=
    innerFibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsInitial
      MonoidalClosed.internalHom (initial.to X) p initialIsInitial)
  have h : parameterMappingPost X p =
      (parameterMappingIsoIhom X Y).hom ≫ (ihom X).map p ≫
        (parameterMappingIsoIhom X Z).inv := by
    apply (cancel_mono (parameterMappingIsoIhom X Z).hom).mp
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      parameterMappingIsoIhom_post]
  rw [h]
  exact ⟨innerFibrations.comp_mem _ _ (innerHornInclusions.rlp_of_isIso _)
    (innerFibrations.comp_mem _ _ InnerFibration.mem (innerHornInclusions.rlp_of_isIso _))⟩

/-- The original unmarked fixed-base prism complex is a native quasicategory. -/
theorem parameterRelative_quasicategory {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) [InnerFibration p.hom] :
    Quasicategory (parameterRelative r p) := by
  let _ : InnerFibration (parameterMappingPost X.toSSet p.hom) :=
    parameterMappingPost_innerFibration X.toSSet p.hom
  let q : parameterRelative r p ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)
  let _ : InnerFibration q := ⟨innerFibrations.pullback_snd _ _ InnerFibration.mem⟩
  exact quasicategory_of_innerFibration q

end SSet.Marked
