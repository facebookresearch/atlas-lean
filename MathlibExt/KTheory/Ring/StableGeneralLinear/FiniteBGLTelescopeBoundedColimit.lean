/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeBoundedStage
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarNerve
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# The original telescope nerve as a filtered union of bounded pieces

An original composable-arrow simplex is bounded by the base of its last
object. Its lift into that full bounded subcategory has the same objects
and arrows. Equality of lifted simplices is detected by the original full
inclusion. These computations prove that the actual bounded nerve cofan
is colimiting, without a supplied homotopy-colimit or comparison witness.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Semiring R]

/-- The increasing diagram of full bounded pieces of the ORIGINAL
categorical telescope. Every transition is the original full inclusion. -/
public abbrev finiteBGLTelescopeBoundedCategoryDiagram : ℕ ⥤ Cat.{u, 0} where
  obj n := Cat.of (FiniteBGLTelescopeBoundedCategory R n)
  map {n m} f := (ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R m from
      fun X hX => hX.trans (leOfHom f))).toCatHom
  map_id n := by
    apply Cat.Hom.ext
    rfl
  map_comp f g := by
    apply Cat.Hom.ext
    rfl

/-- The literal nerve diagram of the original full bounded pieces. -/
public abbrev finiteBGLTelescopeBoundedNerveDiagram : ℕ ⥤ SSet.{u} :=
  finiteBGLTelescopeBoundedCategoryDiagram R ⋙ nerveFunctor.{u, 0}

/-- The original full inclusions form their actual nerve cofan into the
nerve of the ORIGINAL categorical telescope. -/
public abbrev finiteBGLTelescopeBoundedNerveCocone :
    Cocone (finiteBGLTelescopeBoundedNerveDiagram R) where
  pt := nerve (FiniteBGLTelescopeCategory R)
  ι.app n := nerveMap (finiteBGLTelescopeBoundedInclusion R n)
  ι.naturality {n m} f := by
    let F := ((finiteBGLTelescopeBoundedCategoryDiagram R).map f).toFunctor
    let G := finiteBGLTelescopeBoundedInclusion R m
    have hFG : F ⋙ G = finiteBGLTelescopeBoundedInclusion R n := rfl
    change nerveMap F ≫ nerveMap G =
      nerveMap (finiteBGLTelescopeBoundedInclusion R n) ≫ 𝟙 _
    exact ((nerveFunctor.{u, 0}).map_comp F.toCatHom G.toCatHom).symm.trans
      ((congrArg nerveMap hFG).trans (Category.comp_id _).symm)

private theorem finiteBGLTelescopeBoundedLiftCongr {n k : ℕ}
    {σ τ : Fin (k + 1) ⥤ FiniteBGLTelescopeCategory R} (h : σ = τ)
    (hσ : ∀ i, (σ.obj i).base ≤ n) (hτ : ∀ i, (τ.obj i).base ≤ n) :
    (finiteBGLTelescopeBound R n).lift σ hσ =
      (finiteBGLTelescopeBound R n).lift τ hτ := by
  cases h
  rfl

private theorem finiteBGLTelescopeBoundedNerveInjection
    (n : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    Function.Injective
      ((nerveMap (finiteBGLTelescopeBoundedInclusion R n)).app Δ) := by
  intro σ τ h
  change σ ⋙ finiteBGLTelescopeBoundedInclusion R n =
    τ ⋙ finiteBGLTelescopeBoundedInclusion R n at h
  exact finiteBGLTelescopeBoundedLiftCongr R h
    (fun i => (σ.obj i).property) (fun i => (τ.obj i).property)

private def finiteBGLTelescopeBoundedNerveDegreeIsColimit
    (Δ : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ (Type u)).obj Δ).mapCocone
      (finiteBGLTelescopeBoundedNerveCocone R)) := by
  let D := finiteBGLTelescopeBoundedNerveDiagram R ⋙
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj Δ
  let c := ((evaluation SimplexCategoryᵒᵖ (Type u)).obj Δ).mapCocone
    (finiteBGLTelescopeBoundedNerveCocone R)
  refine Types.FilteredColimit.isColimitOf' D c ?_ ?_
  · intro σ
    let n := (σ.obj (Fin.last Δ.unop.len)).base
    have hBound : ∀ i, (σ.obj i).base ≤ n := fun i =>
      leOfHom (σ.map (homOfLE (Fin.le_last i))).base
    let τ : (nerve (FiniteBGLTelescopeBoundedCategory R n)).obj Δ :=
      (finiteBGLTelescopeBound R n).lift σ hBound
    refine ⟨n, τ, ?_⟩
    change σ = τ ⋙ finiteBGLTelescopeBoundedInclusion R n
    rfl
  · intro n σ τ h
    have hστ : σ = τ := finiteBGLTelescopeBoundedNerveInjection R n Δ h
    exact ⟨n, 𝟙 n, congrArg (D.map (𝟙 n)) hστ⟩

/-- Every original telescope simplex has a finite last-object bound, and
the SAME bounded full inclusions therefore form a simplicial colimit. -/
public def finiteBGLTelescopeBoundedNerveCoconeIsColimit :
    IsColimit (finiteBGLTelescopeBoundedNerveCocone R) :=
  evaluationJointlyReflectsColimits _
    (finiteBGLTelescopeBoundedNerveDegreeIsColimit R)

/-- The actual bounded cofan injection is the original full inclusion. -/
public theorem finiteBGLTelescopeBoundedNerveCocone_ι (n : ℕ) :
    (finiteBGLTelescopeBoundedNerveCocone R).ι.app n =
      nerveMap (finiteBGLTelescopeBoundedInclusion R n) := by
  unfold finiteBGLTelescopeBoundedNerveCocone
  rfl

end AlgebraicKTheory.StableGL

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology HomotopicalAlgebra
open scoped TopCat.modelCategory

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Semiring R]

/-- Every original full bounded inclusion is monic on the ENTIRE original
nerve, using its actual faithful functor and injective object reader. -/
public theorem finiteBGLTelescopeBoundedInclusionNerve_mono (n : ℕ) :
    Mono (nerveMap (finiteBGLTelescopeBoundedInclusion R n)) := by
  let F := finiteBGLTelescopeBoundedInclusion R n
  let _ : F.Faithful := inferInstance
  have hObj : Function.Injective F.obj := by
    intro X Y h
    apply ObjectProperty.FullSubcategory.ext
    exact h
  exact SSet.nerveMap_mono_of_faithful F hObj

/-- Every ORIGINAL bounded nerve transition is monic, retaining the
literal original full inclusion and all original object/arrow readers. -/
public theorem finiteBGLTelescopeBoundedNerveTransition_mono
    {n m : ℕ} (f : n ⟶ m) :
    Mono ((finiteBGLTelescopeBoundedNerveDiagram R).map f) := by
  let F := ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R m from
      fun X hX => hX.trans (leOfHom f))
  let _ : F.Faithful := inferInstance
  have hObj : Function.Injective F.obj := by
    intro X Y h
    apply ObjectProperty.FullSubcategory.ext
    exact congrArg
      (fun c : FiniteBGLTelescopeBoundedCategory R m => c.obj) h
  change Mono (nerveMap F)
  exact SSet.nerveMap_mono_of_faithful F hObj

/-- The SAME original realized bounded transition is a model cofibration,
derived from its actual whole simplicial Mono. -/
public theorem finiteBGLTelescopeBoundedTopTransition_cofibration
    {n m : ℕ} (f : n ⟶ m) :
    Cofibration (SSet.toTop.map ((finiteBGLTelescopeBoundedNerveDiagram R).map f)) := by
  let _ : Mono ((finiteBGLTelescopeBoundedNerveDiagram R).map f) :=
    finiteBGLTelescopeBoundedNerveTransition_mono R f
  exact (cofibration_iff _).mpr
    (SSet.toTop_map_mem_realizedBoundaryLLP
      ((finiteBGLTelescopeBoundedNerveDiagram R).map f))

/-- The ORIGINAL bounded inclusion has the actual Hurewicz extension
property on every original realized point and whole interval family. -/
public theorem finiteBGLTelescopeBoundedTopTransition_isHurewiczCofibration
    {n m : ℕ} (f : n ⟶ m) :
    TopCat.IsHurewiczCofibration
      (SSet.toTop.map ((finiteBGLTelescopeBoundedNerveDiagram R).map f)) := by
  let _ : Mono ((finiteBGLTelescopeBoundedNerveDiagram R).map f) :=
    finiteBGLTelescopeBoundedNerveTransition_mono R f
  intro Z instZ g H h0
  exact @SSet.toTop_map_isHurewiczCofibration _ _
    ((finiteBGLTelescopeBoundedNerveDiagram R).map f) inferInstance Z instZ g H h0

/-- The actual ORIGINAL ordinary telescope is the colimit of its original
full bounded pieces. The cofan and every map are the original realizations. -/
public def finiteBGLTelescopeBoundedTopCoconeIsColimit :
    IsColimit (SSet.toTop.mapCocone (finiteBGLTelescopeBoundedNerveCocone R)) :=
  isColimitOfPreserves SSet.toTop (finiteBGLTelescopeBoundedNerveCoconeIsColimit R)

end AlgebraicKTheory.StableGL

end
