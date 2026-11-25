/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
Original authors: @junekim623, Muse

Original proof (no external Lean code adapted): the forgetful functor
`SheafOfModules.toSheaf R` from sheaves of modules to abelian sheaves preserves
colimits. A colimit of module sheaves is the sheafification of the colimit of
the underlying presheaf diagram; applying `toSheaf` turns module
sheafification into ordinary sheafification (`sheafificationCompToSheaf`), and
both steps preserve colimits, so the image cocone is identified with the
abelian sheafification of the presheaf colimit cocone, which is a colimit
cocone. The corollary for topological spaces yields preservation of cokernels
hence of all finite colimits, which is the exactness input for comparing
module-sheaf cohomology with abelian-sheaf cohomology.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Topology.Sheaves.Abelian

/-!
# The forgetful functor to abelian sheaves preserves colimits

The forgetful functor `SheafOfModules.toSheaf` from sheaves of modules to
abelian sheaves preserves colimits of any shape; over a topological space
this gives preservation of cokernels, hence of all finite colimits.
-/

@[expose] public section

open _root_.CategoryTheory CategoryTheory Limits _root_.TopologicalSpace TopologicalSpace

universe w w' v u u₁ v₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  {K : Type w} [Category.{w'} K]
  [HasColimitsOfShape K (PresheafOfModules.{v} R.obj)]
  [HasColimitsOfShape K AddCommGrpCat.{v}]

namespace SheafOfModules

/-- The forgetful functor from sheaves of modules to abelian sheaves preserves
colimits of shape `K`.

Given `F : K ⥤ SheafOfModules R`, write `F₀ := F ⋙ forget` for the underlying
presheaf-module diagram and `c₀` for its colimit cocone. Module sheafification
`S` (a left adjoint) sends `c₀` to a colimit cocone, which the counit
isomorphism `e : F ≅ F₀ ⋙ S` transports to a colimit cocone on `F`. On the
abelian side, `T := toPresheaf` and `P := presheafToSheaf` (both
colimit-preserving) send `c₀` to a colimit cocone, transported along the
diagram iso `n` (built from `e` and `sheafificationCompToSheaf`) to a colimit
cocone on `F ⋙ toSheaf`. The two cocones on `F ⋙ toSheaf` agree by naturality
of `sheafificationCompToSheaf`, so the image cocone is a colimit. -/
theorem preservesColimitsOfShape_toSheaf :
    PreservesColimitsOfShape K (SheafOfModules.toSheaf.{v} R) where
  preservesColimit {F} := by
    -- The counit of module sheafification is an isomorphism, so `F` is
    -- isomorphic to the sheafification of its underlying presheaf diagram
    -- (mirroring `SheafOfModules.hasColimit`).
    let e : F ≅ (F ⋙ SheafOfModules.forget R) ⋙
        PresheafOfModules.sheafification (𝟙 R.obj) :=
      Functor.isoWhiskerLeft F
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
    -- Colimit cocone of the underlying presheaf-module diagram.
    let c₀ := colimit.cocone (F ⋙ SheafOfModules.forget R)
    have hc₀ : IsColimit c₀ := colimit.isColimit _
    -- Its sheafification is a colimit cocone (left adjoint preserves).
    have hS : IsColimit ((PresheafOfModules.sheafification (𝟙 R.obj)).mapCocone
        c₀) :=
      isColimitOfPreserves _ hc₀
    -- Transport along `e` to a colimit cocone on `F` itself.
    have htS : IsColimit ((Cocone.precompose e.hom).obj
        ((PresheafOfModules.sheafification (𝟙 R.obj)).mapCocone c₀)) :=
      (IsColimit.precomposeHomEquiv e _).symm hS
    -- On the abelian side: forget to presheaves, then sheafify.
    have hTA : IsColimit ((PresheafOfModules.toPresheaf R.obj).mapCocone c₀) :=
      isColimitOfPreserves _ hc₀
    have hP : IsColimit ((presheafToSheaf J AddCommGrpCat.{v}).mapCocone
        ((PresheafOfModules.toPresheaf R.obj).mapCocone c₀)) :=
      isColimitOfPreserves _ hTA
    -- The comparison iso of abelian-sheaf diagrams, from `e` and the fact
    -- that `toSheaf` turns module sheafification into abelian sheafification.
    let σ := PresheafOfModules.sheafificationCompToSheaf (α := (𝟙 R.obj))
    let n : F ⋙ SheafOfModules.toSheaf R ≅
        (((F ⋙ SheafOfModules.forget R) ⋙
          PresheafOfModules.toPresheaf R.obj) ⋙
          presheafToSheaf J AddCommGrpCat.{v}) :=
      (Functor.isoWhiskerRight e _) ≪≫
        (Functor.associator _ _ _) ≪≫
        (Functor.isoWhiskerLeft _ σ) ≪≫
        (Functor.associator _ _ _).symm
    have htP : IsColimit ((Cocone.precompose n.hom).obj
        ((presheafToSheaf J AddCommGrpCat.{v}).mapCocone
          ((PresheafOfModules.toPresheaf R.obj).mapCocone c₀))) :=
      (IsColimit.precomposeHomEquiv n _).symm hP
    -- The image cocone agrees with the transported one by naturality of `σ`.
    have w : (SheafOfModules.toSheaf R).mapCocone
        ((Cocone.precompose e.hom).obj
          ((PresheafOfModules.sheafification (𝟙 R.obj)).mapCocone c₀)) ≅
        (Cocone.precompose n.hom).obj
          ((presheafToSheaf J AddCommGrpCat.{v}).mapCocone
            ((PresheafOfModules.toPresheaf R.obj).mapCocone c₀)) := by
      refine Cocone.ext (σ.app c₀.pt) (fun j => ?_)
      have hnj : n.hom.app j =
          (SheafOfModules.toSheaf R).map (e.hom.app j) ≫ (σ.app _).hom := by
        simp [n]
      have nat := σ.hom.naturality (c₀.ι.app j)
      have stepU : (SheafOfModules.toSheaf R).map
          ((PresheafOfModules.sheafification (𝟙 R.obj)).map (c₀.ι.app j)) =
          ((PresheafOfModules.sheafification (𝟙 R.obj) ⋙
            SheafOfModules.toSheaf R).map (c₀.ι.app j)) := rfl
      have stepP : (presheafToSheaf J AddCommGrpCat.{v}).map
          ((PresheafOfModules.toPresheaf R.obj).map (c₀.ι.app j)) =
          (((PresheafOfModules.toPresheaf R.obj) ⋙
            presheafToSheaf J AddCommGrpCat.{v}).map (c₀.ι.app j)) := rfl
      change (SheafOfModules.toSheaf R).map (e.hom.app j ≫
          (PresheafOfModules.sheafification (𝟙 R.obj)).map (c₀.ι.app j)) ≫
          (σ.app c₀.pt).hom =
        n.hom.app j ≫ (presheafToSheaf J AddCommGrpCat.{v}).map
          ((PresheafOfModules.toPresheaf R.obj).map (c₀.ι.app j))
      rw [hnj, Functor.map_comp, stepU, stepP, Category.assoc, Category.assoc]
      exact congrArg ((SheafOfModules.toSheaf R).map (e.hom.app j) ≫ ·) nat
    have hUtS : IsColimit ((SheafOfModules.toSheaf R).mapCocone
        ((Cocone.precompose e.hom).obj
          ((PresheafOfModules.sheafification (𝟙 R.obj)).mapCocone c₀))) :=
      htP.ofIsoColimit w.symm
    exact preservesColimit_of_preserves_colimit_cocone htS hUtS

section Topological

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  {M N : SheafOfModules.{u} R}

/-- Over a topological space, `toSheaf` preserves cokernels. The required
colimit hypotheses discharge against the abelian structures on presheaves and
sheaves of modules. -/
instance preservesColimit_toSheaf_parallelPair (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) (SheafOfModules.toSheaf.{u} R) := by
  have : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    inferInstance
  have : (Opens.grothendieckTopology X).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  have : HasColimitsOfShape WalkingParallelPair
      (PresheafOfModules.{u} R.obj) := inferInstance
  have : HasColimitsOfShape WalkingParallelPair AddCommGrpCat.{u} :=
    inferInstance
  exact preservesColimitsOfShape_toSheaf.preservesColimit

/-- Over a topological space, `toSheaf` preserves all finite colimits. -/
instance preservesFiniteColimits_toSheaf :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) := by
  have : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    inferInstance
  have : (Opens.grothendieckTopology X).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  exact Functor.preservesFiniteColimits_of_preservesCokernels
    (SheafOfModules.toSheaf.{u} R)

end Topological

end SheafOfModules

end
