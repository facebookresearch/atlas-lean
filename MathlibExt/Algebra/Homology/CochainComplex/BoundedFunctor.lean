/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.Bounded
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Functor comparisons on bounded cochains

Degreewise prolongations lift to bounded cochains. Natural transformations
and isomorphisms retain their components. Equivalences restrict to these
full subcategories with the degreewise unit and counit and the same support
windows.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD uE vE

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
  {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
  {E : Type uE} [Category.{vE} E] [HasZeroMorphisms E]

namespace Functor

variable (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- The original bounded differential is the literal original functor image. -/
theorem mapCochainComplexBounded_obj_d (K : CochainComplex.Bounded C) (i j : ℤ) :
    ((F.mapCochainComplexBounded).obj K).obj.d i j = F.map (K.obj.d i j) := rfl

/-- The whole original bounded inclusion square is the canonical full-subcategory lift square. -/
def mapCochainComplexBoundedCompιIso :
    F.mapCochainComplexBounded ⋙ CochainComplex.Bounded.ι D ≅
      CochainComplex.Bounded.ι C ⋙ F.mapHomologicalComplex (.up ℤ) := Iso.refl _

/-- A fully faithful original functor reflects the same original finite support windows. -/
theorem bounded_mapHomologicalComplex_obj_iff [F.Full] [F.Faithful]
    (K : CochainComplex C ℤ) :
    CochainComplex.bounded D ((F.mapHomologicalComplex (.up ℤ)).obj K) ↔
      CochainComplex.bounded C K := by
  constructor
  · rintro ⟨a, b, hK⟩
    exact ⟨a, b, fun j hj => IsZero.of_full_of_faithful_of_isZero F (K.X j) (hK j hj)⟩
  · exact bounded_mapHomologicalComplex_obj F K

end Functor

namespace NatTrans

variable {F G H : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [H.PreservesZeroMorphisms]

/-- Restrict the canonical degreewise natural transformation to the original bounded cochains. -/
def mapCochainComplexBounded (τ : F ⟶ G) :
    F.mapCochainComplexBounded ⟶ G.mapCochainComplexBounded where
  app K := ObjectProperty.homMk ((τ.mapHomologicalComplex (.up ℤ)).app K.obj)
  naturality K L f := by
    apply ObjectProperty.hom_ext
    exact (τ.mapHomologicalComplex (.up ℤ)).naturality f.hom

/-- The actual bounded comparison retains each given original component. -/
theorem mapCochainComplexBounded_app_f (τ : F ⟶ G) (K : CochainComplex.Bounded C) (j : ℤ) :
    ((τ.mapCochainComplexBounded).app K).hom.f j = τ.app (K.obj.X j) := rfl

/-- Identity comparisons remain the whole original identity transformation. -/
@[simp]
theorem mapCochainComplexBounded_id :
    mapCochainComplexBounded (𝟙 F) = 𝟙 F.mapCochainComplexBounded := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun τ => τ.app K.obj) (mapHomologicalComplex_id (.up ℤ) F)

/-- Composition uses the same original degreewise transformations. -/
theorem mapCochainComplexBounded_comp (τ : F ⟶ G) (σ : G ⟶ H) :
    (τ ≫ σ).mapCochainComplexBounded = τ.mapCochainComplexBounded ≫ σ.mapCochainComplexBounded := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun τ => τ.app K.obj) (mapHomologicalComplex_comp (.up ℤ) τ σ)

end NatTrans

namespace NatIso

variable {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

/-- An original natural isomorphism restricts with its original inverse components. -/
def mapCochainComplexBounded (e : F ≅ G) :
    F.mapCochainComplexBounded ≅ G.mapCochainComplexBounded where
  hom := e.hom.mapCochainComplexBounded
  inv := e.inv.mapCochainComplexBounded
  hom_inv_id := by
    rw [← NatTrans.mapCochainComplexBounded_comp, e.hom_inv_id,
      NatTrans.mapCochainComplexBounded_id]
  inv_hom_id := by
    rw [← NatTrans.mapCochainComplexBounded_comp, e.inv_hom_id,
      NatTrans.mapCochainComplexBounded_id]

/-- The whole original bounded isomorphism component is the canonical degreewise component. -/
theorem mapCochainComplexBounded_hom_app_f (e : F ≅ G) (K : CochainComplex.Bounded C) (j : ℤ) :
    ((NatIso.mapCochainComplexBounded e).hom.app K).hom.f j = e.hom.app (K.obj.X j) := rfl

/-- The actual inverse retains the original inverse component in every integer degree. -/
theorem mapCochainComplexBounded_inv_app_f (e : F ≅ G) (K : CochainComplex.Bounded C) (j : ℤ) :
    ((NatIso.mapCochainComplexBounded e).inv.app K).hom.f j = e.inv.app (K.obj.X j) := rfl

end NatIso

namespace Functor

/-- Composition of the actual bounded lifts retains the original prolongation comparison. -/
def mapCochainComplexBoundedCompIso (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    F.mapCochainComplexBounded ⋙ G.mapCochainComplexBounded ≅
      (F ⋙ G).mapCochainComplexBounded :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _
    ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).app K.obj)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.naturality f.hom)

/-- The identity bounded lift uses the canonical original degreewise identity comparison. -/
def mapCochainComplexBoundedIdIso :
    (𝟭 C).mapCochainComplexBounded ≅ 𝟭 (CochainComplex.Bounded C) :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _
    ((mapHomologicalComplexIdIso C (.up ℤ)).app K.obj)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (mapHomologicalComplexIdIso C (.up ℤ)).hom.naturality f.hom)

end Functor

namespace Equivalence

variable (e : C ≌ D) [e.functor.PreservesZeroMorphisms]

/-- Restrict the canonical degreewise equivalence to the original finite-support cochains. -/
def mapCochainComplexBounded : CochainComplex.Bounded C ≌ CochainComplex.Bounded D :=
  (e.mapHomologicalComplex (.up ℤ)).congrFullSubcategory (by
    ext K
    exact e.functor.bounded_mapHomologicalComplex_obj_iff K)

/-- The forward equivalence is literally the original bounded functor lift. -/
theorem mapCochainComplexBounded_functor :
    e.mapCochainComplexBounded.functor = e.functor.mapCochainComplexBounded := rfl

/-- Its inverse is literally the original bounded inverse-functor lift. -/
theorem mapCochainComplexBounded_inverse :
    e.mapCochainComplexBounded.inverse = e.inverse.mapCochainComplexBounded := rfl

/-- The original unit remains the actual unit component in every original degree. -/
theorem mapCochainComplexBounded_unitIso_hom_app_f (K : CochainComplex.Bounded C) (j : ℤ) :
    ((e.mapCochainComplexBounded).unitIso.hom.app K).hom.f j =
      e.unitIso.hom.app (K.obj.X j) := by
  simp [mapCochainComplexBounded, mapHomologicalComplex]
  rfl

/-- The original counit remains the actual counit component in every original degree. -/
theorem mapCochainComplexBounded_counitIso_hom_app_f (K : CochainComplex.Bounded D) (j : ℤ) :
    ((e.mapCochainComplexBounded).counitIso.hom.app K).hom.f j =
      e.counitIso.hom.app (K.obj.X j) := by
  simp [mapCochainComplexBounded, mapHomologicalComplex]
  rfl

end Equivalence

end CategoryTheory

end
