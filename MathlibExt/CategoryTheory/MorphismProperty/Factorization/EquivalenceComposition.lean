/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence

/-!
# Complete given factorization data through composed actual equivalences

The two routes use the same supplied middle functor and its complete natural
maps. The actual units and counits of the given equivalences provide every
comparison. No factorization is selected again.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe uC vC uD vD uE vE
open CategoryTheory

namespace CategoryTheory.Equivalence

/-- The composite counit keeps both supplied counit components. -/
theorem originalFactorization_trans_counit_hom {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
    (e : C ≌ D) (f : D ≌ E) (X : E) :
    (e.trans f).counitIso.hom.app X =
      f.functor.map (e.counitIso.hom.app (f.inverse.obj X)) ≫ f.counitIso.hom.app X := by
  dsimp [Equivalence.trans]
  simp only [Category.comp_id, Category.id_comp]

/-- The composite inverse counit keeps both supplied inverse components. -/
theorem originalFactorization_trans_counit_inv {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
    (e : C ≌ D) (f : D ≌ E) (X : E) :
    (e.trans f).counitIso.inv.app X =
      f.counitIso.inv.app X ≫ f.functor.map (e.counitIso.inv.app (f.inverse.obj X)) := by
  dsimp [Equivalence.trans]
  simp only [Category.comp_id, Category.id_comp]

end CategoryTheory.Equivalence

namespace CategoryTheory.MorphismProperty.FunctorialFactorizationData

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E]
  {W₁ W₂ : MorphismProperty E} [W₁.RespectsIso] [W₂.RespectsIso]

/-- The full iterated middle functor is literally the direct composite route. -/
theorem ofEquivalence_trans_Z (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : D ≌ E) :
    ((data.ofEquivalence f).ofEquivalence e).Z =
      (data.ofEquivalence (e.trans f)).Z := rfl

/-- The two routes preserve every complete Arrow map. -/
theorem ofEquivalence_trans_Z_map (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : D ≌ E) {a b : Arrow C} (φ : a ⟶ b) :
    ((data.ofEquivalence f).ofEquivalence e).Z.map φ =
      e.inverse.map (f.inverse.map
        (data.Z.map (f.functor.mapArrow.map (e.functor.mapArrow.map φ)))) := rfl

/-- The iterated left map exposes both original units and the original left map. -/
theorem ofEquivalence_trans_i_explicit (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : D ≌ E) (a : Arrow C) :
    ((data.ofEquivalence f).ofEquivalence e).i.app a =
      e.unitIso.hom.app a.left ≫ e.inverse.map
        (f.unitIso.hom.app (e.functor.obj a.left) ≫
          f.inverse.map (data.i.app (f.functor.mapArrow.obj (e.functor.mapArrow.obj a)))) :=
  rfl

/-- The iterated right map exposes both original inverse units and the original right map. -/
theorem ofEquivalence_trans_p_explicit (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : D ≌ E) (a : Arrow C) :
    ((data.ofEquivalence f).ofEquivalence e).p.app a =
      e.inverse.map
        (f.inverse.map (data.p.app (f.functor.mapArrow.obj (e.functor.mapArrow.obj a))) ≫
          f.unitIso.inv.app (e.functor.obj a.right)) ≫ e.unitIso.inv.app a.right := rfl

/-- The direct and iterated routes have exactly the same original left component. -/
theorem ofEquivalence_trans_i (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : D ≌ E) (a : Arrow C) :
    ((data.ofEquivalence f).ofEquivalence e).i.app a =
      (data.ofEquivalence (e.trans f)).i.app a := by
  dsimp [ofEquivalence, Equivalence.trans]
  simp only [Functor.map_comp, Category.assoc, Category.comp_id, Category.id_comp]

/-- The direct and iterated routes have exactly the same original right component. -/
theorem ofEquivalence_trans_p (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : D ≌ E) (a : Arrow C) :
    ((data.ofEquivalence f).ofEquivalence e).p.app a =
      (data.ofEquivalence (e.trans f)).p.app a := by
  dsimp [ofEquivalence, Equivalence.trans]
  simp only [Functor.map_comp, Category.assoc, Category.comp_id, Category.id_comp]

/-- The complete iterated maps factor the original caller Arrow. -/
theorem ofEquivalence_trans_fac (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : D ≌ E) (a : Arrow C) :
    ((data.ofEquivalence f).ofEquivalence e).i.app a ≫
      ((data.ofEquivalence f).ofEquivalence e).p.app a = a.hom :=
  ((data.ofEquivalence f).ofEquivalence e).fac_app

/-- The full middle comparison is the direct composite counit on the same original data. -/
def ofEquivalenceTransComparisonIso (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : D ≌ E) :
    ((data.ofEquivalence f).ofEquivalence e).Z ⋙ (e.functor ⋙ f.functor) ≅
      (e.functor ⋙ f.functor).mapArrow ⋙ data.Z :=
  data.ofEquivalenceZComparisonIso (e.trans f)

/-- Both original counits occur in the full intermediate comparison component. -/
theorem ofEquivalenceTransComparisonIso_hom_app
    (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) (f : D ≌ E)
    (a : Arrow C) :
    (data.ofEquivalenceTransComparisonIso e f).hom.app a =
      f.functor.map (e.counitIso.hom.app
        (f.inverse.obj (data.Z.obj ((e.functor ⋙ f.functor).mapArrow.obj a)))) ≫
          f.counitIso.hom.app (data.Z.obj ((e.functor ⋙ f.functor).mapArrow.obj a)) :=
  Equivalence.originalFactorization_trans_counit_hom e f _

/-- The inverse component retains both original inverse counits. -/
theorem ofEquivalenceTransComparisonIso_inv_app
    (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) (f : D ≌ E)
    (a : Arrow C) :
    (data.ofEquivalenceTransComparisonIso e f).inv.app a =
      f.counitIso.inv.app (data.Z.obj ((e.functor ⋙ f.functor).mapArrow.obj a)) ≫
        f.functor.map (e.counitIso.inv.app
          (f.inverse.obj (data.Z.obj ((e.functor ⋙ f.functor).mapArrow.obj a)))) :=
  Equivalence.originalFactorization_trans_counit_inv e f _

/-- The full composite comparison recovers the exact original left factor. -/
theorem ofEquivalence_trans_mapped_i (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : D ≌ E) (a : Arrow C) :
    (e.functor ⋙ f.functor).map (((data.ofEquivalence f).ofEquivalence e).i.app a) ≫
      (data.ofEquivalenceTransComparisonIso e f).hom.app a =
        data.i.app ((e.functor ⋙ f.functor).mapArrow.obj a) := by
  rw [ofEquivalence_trans_i]
  exact data.ofEquivalence_mapped_i (e.trans f) a

/-- The full composite comparison recovers the exact original right factor. -/
theorem ofEquivalence_trans_mapped_p (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : D ≌ E) (a : Arrow C) :
    (data.ofEquivalenceTransComparisonIso e f).hom.app a ≫
      data.p.app ((e.functor ⋙ f.functor).mapArrow.obj a) =
        (e.functor ⋙ f.functor).map (((data.ofEquivalence f).ofEquivalence e).p.app a) := by
  rw [ofEquivalence_trans_p]
  exact data.ofEquivalence_mapped_p (e.trans f) a

/-- Every arbitrary original Arrow square commutes with the complete counit comparison. -/
theorem ofEquivalence_trans_naturality (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : D ≌ E) {a b : Arrow C} (φ : a ⟶ b) :
    (e.functor ⋙ f.functor).map (((data.ofEquivalence f).ofEquivalence e).Z.map φ) ≫
      (data.ofEquivalenceTransComparisonIso e f).hom.app b =
        (data.ofEquivalenceTransComparisonIso e f).hom.app a ≫
          data.Z.map ((e.functor ⋙ f.functor).mapArrow.map φ) :=
  (data.ofEquivalenceTransComparisonIso e f).hom.naturality φ

/-- The inverse full comparison also commutes with every original Arrow square. -/
theorem ofEquivalence_trans_inverse_naturality (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : D ≌ E) {a b : Arrow C} (φ : a ⟶ b) :
    data.Z.map ((e.functor ⋙ f.functor).mapArrow.map φ) ≫
      (data.ofEquivalenceTransComparisonIso e f).inv.app b =
        (data.ofEquivalenceTransComparisonIso e f).inv.app a ≫
          (e.functor ⋙ f.functor).map (((data.ofEquivalence f).ofEquivalence e).Z.map φ) :=
  (data.ofEquivalenceTransComparisonIso e f).inv.naturality φ

end CategoryTheory.MorphismProperty.FunctorialFactorizationData
