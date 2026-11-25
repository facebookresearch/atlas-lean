/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Localization.Equivalence
public import Mathlib.CategoryTheory.Localization.Construction

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v u' v'
open CategoryTheory

namespace CategoryTheory.Localization
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- The given original carrier equivalence lifts to complete literal localization functors. -/
def originalForward (e : C ≌ D) (W : MorphismProperty C) (W' : MorphismProperty D)
    (h : W.IsInvertedBy (e.functor ⋙ W'.Q)) :=
  Construction.lift (e.functor ⋙ W'.Q) h

/-- Its actual original inverse lifts through the exact other weak class. -/
def originalInverse (e : C ≌ D) (W : MorphismProperty C) (W' : MorphismProperty D)
    (h : W'.IsInvertedBy (e.inverse ⋙ W.Q)) :=
  Construction.lift (e.inverse ⋙ W.Q) h

/-- The whole forward original object/map projection is strict. -/
theorem originalForward_projection (e : C ≌ D) (W : MorphismProperty C)
    (W' : MorphismProperty D) (h : W.IsInvertedBy (e.functor ⋙ W'.Q)) :
    W.Q ⋙ originalForward e W W' h = e.functor ⋙ W'.Q := Construction.fac _ _

/-- The entire given inverse object/map projection is strict. -/
theorem originalInverse_projection (e : C ≌ D) (W : MorphismProperty C)
    (W' : MorphismProperty D) (h : W'.IsInvertedBy (e.inverse ⋙ W.Q)) :
    W'.Q ⋙ originalInverse e W W' h = e.inverse ⋙ W.Q := Construction.fac _ _

/-- Every whole original source morphism has its strict image under the given Ho lift. -/
theorem originalForward_map_projected (e : C ≌ D) (W : MorphismProperty C)
    (W' : MorphismProperty D) (h : W.IsInvertedBy (e.functor ⋙ W'.Q))
    {X Y : C} (f : X ⟶ Y) :
    (originalForward e W W' h).map (W.Q.map f) = W'.Q.map (e.functor.map f) :=
  Functor.congr_hom (originalForward_projection e W W' h) f

/-- Every original target morphism has its strict image under the given inverse Ho lift. -/
theorem originalInverse_map_projected (e : C ≌ D) (W : MorphismProperty C)
    (W' : MorphismProperty D) (h : W'.IsInvertedBy (e.inverse ⋙ W.Q))
    {X Y : D} (f : X ⟶ Y) :
    (originalInverse e W W' h).map (W'.Q.map f) = W.Q.map (e.inverse.map f) :=
  Functor.congr_hom (originalInverse_projection e W W' h) f

/-- The actual original forward/inverse roundtrip preserves its full projected source functor. -/
theorem originalForwardInverse_projection (e : C ≌ D) (W : MorphismProperty C)
    (W' : MorphismProperty D) (h : W.IsInvertedBy (e.functor ⋙ W'.Q))
    (h' : W'.IsInvertedBy (e.inverse ⋙ W.Q)) :
    W.Q ⋙ (originalForward e W W' h ⋙ originalInverse e W W' h') =
      (e.functor ⋙ e.inverse) ⋙ W.Q := by
  calc
    W.Q ⋙ (originalForward e W W' h ⋙ originalInverse e W W' h') =
        (W.Q ⋙ originalForward e W W' h) ⋙ originalInverse e W W' h' := rfl
    _ = (e.functor ⋙ W'.Q) ⋙ originalInverse e W W' h' := by
      rw [originalForward_projection]
    _ = e.functor ⋙ (W'.Q ⋙ originalInverse e W W' h') := rfl
    _ = e.functor ⋙ (e.inverse ⋙ W.Q) := by rw [originalInverse_projection]
    _ = _ := rfl

/-- The actual original inverse/forward roundtrip keeps its full target projection. -/
theorem originalInverseForward_projection (e : C ≌ D) (W : MorphismProperty C)
    (W' : MorphismProperty D) (h : W.IsInvertedBy (e.functor ⋙ W'.Q))
    (h' : W'.IsInvertedBy (e.inverse ⋙ W.Q)) :
    W'.Q ⋙ (originalInverse e W W' h' ⋙ originalForward e W W' h) =
      (e.inverse ⋙ e.functor) ⋙ W'.Q := by
  calc
    W'.Q ⋙ (originalInverse e W W' h' ⋙ originalForward e W W' h) =
        (W'.Q ⋙ originalInverse e W W' h') ⋙ originalForward e W W' h := rfl
    _ = (e.inverse ⋙ W.Q) ⋙ originalForward e W W' h := by
      rw [originalInverse_projection]
    _ = e.inverse ⋙ (W.Q ⋙ originalForward e W W' h) := rfl
    _ = e.inverse ⋙ (e.functor ⋙ W'.Q) := by rw [originalForward_projection]
    _ = _ := rfl

/-- The exact original unit lifts through the whole source localization, with its given maps. -/
def originalUnitIso (e : C ≌ D) (W : MorphismProperty C) (W' : MorphismProperty D)
    (h : W.IsInvertedBy (e.functor ⋙ W'.Q))
    (h' : W'.IsInvertedBy (e.inverse ⋙ W.Q)) :
    𝟭 W.Localization ≅ originalForward e W W' h ⋙ originalInverse e W W' h' := by
  let _ : Lifting W.Q W ((e.functor ⋙ e.inverse) ⋙ W.Q)
      (originalForward e W W' h ⋙ originalInverse e W W' h') :=
    ⟨eqToIso (originalForwardInverse_projection e W W' h h')⟩
  exact liftNatIso W.Q W W.Q ((e.functor ⋙ e.inverse) ⋙ W.Q) (𝟭 W.Localization)
    (originalForward e W W' h ⋙ originalInverse e W W' h') (Functor.isoWhiskerRight e.unitIso W.Q)

/-- The exact original counit lifts to the full target localization without a new choice. -/
def originalCounitIso (e : C ≌ D) (W : MorphismProperty C) (W' : MorphismProperty D)
    (h : W.IsInvertedBy (e.functor ⋙ W'.Q))
    (h' : W'.IsInvertedBy (e.inverse ⋙ W.Q)) :
    originalInverse e W W' h' ⋙ originalForward e W W' h ≅ 𝟭 W'.Localization := by
  let _ : Lifting W'.Q W' ((e.inverse ⋙ e.functor) ⋙ W'.Q)
      (originalInverse e W W' h' ⋙ originalForward e W W' h) :=
    ⟨eqToIso (originalInverseForward_projection e W W' h h')⟩
  exact liftNatIso W'.Q W' ((e.inverse ⋙ e.functor) ⋙ W'.Q) W'.Q
    (originalInverse e W W' h' ⋙ originalForward e W W' h) (𝟭 W'.Localization)
    (Functor.isoWhiskerRight e.counitIso W'.Q)

/-- The complete actual projected unit is the original given source component. -/
theorem originalUnitIso_hom_projected (e : C ≌ D) (W : MorphismProperty C)
    (W' : MorphismProperty D) (h : W.IsInvertedBy (e.functor ⋙ W'.Q))
    (h' : W'.IsInvertedBy (e.inverse ⋙ W.Q)) (X : C) :
    (originalUnitIso e W W' h h').hom.app (W.Q.obj X) = W.Q.map (e.unitIso.hom.app X) := by
  rw [originalUnitIso, liftNatIso_hom, liftNatTrans_app]
  change (𝟙 _ ≫ W.Q.map (e.unitIso.hom.app X)) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

/-- The full projected unit inverse is the original given inverse source component. -/
theorem originalUnitIso_inv_projected (e : C ≌ D) (W : MorphismProperty C)
    (W' : MorphismProperty D) (h : W.IsInvertedBy (e.functor ⋙ W'.Q))
    (h' : W'.IsInvertedBy (e.inverse ⋙ W.Q)) (X : C) :
    (originalUnitIso e W W' h h').inv.app (W.Q.obj X) = W.Q.map (e.unitIso.inv.app X) := by
  rw [originalUnitIso, liftNatIso_inv, liftNatTrans_app]
  change (𝟙 _ ≫ W.Q.map (e.unitIso.inv.app X)) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

/-- The complete actual projected counit is the original given target component. -/
theorem originalCounitIso_hom_projected (e : C ≌ D) (W : MorphismProperty C)
    (W' : MorphismProperty D) (h : W.IsInvertedBy (e.functor ⋙ W'.Q))
    (h' : W'.IsInvertedBy (e.inverse ⋙ W.Q)) (X : D) :
    (originalCounitIso e W W' h h').hom.app (W'.Q.obj X) = W'.Q.map (e.counitIso.hom.app X) := by
  rw [originalCounitIso, liftNatIso_hom, liftNatTrans_app]
  change (𝟙 _ ≫ W'.Q.map (e.counitIso.hom.app X)) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

/-- The full projected counit inverse is the original given inverse target component. -/
theorem originalCounitIso_inv_projected (e : C ≌ D) (W : MorphismProperty C)
    (W' : MorphismProperty D) (h : W.IsInvertedBy (e.functor ⋙ W'.Q))
    (h' : W'.IsInvertedBy (e.inverse ⋙ W.Q)) (X : D) :
    (originalCounitIso e W W' h h').inv.app (W'.Q.obj X) = W'.Q.map (e.counitIso.inv.app X) := by
  rw [originalCounitIso, liftNatIso_inv, liftNatTrans_app]
  change (𝟙 _ ≫ W'.Q.map (e.counitIso.inv.app X)) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

/-- The original equivalence triangle holds on every actual source localization object. -/
theorem originalForward_triangle (e : C ≌ D) (W : MorphismProperty C)
    (W' : MorphismProperty D) (h : W.IsInvertedBy (e.functor ⋙ W'.Q))
    (h' : W'.IsInvertedBy (e.inverse ⋙ W.Q)) :
    Functor.whiskerRight (originalUnitIso e W W' h h').hom (originalForward e W W' h) ≫
      Functor.whiskerLeft (originalForward e W W' h) (originalCounitIso e W W' h h').hom =
        𝟙 (originalForward e W W' h) := by
  apply natTrans_ext W.Q W
  intro X
  change (originalForward e W W' h).map ((originalUnitIso e W W' h h').hom.app (W.Q.obj X)) ≫
    (originalCounitIso e W W' h h').hom.app (W'.Q.obj (e.functor.obj X)) = 𝟙 _
  have hu := congrArg (originalForward e W W' h).map
    (originalUnitIso_hom_projected e W W' h h' X)
  have hm := originalForward_map_projected e W W' h (e.unitIso.hom.app X)
  have hc := originalCounitIso_hom_projected e W W' h h' (e.functor.obj X)
  refine (congrArg (fun f => f ≫ (originalCounitIso e W W' h h').hom.app
    (W'.Q.obj (e.functor.obj X))) (hu.trans hm)).trans ?_
  refine (congrArg (fun f => W'.Q.map (e.functor.map (e.unitIso.hom.app X)) ≫ f) hc).trans ?_
  exact (W'.Q.map_comp _ _).symm.trans
    ((congrArg W'.Q.map (e.functor_unit_comp X)).trans (W'.Q.map_id _))

/-- The whole localization equivalence retains the given original inverse, unit and counit. -/
def originalEquivalence (e : C ≌ D) (W : MorphismProperty C) (W' : MorphismProperty D)
    (h : W.IsInvertedBy (e.functor ⋙ W'.Q))
    (h' : W'.IsInvertedBy (e.inverse ⋙ W.Q)) : W.Localization ≌ W'.Localization where
  functor := originalForward e W W' h
  inverse := originalInverse e W W' h'
  unitIso := originalUnitIso e W W' h h'
  counitIso := originalCounitIso e W W' h h'
  functor_unitIso_comp X := congr_app (originalForward_triangle e W W' h h') X

/-- The inverse localization equivalence retains the full original counit inverse as its unit. -/
theorem originalEquivalence_unitIso_symm (e : C ≌ D) (W : MorphismProperty C)
    (W' : MorphismProperty D) (h : W.IsInvertedBy (e.functor ⋙ W'.Q))
    (h' : W'.IsInvertedBy (e.inverse ⋙ W.Q)) :
    (originalEquivalence e.symm W' W h' h).unitIso =
      (originalEquivalence e W W' h h').counitIso.symm := by
  apply Iso.ext
  apply natTrans_ext W'.Q W'
  intro Y
  exact (originalUnitIso_hom_projected e.symm W' W h' h Y).trans
    (originalCounitIso_inv_projected e W W' h h' Y).symm

/-- The inverse localization equivalence retains the full original unit inverse as its counit. -/
theorem originalEquivalence_counitIso_symm (e : C ≌ D) (W : MorphismProperty C)
    (W' : MorphismProperty D) (h : W.IsInvertedBy (e.functor ⋙ W'.Q))
    (h' : W'.IsInvertedBy (e.inverse ⋙ W.Q)) :
    (originalEquivalence e.symm W' W h' h).counitIso =
      (originalEquivalence e W W' h h').unitIso.symm := by
  apply Iso.ext
  apply natTrans_ext W.Q W
  intro X
  exact (originalCounitIso_hom_projected e.symm W' W h' h X).trans
    (originalUnitIso_inv_projected e W W' h h' X).symm

end CategoryTheory.Localization
