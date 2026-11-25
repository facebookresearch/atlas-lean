/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.Equivalence

/-!
# Original functorial factorization data along an explicit equivalence

The given intermediate functor and natural maps are moved using exactly the
provided inverse, unit and counit. The source category receives no model or
desired factorization as an input.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe vC vD uC uD
open CategoryTheory

namespace CategoryTheory.MorphismProperty.FunctorialFactorizationData

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {W₁ W₂ : MorphismProperty D} [W₁.RespectsIso] [W₂.RespectsIso]

/-- Pull the complete original data back through the actual supplied inverse. -/
def ofEquivalence (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) :
    FunctorialFactorizationData (W₁.inverseImage e.functor) (W₂.inverseImage e.functor) where
  Z := e.functor.mapArrow ⋙ data.Z ⋙ e.inverse
  i :=
    { app f := e.unitIso.hom.app f.left ≫
        e.inverse.map (data.i.app (e.functor.mapArrow.obj f))
      naturality := by
        intro f g φ
        have hd : e.functor.map φ.left ≫ data.i.app (e.functor.mapArrow.obj g) =
            data.i.app (e.functor.mapArrow.obj f) ≫ data.Z.map (e.functor.mapArrow.map φ) :=
          data.i.naturality (e.functor.mapArrow.map φ)
        have hu : φ.left ≫ e.unitIso.hom.app g.left =
            e.unitIso.hom.app f.left ≫ e.inverse.map (e.functor.map φ.left) := by
          simpa only [Functor.id_map, Functor.comp_map] using e.unitIso.hom.naturality φ.left
        change φ.left ≫ (e.unitIso.hom.app g.left ≫
            e.inverse.map (data.i.app (e.functor.mapArrow.obj g))) =
          (e.unitIso.hom.app f.left ≫ e.inverse.map (data.i.app (e.functor.mapArrow.obj f))) ≫
            e.inverse.map (data.Z.map (e.functor.mapArrow.map φ))
        rw [← Category.assoc, hu]
        rw [Category.assoc, ← e.inverse.map_comp, hd, e.inverse.map_comp, Category.assoc] }
  p :=
    { app f := e.inverse.map (data.p.app (e.functor.mapArrow.obj f)) ≫
        e.unitIso.inv.app f.right
      naturality := by
        intro f g φ
        have hd : data.Z.map (e.functor.mapArrow.map φ) ≫ data.p.app (e.functor.mapArrow.obj g) =
            data.p.app (e.functor.mapArrow.obj f) ≫ e.functor.map φ.right :=
          data.p.naturality (e.functor.mapArrow.map φ)
        have hu : e.inverse.map (e.functor.map φ.right) ≫ e.unitIso.inv.app g.right =
            e.unitIso.inv.app f.right ≫ φ.right := by
          simpa only [Functor.id_map, Functor.comp_map] using e.unitIso.inv.naturality φ.right
        change e.inverse.map (data.Z.map (e.functor.mapArrow.map φ)) ≫
            (e.inverse.map (data.p.app (e.functor.mapArrow.obj g)) ≫ e.unitIso.inv.app g.right) =
          (e.inverse.map (data.p.app (e.functor.mapArrow.obj f)) ≫
            e.unitIso.inv.app f.right) ≫ φ.right
        rw [← Category.assoc, ← e.inverse.map_comp, hd, e.inverse.map_comp,
          Category.assoc, hu, Category.assoc] }
  fac := by
    ext f
    change (e.unitIso.hom.app f.left ≫ e.inverse.map (data.i.app (e.functor.mapArrow.obj f))) ≫
        (e.inverse.map (data.p.app (e.functor.mapArrow.obj f)) ≫ e.unitIso.inv.app f.right) = f.hom
    have hd : data.i.app (e.functor.mapArrow.obj f) ≫ data.p.app (e.functor.mapArrow.obj f) =
        e.functor.map f.hom := data.fac_app
    have hu : f.hom ≫ e.unitIso.hom.app f.right =
        e.unitIso.hom.app f.left ≫ e.inverse.map (e.functor.map f.hom) := by
      simpa only [Functor.id_map, Functor.comp_map] using e.unitIso.hom.naturality f.hom
    rw [Category.assoc, ← Category.assoc (e.inverse.map _) (e.inverse.map _) _,
      ← e.inverse.map_comp, hd, ← Category.assoc, ← hu,
      Category.assoc, e.unitIso.hom_inv_id_app]
    simpa only [Functor.id_obj] using Category.comp_id f.hom
  hi f := by
    have hc : e.functor.map (e.inverse.map (data.i.app (e.functor.mapArrow.obj f))) ≫
        e.counitIso.hom.app (data.Z.obj (e.functor.mapArrow.obj f)) =
      e.counitIso.hom.app (e.functor.obj f.left) ≫ data.i.app (e.functor.mapArrow.obj f) := by
      simpa only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj,
        Arrow.leftFunc_obj, Functor.mapArrow_obj, Arrow.mk_left] using
        e.counitIso.hom.naturality (data.i.app (e.functor.mapArrow.obj f))
    have h : (Iso.refl (e.functor.obj f.left)).hom ≫ data.i.app (e.functor.mapArrow.obj f) =
        e.functor.map (e.unitIso.hom.app f.left ≫
          e.inverse.map (data.i.app (e.functor.mapArrow.obj f))) ≫
        (e.counitIso.app (data.Z.obj (e.functor.mapArrow.obj f))).hom := by
      simp only [Iso.refl_hom, Iso.app_hom, Category.id_comp, Functor.map_comp]
      rw [Category.assoc, hc, ← Category.assoc,
        e.functor_unitIso_comp f.left]
      symm
      simpa only [Arrow.leftFunc_obj, Functor.mapArrow_obj, Arrow.mk_left] using
        Category.id_comp (data.i.app (e.functor.mapArrow.obj f))
    let q : Arrow.mk (e.functor.map (e.unitIso.hom.app f.left ≫
        e.inverse.map (data.i.app (e.functor.mapArrow.obj f)))) ≅
        Arrow.mk (data.i.app (e.functor.mapArrow.obj f)) :=
      Arrow.isoMk (Iso.refl (e.functor.obj f.left))
      (e.counitIso.app (data.Z.obj (e.functor.mapArrow.obj f))) h
    exact (W₁.arrow_mk_iso_iff q).2 (data.hi (e.functor.mapArrow.obj f))
  hp f := by
    have hu : e.functor.map (e.unitIso.inv.app f.right) =
        e.counitIso.hom.app (e.functor.obj f.right) := (e.counit_app_functor f.right).symm
    have hc : e.functor.map (e.inverse.map (data.p.app (e.functor.mapArrow.obj f))) ≫
        e.counitIso.hom.app (e.functor.obj f.right) =
      e.counitIso.hom.app (data.Z.obj (e.functor.mapArrow.obj f)) ≫
        data.p.app (e.functor.mapArrow.obj f) := by
      simpa only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj,
        Arrow.rightFunc_obj, Functor.mapArrow_obj, Arrow.mk_right] using
        e.counitIso.hom.naturality (data.p.app (e.functor.mapArrow.obj f))
    have h : (e.counitIso.app (data.Z.obj (e.functor.mapArrow.obj f))).hom ≫
        data.p.app (e.functor.mapArrow.obj f) =
      e.functor.map (e.inverse.map (data.p.app (e.functor.mapArrow.obj f)) ≫
        e.unitIso.inv.app f.right) ≫ (Iso.refl (e.functor.obj f.right)).hom := by
      simp only [Iso.refl_hom, Iso.app_hom, Functor.map_comp]
      rw [hu]
      have hid := Category.comp_id
        (e.functor.map (e.inverse.map (data.p.app (e.functor.mapArrow.obj f))) ≫
          e.counitIso.hom.app (e.functor.obj f.right))
      simpa only [Functor.id_obj, Functor.comp_obj, Arrow.rightFunc_obj, Functor.mapArrow_obj,
        Arrow.mk_right] using hc.symm.trans hid.symm
    let q : Arrow.mk (e.functor.map (e.inverse.map (data.p.app (e.functor.mapArrow.obj f)) ≫
        e.unitIso.inv.app f.right)) ≅ Arrow.mk (data.p.app (e.functor.mapArrow.obj f)) :=
      Arrow.isoMk (e.counitIso.app (data.Z.obj (e.functor.mapArrow.obj f)))
      (Iso.refl (e.functor.obj f.right)) h
    exact (W₂.arrow_mk_iso_iff q).2 (data.hp (e.functor.mapArrow.obj f))

/-- The whole original intermediate functor is retained through the actual inverse. -/
theorem ofEquivalence_Z (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) :
    (data.ofEquivalence e).Z = e.functor.mapArrow ⋙ data.Z ⋙ e.inverse := rfl

/-- Every intermediate object is the actual inverse of the original mapped-arrow object. -/
theorem ofEquivalence_Z_obj (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) (f : Arrow C) :
    (data.ofEquivalence e).Z.obj f = e.inverse.obj (data.Z.obj (e.functor.mapArrow.obj f)) := rfl

/-- Every complete Arrow map is the actual inverse of the original intermediate map. -/
theorem ofEquivalence_Z_map (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D)
    {f g : Arrow C} (φ : f ⟶ g) :
    (data.ofEquivalence e).Z.map φ = e.inverse.map (data.Z.map (e.functor.mapArrow.map φ)) := rfl

/-- The left natural arrow uses the original unit and original mapped left component. -/
theorem ofEquivalence_i_app (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) (f : Arrow C) :
    (data.ofEquivalence e).i.app f = e.unitIso.hom.app f.left ≫
      e.inverse.map (data.i.app (e.functor.mapArrow.obj f)) := rfl

/-- The right natural arrow uses the original mapped right component and inverse unit. -/
theorem ofEquivalence_p_app (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) (f : Arrow C) :
    (data.ofEquivalence e).p.app f = e.inverse.map (data.p.app (e.functor.mapArrow.obj f)) ≫
      e.unitIso.inv.app f.right := rfl

/-- The two transported original arrows factor exactly the source caller arrow. -/
theorem ofEquivalence_fac_app (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) (f : Arrow C) :
    (data.ofEquivalence e).i.app f ≫ (data.ofEquivalence e).p.app f = f.hom :=
  (data.ofEquivalence e).fac_app

/-- The actual counit compares the whole transported middle functor to the original one. -/
def ofEquivalenceZComparisonIso (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) :
    (data.ofEquivalence e).Z ⋙ e.functor ≅ e.functor.mapArrow ⋙ data.Z :=
  NatIso.ofComponents (fun f => e.counitIso.app (data.Z.obj (e.functor.mapArrow.obj f)))
    (fun φ => by
      change e.functor.map (e.inverse.map (data.Z.map (e.functor.mapArrow.map φ))) ≫
          e.counitIso.hom.app _ = e.counitIso.hom.app _ ≫ data.Z.map (e.functor.mapArrow.map φ)
      simpa only [Functor.comp_map, Functor.id_map] using
        e.counitIso.hom.naturality (data.Z.map (e.functor.mapArrow.map φ)))

/-- The full mapped left arrow recovers the original component through the actual counit. -/
theorem ofEquivalence_mapped_i (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : Arrow C) :
    e.functor.map ((data.ofEquivalence e).i.app f) ≫
      (data.ofEquivalenceZComparisonIso e).hom.app f = data.i.app (e.functor.mapArrow.obj f) := by
  change e.functor.map (e.unitIso.hom.app f.left ≫
      e.inverse.map (data.i.app (e.functor.mapArrow.obj f))) ≫
    e.counitIso.hom.app (data.Z.obj (e.functor.mapArrow.obj f)) = _
  have hc : e.functor.map (e.inverse.map (data.i.app (e.functor.mapArrow.obj f))) ≫
      e.counitIso.hom.app (data.Z.obj (e.functor.mapArrow.obj f)) =
    e.counitIso.hom.app (e.functor.obj f.left) ≫ data.i.app (e.functor.mapArrow.obj f) := by
    simpa only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj,
      Arrow.leftFunc_obj, Functor.mapArrow_obj, Arrow.mk_left] using
      e.counitIso.hom.naturality (data.i.app (e.functor.mapArrow.obj f))
  rw [Functor.map_comp, Category.assoc, hc,
    ← Category.assoc, e.functor_unitIso_comp f.left]
  simpa only [Arrow.leftFunc_obj, Functor.mapArrow_obj, Arrow.mk_left] using
    Category.id_comp (data.i.app (e.functor.mapArrow.obj f))

/-- The full mapped right arrow recovers the original component through the actual counit. -/
theorem ofEquivalence_mapped_p (data : FunctorialFactorizationData W₁ W₂)
    (e : C ≌ D) (f : Arrow C) :
    (data.ofEquivalenceZComparisonIso e).hom.app f ≫ data.p.app (e.functor.mapArrow.obj f) =
      e.functor.map ((data.ofEquivalence e).p.app f) := by
  change e.counitIso.hom.app (data.Z.obj (e.functor.mapArrow.obj f)) ≫ _ =
    e.functor.map (e.inverse.map (data.p.app (e.functor.mapArrow.obj f)) ≫
      e.unitIso.inv.app f.right)
  rw [Functor.map_comp, ← e.counit_app_functor f.right]
  symm
  simpa only [Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.comp_obj,
    Arrow.rightFunc_obj, Functor.mapArrow_obj, Arrow.mk_right] using
    e.counitIso.hom.naturality (data.p.app (e.functor.mapArrow.obj f))

end CategoryTheory.MorphismProperty.FunctorialFactorizationData
