/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
module

public import Mathlib.CategoryTheory.Enriched.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-!
# Pointwise tensor and the original under-category mapping ends

The internal Hom for arbitrary ordinary diagrams is the existing enriched
Hom end on each under category. The tensor-Hom adjunction below retains
every original diagram map. In particular, the internal Hom is not formed
by applying the coefficient internal Hom objectwise.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe uJ vJ uV vV

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Enriched.FunctorCategory
open scoped MonoidalClosed

namespace CategoryTheory.Monoidal.PointwiseFunctorClosed

variable {J : Type uJ} [Category.{vJ} J]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  [∀ F G : J ⥤ V, HasEnrichedHom V F G]
  [∀ F G : J ⥤ V, HasFunctorEnrichedHom V F G]

/-- The original under-category ends, with their existing entire diagram action. -/
def internalHom (F : J ⥤ V) : (J ⥤ V) ⥤ (J ⥤ V) := by
  letI := functorEnrichedOrdinaryCategory V (J := J) (C := V)
  exact (eHomFunctor (J ⥤ V) (J ⥤ V)).obj (op F)

/-- The value remains the existing end on the entire original under category. -/
theorem internalHom_obj (F G : J ⥤ V) (j : J) :
    ((internalHom F).obj G).obj j =
      enrichedHom V (Under.forget j ⋙ F) (Under.forget j ⋙ G) := rfl

/-- The original projection indexed by an actual arrow out of j. -/
abbrev projection (F G : J ⥤ V) (j : J) (a : Under j) :
    ((internalHom F).obj G).obj j ⟶ (ihom (F.obj a.right)).obj (G.obj a.right) :=
  enrichedHomπ V (Under.forget j ⋙ F) (Under.forget j ⋙ G) a

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary-to-enriched comparison retains every original component. -/
theorem functorHomEquiv_projection {F G : J ⥤ V} (τ : F ⟶ G) (j : J) (a : Under j) :
    (functorHomEquiv V τ).app j ≫ projection F G j a =
      MonoidalClosed.curry' (τ.app a.right) := by
  rw [functorHomEquiv_apply_app]
  dsimp only [projection, precompEnrichedHom, precompEnrichedHom']
  rw [Category.assoc, end_.lift_π]
  simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app]
  dsimp only [Functor.comp_obj, Under.forget_obj]
  rw [eHomWhiskerRight_id, eHomWhiskerLeft_id]
  simpa only [Category.comp_id, tensorUnit_obj,
    MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv] using homEquiv_apply_π V τ a.right

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition on the existing right-Hom functor is the exact coefficient map. -/
theorem internalHom_map_projection (F : J ⥤ V) {G H : J ⥤ V}
    (τ : G ⟶ H) (j : J) (a : Under j) :
    ((internalHom F).map τ).app j ≫ projection F H j a =
      projection F G j a ≫ (ihom (F.obj a.right)).map (τ.app a.right) := by
  change ((ρ_ (enrichedHom V (Under.forget j ⋙ F) (Under.forget j ⋙ G))).inv ≫
    enrichedHom V (Under.forget j ⋙ F) (Under.forget j ⋙ G) ◁
      (functorHomEquiv V τ).app j ≫
      enrichedComp V (Under.forget j ⋙ F) (Under.forget j ⋙ G)
        (Under.forget j ⋙ H)) ≫ projection F H j a = _
  simp only [Category.assoc]
  rw [enrichedComp_π]
  dsimp only [Functor.op_obj, Functor.comp_obj, Under.forget_obj, unop_op]
  have ht :
      enrichedHom V (Under.forget j ⋙ F) (Under.forget j ⋙ G) ◁
        (functorHomEquiv V τ).app j ≫
        (projection F G j a ⊗ₘ projection G H j a) =
      projection F G j a ⊗ₘ MonoidalClosed.curry' (τ.app a.right) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
      functorHomEquiv_projection]
  rw [← Category.assoc _ _ (eComp V (F.obj a.right) (G.obj a.right) (H.obj a.right)), ht]
  rw [tensorHom_def, Category.assoc, ← rightUnitor_inv_naturality_assoc]
  rw [MonoidalClosed.enrichedCategorySelf_comp]
  rw [MonoidalClosed.whiskerLeft_curry'_comp, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Currying at j keeps each original arrow j-to-k through the end projection. -/
def curryComponent {F G H : J ⥤ V} (τ : F ⊗ G ⟶ H) (j : J) :
    G.obj j ⟶ ((internalHom F).obj H).obj j :=
  end_.lift
    (fun a : Under j =>
      MonoidalClosed.curry ((F.obj a.right ◁ G.map a.hom) ≫ τ.app a.right))
    (by
      intro a b h
      change MonoidalClosed.curry ((F.obj a.right ◁ G.map a.hom) ≫ τ.app a.right) ≫
          eHomWhiskerLeft V (F.obj a.right) (H.map h.right) =
        MonoidalClosed.curry ((F.obj b.right ◁ G.map b.hom) ≫ τ.app b.right) ≫
          eHomWhiskerRight V (F.map h.right) (H.obj b.right)
      rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
        MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight,
        ← MonoidalClosed.curry_natural_right, MonoidalClosed.curry_pre_app]
      apply congrArg MonoidalClosed.curry
      rw [Category.assoc, ← τ.naturality h.right]
      change (F.obj a.right ◁ G.map a.hom) ≫
          (F.map h.right ⊗ₘ G.map h.right) ≫ τ.app b.right = _
      rw [tensorHom_def', Category.assoc, ← whiskerLeft_comp_assoc, ← G.map_comp,
        Under.w h, whisker_exchange_assoc])

/-- The full original currying formula holds at every under-category object. -/
theorem curryComponent_projection {F G H : J ⥤ V}
    (τ : F ⊗ G ⟶ H) (j : J) (a : Under j) :
    curryComponent τ j ≫ projection F H j a =
      MonoidalClosed.curry ((F.obj a.right ◁ G.map a.hom) ≫ τ.app a.right) :=
  end_.lift_π _ _ a

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the under-category end keeps the same target object and complete arrow. -/
theorem internalHom_map_index_projection (F G : J ⥤ V)
    {j k : J} (f : j ⟶ k) (a : Under k) :
    ((internalHom F).obj G).map f ≫ projection F G k a =
      projection F G j ((Under.map f).obj a) := by
  change (functorEnrichedHom V F G).map f ≫
    enrichedHomπ V (Under.forget k ⋙ F) (Under.forget k ⋙ G) a = _
  rw [functorEnrichedHom_map]
  dsimp only [precompEnrichedHom', projection]
  rw [end_.lift_π]
  simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app]
  dsimp only [Functor.comp_obj, Under.forget_obj, Under.map_obj_right]
  rw [eHomWhiskerRight_id, eHomWhiskerLeft_id]
  simp only [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The component end lifts form a natural transformation on all original J arrows. -/
def curry {F G H : J ⥤ V} (τ : F ⊗ G ⟶ H) : G ⟶ (internalHom F).obj H where
  app j := curryComponent τ j
  naturality j k f := by
    apply end_.hom_ext
    intro a
    simp only [Category.assoc]
    rw [curryComponent_projection, internalHom_map_index_projection,
      curryComponent_projection]
    dsimp only [Under.map_obj_right]
    rw [← MonoidalClosed.curry_natural_left]
    change MonoidalClosed.curry ((F.obj a.right ◁ G.map f) ≫
      (F.obj a.right ◁ G.map a.hom) ≫ τ.app a.right) =
      MonoidalClosed.curry ((F.obj a.right ◁ G.map (f ≫ a.hom)) ≫ τ.app a.right)
    simp only [Functor.map_comp, whiskerLeft_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Inverse transposition is evaluation at the original identity under j. -/
def uncurry {F G H : J ⥤ V} (τ : G ⟶ (internalHom F).obj H) : F ⊗ G ⟶ H where
  app j := MonoidalClosed.uncurry (τ.app j ≫ projection F H j (Under.mk (𝟙 j)))
  naturality j k f := by
    let a : Under j := (Under.map f).obj (Under.mk (𝟙 k))
    let h : Under.mk (𝟙 j) ⟶ a := Under.homMk f (by
      change (𝟙 j) ≫ f = f ≫ 𝟙 k
      simp only [Category.id_comp, Category.comp_id])
    have hEnd := congrArg (fun t => τ.app j ≫ t)
      (enrichedHom_condition V (Under.forget j ⋙ F) (Under.forget j ⋙ H) h)
    dsimp only [Functor.comp_obj, Under.forget_obj] at hEnd
    rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
      MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] at hEnd
    change τ.app j ≫ projection F H j (Under.mk (𝟙 j)) ≫ (ihom (F.obj j)).map (H.map f) =
      τ.app j ≫ projection F H j a ≫ (MonoidalClosed.pre (F.map f)).app (H.obj k) at hEnd
    have hNat := congrArg (fun t => t ≫ projection F H k (Under.mk (𝟙 k))) (τ.naturality f)
    simp only [Category.assoc] at hNat
    rw [internalHom_map_index_projection] at hNat
    change G.map f ≫ τ.app k ≫ projection F H k (Under.mk (𝟙 k)) =
      τ.app j ≫ projection F H j a at hNat
    change (F.map f ⊗ₘ G.map f) ≫
      MonoidalClosed.uncurry (τ.app k ≫ projection F H k (Under.mk (𝟙 k))) = _
    rw [tensorHom_def, Category.assoc, ← MonoidalClosed.uncurry_natural_left, hNat]
    rw [← MonoidalClosed.uncurry_pre_app]
    simp only [Category.assoc]
    exact (congrArg MonoidalClosed.uncurry hEnd.symm).trans
      (by
        simpa only [Category.assoc, Under.mk_right] using
          (MonoidalClosed.uncurry_natural_right
            (τ.app j ≫ projection F H j (Under.mk (𝟙 j))) (H.map f)))

set_option backward.isDefEq.respectTransparency false in
/-- Inverse transposition after transposition is the complete original diagram arrow. -/
theorem uncurry_curry {F G H : J ⥤ V} (τ : F ⊗ G ⟶ H) : uncurry (curry τ) = τ := by
  ext j
  change MonoidalClosed.uncurry (curryComponent τ j ≫
    projection F H j (Under.mk (𝟙 j))) = τ.app j
  rw [curryComponent_projection]
  simp only [Under.mk_right, Under.mk_hom, Functor.map_id, whiskerLeft_id,
    Category.id_comp, MonoidalClosed.uncurry_curry]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transposition after evaluation retains every original under-end projection. -/
theorem curry_uncurry {F G H : J ⥤ V} (τ : G ⟶ (internalHom F).obj H) :
    curry (uncurry τ) = τ := by
  ext j
  apply end_.hom_ext
  intro a
  change curryComponent (uncurry τ) j ≫ projection F H j a = τ.app j ≫ projection F H j a
  rw [curryComponent_projection]
  change MonoidalClosed.curry (F.obj a.right ◁ G.map a.hom ≫
    MonoidalClosed.uncurry (τ.app a.right ≫ projection F H a.right (Under.mk (𝟙 a.right)))) = _
  rw [MonoidalClosed.curry_natural_left, MonoidalClosed.curry_uncurry]
  have hNat := congrArg
    (fun t => t ≫ projection F H a.right (Under.mk (𝟙 a.right))) (τ.naturality a.hom)
  simp only [Category.assoc] at hNat
  rw [internalHom_map_index_projection] at hNat
  rw [hNat]
  let b : Under j := (Under.map a.hom).obj (Under.mk (𝟙 a.right))
  let h : a ⟶ b := Under.homMk (𝟙 a.right) (by rfl)
  have hEnd := enrichedHom_condition V (Under.forget j ⋙ F) (Under.forget j ⋙ H) h
  dsimp only [Functor.comp_obj, Under.forget_obj] at hEnd
  change projection F H j a ≫ eHomWhiskerLeft V (F.obj a.right) (H.map (𝟙 a.right)) =
    projection F H j b ≫ eHomWhiskerRight V (F.map (𝟙 a.right)) (H.obj a.right) at hEnd
  simp only [Functor.map_id, eHomWhiskerLeft_id, eHomWhiskerRight_id] at hEnd
  have hab : projection F H j a = projection F H j b := by
    exact (Category.comp_id _).symm.trans (hEnd.trans (Category.comp_id _))
  exact congrArg (fun t => τ.app j ≫ t) hab.symm

/-- The full ordinary tensor-Hom bijection is the original under-end transpose. -/
def homEquiv (F G H : J ⥤ V) : (F ⊗ G ⟶ H) ≃ (G ⟶ (internalHom F).obj H) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

set_option backward.isDefEq.respectTransparency false in
/-- The transpose is natural in every original target transformation. -/
theorem curry_naturality_right {F G H H' : J ⥤ V} (τ : F ⊗ G ⟶ H) (q : H ⟶ H') :
    curry (τ ≫ q) = curry τ ≫ (internalHom F).map q := by
  ext j
  apply end_.hom_ext
  intro a
  simp only [NatTrans.comp_app, Category.assoc]
  rw [internalHom_map_projection]
  change curryComponent (τ ≫ q) j ≫ projection F H' j a =
    curryComponent τ j ≫ projection F H j a ≫ (ihom (F.obj a.right)).map (q.app a.right)
  rw [curryComponent_projection, ← Category.assoc, curryComponent_projection]
  simp only [NatTrans.comp_app, Category.assoc, MonoidalClosed.curry_natural_right,
    Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse transpose is natural in every entire original input arrow. -/
theorem uncurry_naturality_left {F G G' H : J ⥤ V}
    (q : G' ⟶ G) (τ : G ⟶ (internalHom F).obj H) :
    uncurry (q ≫ τ) = (F ◁ q) ≫ uncurry τ := by
  ext j
  change MonoidalClosed.uncurry ((q.app j ≫ τ.app j) ≫
    projection F H j (Under.mk (𝟙 j))) = _
  rw [Category.assoc, MonoidalClosed.uncurry_natural_left]
  rfl

/-- Construct the missing pointwise closed adjunction from those exact ends and maps. -/
def adjunction (F : J ⥤ V) : tensorLeft F ⊣ internalHom F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G H => homEquiv F G H
      homEquiv_naturality_left_symm := uncurry_naturality_left
      homEquiv_naturality_right := curry_naturality_right }

/-- The pointwise tensor is closed using the original under-category end functor. -/
@[instance_reducible]
def monoidalClosed : MonoidalClosed (J ⥤ V) where
  closed F := { rightAdj := internalHom F, adj := adjunction F }

/-- The chosen internal Hom is literally the source under-end right functor. -/
theorem ihom_eq (F : J ⥤ V) :
    letI := monoidalClosed (J := J) (V := V)
    ihom F = internalHom F := rfl

end CategoryTheory.Monoidal.PointwiseFunctorClosed
