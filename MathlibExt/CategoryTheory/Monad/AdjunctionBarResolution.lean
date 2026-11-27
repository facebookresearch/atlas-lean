/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import MathlibExt.CategoryTheory.Monad.BarResolution
public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedWhiskering

/-!
# Free Bar constructions from an adjunction

For an adjunction `F ⊣ U`, the coefficient object determines a free simplicial Bar with counit
augmentation. Applying `U` identifies this augmented object with the regular monadic Bar, whose
extra degeneracy gives a contraction.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe vC uC vD uD

namespace CategoryTheory.SimplicialObject

variable {C : Type uC} [Category.{vC} C]

/-- Maps from a simplicial object to a constant are determined by their zero component. -/
theorem toConst_ext_zero {X : SimplicialObject C} {M : C}
    {p q : X ⟶ (SimplicialObject.const C).obj M}
    (h : p.app (op (SimplexCategory.mk 0)) = q.app (op (SimplexCategory.mk 0))) : p = q := by
  apply NatTrans.ext
  funext Δ
  let v := (SimplexCategory.const (SimplexCategory.mk 0) (unop Δ) 0).op
  have hp : X.map v ≫ p.app (op (SimplexCategory.mk 0)) = p.app Δ := by
    simpa only [Functor.id_obj, Functor.const_obj_obj, Functor.const_obj_map,
      Category.comp_id] using p.naturality v
  have hq : X.map v ≫ q.app (op (SimplexCategory.mk 0)) = q.app Δ := by
    simpa only [Functor.id_obj, Functor.const_obj_obj, Functor.const_obj_map,
      Category.comp_id] using q.naturality v
  exact hp.symm.trans ((congrArg (fun a => X.map v ≫ a) h).trans hq)

end CategoryTheory.SimplicialObject

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F : C ⥤ D} {U : D ⥤ C}

/-- An adjunction supplies the right module on its free functor. -/
def freeRightModule (adj : F ⊣ U) : Monad.RightModule adj.toMonad D :=
  Monad.RightModule.mk (T := adj.toMonad) F
    { app := fun X => adj.counit.app (F.obj X)
      naturality := fun X Y g => by
        change F.map (U.map (F.map g)) ≫ adj.counit.app (F.obj Y) =
          adj.counit.app (F.obj X) ≫ F.map g
        exact adj.counit.naturality (F.map g) }
    (fun X => adj.left_triangle_components X)
    (fun X => by
      change F.map (U.map (adj.counit.app (F.obj X))) ≫ adj.counit.app (F.obj X) =
        adj.counit.app (F.obj (U.obj (F.obj X))) ≫ adj.counit.app (F.obj X)
      exact adj.counit.naturality (adj.counit.app (F.obj X)))

/-- After the forgetful functor this is the regular monadic right module. -/
def freeRightModuleForgetIso (adj : F ⊣ U) :
    (adj.freeRightModule.postcomp U) ≅ Monad.RightModule.regular adj.toMonad :=
  Monad.Algebra.isoMk (Iso.refl (F ⋙ U))
    (by
      ext X
      change (𝟙 _) ≫ U.map (adj.counit.app (F.obj X)) =
        U.map (adj.counit.app (F.obj X)) ≫ (𝟙 _)
      rw [Category.id_comp, Category.comp_id])

@[simp]
theorem freeRightModuleForgetIso_hom_f (adj : F ⊣ U) :
    adj.freeRightModuleForgetIso.hom.f = 𝟙 _ := rfl

/-- The algebra-valued Bar of the induction right module. -/
def freeBar (adj : F ⊣ U) (M : D) : SimplicialObject D :=
  Monad.algebraBar adj.freeRightModule ((Monad.comparison adj).obj M)

/-- Every Bar level is the free object on the corresponding monad power. -/
@[simp]
theorem freeBar_obj (adj : F ⊣ U) (M : D) (n : ℕ) :
    (adj.freeBar M).obj (op (SimplexCategory.mk n)) =
      F.obj ((Monad.monadPow adj.toMonad n).obj (U.obj M)) := rfl

/-- The counit gives the balanced augmentation from its own naturality law. -/
def freeBarPairing (adj : F ⊣ U) (M : D) :
    Monad.BalancedPairing adj.toMonad adj.freeRightModule
      (Monad.algebraLeftModule ((Monad.comparison adj).obj M)) := by
  let p : Monad.barObj adj.toMonad adj.freeRightModule
      (Monad.algebraLeftModule ((Monad.comparison adj).obj M)) 0 ⟶
      (Functor.const (Discrete PUnit.{1})).obj M :=
    { app := fun _ => adj.counit.app M
      naturality := fun _ _ _ => by
        change F.map (𝟙 (U.obj M)) ≫ adj.counit.app M = adj.counit.app M ≫ (𝟙 M)
        rw [F.map_id]
        exact (Category.id_comp (adj.counit.app M)).trans
          (Category.comp_id (adj.counit.app M)).symm }
  exact Monad.BalancedPairing.mkOfActionEq p (fun _ => by
    change adj.counit.app (F.obj (U.obj M)) ≫ adj.counit.app M =
      F.map (U.map (adj.counit.app M)) ≫ adj.counit.app M
    exact (adj.counit.naturality (adj.counit.app M)).symm)

/-- The augmentation of the free Bar, with counit endpoint. -/
def freeBarAugmented (adj : F ⊣ U) (M : D) : SimplicialObject.Augmented D :=
  (SimplicialObject.Augmented.whiskeringObj _ _ (Monad.resolutionEvalPoint (C := D))).obj
    (adj.freeBarPairing M).toSimplicialAugmented

@[simp]
theorem freeBarAugmented_left (adj : F ⊣ U) (M : D) :
    (adj.freeBarAugmented M).left = adj.freeBar M := rfl

@[simp]
theorem freeBarAugmented_right (adj : F ⊣ U) (M : D) :
    (adj.freeBarAugmented M).right = M := rfl

/-- Degree zero of the augmentation is the counit. -/
@[simp]
theorem freeBarAugmented_hom_zero (adj : F ⊣ U) (M : D) :
    (adj.freeBarAugmented M).hom.app (op (SimplexCategory.mk 0)) = adj.counit.app M := by
  have h := SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk
    (Monad.resolutionEvalPoint (C := D)) (adj.freeBarPairing M).toSimplicialAugmented 0
  have hp : (Monad.resolutionEvalPoint (C := D)).map (adj.freeBarPairing M).pairing =
      adj.counit.app M := rfl
  have h₀ := Monad.BalancedPairing.toSimplicialAugmented_hom_app_mk (adj.freeBarPairing M) 0
  rw [Monad.BalancedPairing.toDataHom_app_zero] at h₀
  have he := congrArg (fun f => (Monad.resolutionEvalPoint (C := D)).map f) h₀
  exact h.trans (he.trans hp)

/-- The target-whiskering comparison identifies the forgotten Bar with the regular Bar. -/
def freeBarForgetIso (adj : F ⊣ U) (M : D) :
    adj.freeBar M ⋙ U ≅ Monad.resolutionBar ((Monad.comparison adj).obj M) := by
  let R := adj.freeRightModule
  let L := Monad.algebraLeftModule ((Monad.comparison adj).obj M)
  change (Monad.twoSidedBar adj.toMonad R L ⋙ Monad.functorPostcompOuter U) ⋙
      (Monad.resolutionEvalPoint (C := C)) ≅
    Monad.twoSidedBar adj.toMonad (Monad.RightModule.regular adj.toMonad) L ⋙
      (Monad.resolutionEvalPoint (C := C))
  exact Functor.isoWhiskerRight
    (Monad.twoSidedBarPostcompWhiskerIso U R L ≪≫
      Monad.twoSidedBarIso adj.freeRightModuleForgetIso (Iso.refl L))
    (Monad.resolutionEvalPoint (C := C))

/-- The comparison has identity components on the Bar terms. -/
@[simp]
theorem freeBarForgetIso_hom_app_mk (adj : F ⊣ U) (M : D) (n : ℕ) :
    (adj.freeBarForgetIso M).hom.app (op (SimplexCategory.mk n)) = 𝟙 _ := by
  let R := adj.freeRightModule
  let L := Monad.algebraLeftModule ((Monad.comparison adj).obj M)
  change (((Monad.twoSidedBarPostcompWhiskerIso U R L).hom.app
      (op (SimplexCategory.mk n))).app (Discrete.mk PUnit.unit)) ≫
    (((Monad.twoSidedBarIso adj.freeRightModuleForgetIso (Iso.refl L)).hom.app
      (op (SimplexCategory.mk n))).app (Discrete.mk PUnit.unit)) = 𝟙 _
  have hw := Monad.twoSidedBarPostcompWhiskerIso_hom_app_app_id U R L n
    (Discrete.mk PUnit.unit)
  have hi := Monad.twoSidedBarIso_hom_app adj.freeRightModuleForgetIso (Iso.refl L)
    (op (SimplexCategory.mk n)) (Discrete.mk PUnit.unit)
  have hs : (((Monad.twoSidedBarIso adj.freeRightModuleForgetIso (Iso.refl L)).hom.app
      (op (SimplexCategory.mk n))).app (Discrete.mk PUnit.unit)) = 𝟙 _ := by
    simp only [Iso.refl_hom, Monad.Algebra.id_f, NatTrans.id_app,
      freeRightModuleForgetIso_hom_f, CategoryTheory.Functor.map_id] at hi
    let W := U.obj (F.obj ((Monad.monadPow adj.toMonad n).obj (U.obj M)))
    have hid : (𝟙 W) ≫ (𝟙 W) = 𝟙 W := Category.id_comp (𝟙 W)
    exact hi.trans hid
  exact (congrArg (fun f => f ≫
    (((Monad.twoSidedBarIso adj.freeRightModuleForgetIso (Iso.refl L)).hom.app
      (op (SimplexCategory.mk n))).app (Discrete.mk PUnit.unit))) hw).trans
    ((Category.id_comp _).trans hs)

/-- The full augmentation is identified through coefficient postcomposition. -/
def freeBarAugmentedForgetIso (adj : F ⊣ U) (M : D) :
    (SimplicialObject.Augmented.whiskeringObj _ _ U).obj (adj.freeBarAugmented M) ≅
      Monad.resolutionAugmented ((Monad.comparison adj).obj M) := by
  refine Comma.isoMk (adj.freeBarForgetIso M) (Iso.refl _) ?_
  apply SimplicialObject.toConst_ext_zero
  change (adj.freeBarForgetIso M).hom.app (op (SimplexCategory.mk 0)) ≫
      (Monad.resolutionAugmented ((Monad.comparison adj).obj M)).hom.app
        (op (SimplexCategory.mk 0)) =
    ((SimplicialObject.Augmented.whiskeringObj _ _ U).obj (adj.freeBarAugmented M)).hom.app
        (op (SimplexCategory.mk 0)) ≫ (𝟙 (U.obj M))
  rw [freeBarForgetIso_hom_app_mk, Monad.resolutionAugmented_hom_zero,
    SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk, freeBarAugmented_hom_zero]
  change (𝟙 (U.obj (F.obj (U.obj M)))) ≫ U.map (adj.counit.app M) =
    U.map (adj.counit.app M) ≫ 𝟙 (U.obj M)
  exact (Category.id_comp (U.map (adj.counit.app M))).trans
    (Category.comp_id (U.map (adj.counit.app M))).symm

/-- The regular extra degeneracy gives the restricted augmented Bar contraction. -/
def freeBarExtra (adj : F ⊣ U) (M : D) :
    SimplicialObject.Augmented.ExtraDegeneracy
      ((SimplicialObject.Augmented.whiskeringObj _ _ U).obj (adj.freeBarAugmented M)) :=
  SimplicialObject.Augmented.ExtraDegeneracy.ofIso (adj.freeBarAugmentedForgetIso M).symm
    (Monad.resolutionExtra ((Monad.comparison adj).obj M))

end CategoryTheory.Adjunction
