/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.Monoidal.Bimod
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Relative tensor products of internal modules

This file constructs the balanced tensor product of modules over a
commutative internal monoid by reusing Mathlib's Bimod tensor and coherence
API. The monoidal construction needs only a braided ambient category; the
braiding and symmetric extension retain the symmetric hypothesis.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe v u

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section Braided

variable [BraidedCategory C]
variable (A : CommMon C)

@[reducible] private def rightSmul (M : Mod C A.X) : M.X ⊗ A.X ⟶ M.X :=
  (β_ M.X A.X).hom ≫ M.mod.smul

private theorem rightSmul_one (M : Mod C A.X) :
    (M.X ◁ η[A.X]) ≫ rightSmul A M = (ρ_ M.X).hom := by
  simp [rightSmul]

private theorem rightSmul_assoc (M : Mod C A.X) :
    (M.X ◁ μ[A.X]) ≫ rightSmul A M =
      (α_ M.X A.X A.X).inv ≫
        (rightSmul A M ▷ A.X) ≫ rightSmul A M := by
  have hcore :
      (α_ A.X A.X M.X).inv ≫ ((β_ A.X A.X).hom ▷ M.X) ≫
          (α_ A.X A.X M.X).hom ≫
          (A.X ◁ ModObj.smul (M := A.X) (X := M.X)) ≫
          ModObj.smul (M := A.X) (X := M.X) =
        (A.X ◁ ModObj.smul (M := A.X) (X := M.X)) ≫
          ModObj.smul (M := A.X) (X := M.X) := by
    calc
      _ = (α_ A.X A.X M.X).inv ≫ ((β_ A.X A.X).hom ▷ M.X) ≫
          (μ[A.X] ▷ M.X) ≫
          ModObj.smul (M := A.X) (X := M.X) := by
            slice_lhs 3 5 => rw [← ModObj.mul_smul_self]
      _ = (α_ A.X A.X M.X).inv ≫
          (((β_ A.X A.X).hom ≫ μ[A.X]) ▷ M.X) ≫
          ModObj.smul (M := A.X) (X := M.X) := by
            simp only [comp_whiskerRight, Category.assoc]
      _ = (α_ A.X A.X M.X).inv ≫ (μ[A.X] ▷ M.X) ≫
          ModObj.smul (M := A.X) (X := M.X) := by
            rw [IsCommMonObj.mul_comm]
      _ = _ := (ModObj.mul_smul_self_flip (M := A.X) M.X).symm
  simp [rightSmul, hcore]

private theorem smul_rightSmul (M : Mod C A.X) :
    (ModObj.smul (M := A.X) (X := M.X) ▷ A.X) ≫ rightSmul A M =
      (α_ A.X M.X A.X).hom ≫ (A.X ◁ rightSmul A M) ≫
        ModObj.smul (M := A.X) (X := M.X) := by
  have hcore :
      (α_ A.X A.X M.X).inv ≫ ((β_ A.X A.X).hom ▷ M.X) ≫
          (α_ A.X A.X M.X).hom ≫
          (A.X ◁ ModObj.smul (M := A.X) (X := M.X)) ≫
          ModObj.smul (M := A.X) (X := M.X) =
        (A.X ◁ ModObj.smul (M := A.X) (X := M.X)) ≫
          ModObj.smul (M := A.X) (X := M.X) := by
    calc
      _ = (α_ A.X A.X M.X).inv ≫ ((β_ A.X A.X).hom ▷ M.X) ≫
          (μ[A.X] ▷ M.X) ≫
          ModObj.smul (M := A.X) (X := M.X) := by
            slice_lhs 3 5 => rw [← ModObj.mul_smul_self]
      _ = (α_ A.X A.X M.X).inv ≫
          (((β_ A.X A.X).hom ≫ μ[A.X]) ▷ M.X) ≫
          ModObj.smul (M := A.X) (X := M.X) := by
            simp only [comp_whiskerRight, Category.assoc]
      _ = (α_ A.X A.X M.X).inv ≫ (μ[A.X] ▷ M.X) ≫
          ModObj.smul (M := A.X) (X := M.X) := by
            rw [IsCommMonObj.mul_comm]
      _ = _ := (ModObj.mul_smul_self_flip (M := A.X) M.X).symm
  simp [rightSmul, hcore]

/-- The right action obtained from the actual left action and ambient braiding. -/
def braidedRightAction (M : Mod C A.X) : M.X ⊗ A.X ⟶ M.X :=
  (β_ M.X A.X).hom ≫ M.mod.smul

/-- The public right action has the original right-unit equation. -/
@[reassoc]
theorem braidedRightAction_one (M : Mod C A.X) :
    (M.X ◁ η[A.X]) ≫ braidedRightAction A M = (ρ_ M.X).hom := by
  exact rightSmul_one A M

/-- The public right action uses the original inverse associator. -/
@[reassoc]
theorem braidedRightAction_assoc (M : Mod C A.X) :
    (M.X ◁ μ[A.X]) ≫ braidedRightAction A M =
      (α_ M.X A.X A.X).inv ≫
        (braidedRightAction A M ▷ A.X) ≫ braidedRightAction A M := by
  exact rightSmul_assoc A M

/-- The actual left action commutes with the public braided right action. -/
@[reassoc]
theorem smul_braidedRightAction (M : Mod C A.X) :
    (M.mod.smul ▷ A.X) ≫ braidedRightAction A M =
      (α_ A.X M.X A.X).hom ≫
        (A.X ◁ braidedRightAction A M) ≫ M.mod.smul := by
  exact smul_rightSmul A M

/-- The bimodule associated to a module over the selected commutative monoid. -/
abbrev associatedBimodule (M : Mod C A.X) :
  Bimod ({ X := A.X } : Mon C) ({ X := A.X } : Mon C) where
  X := M.X
  actLeft := M.mod.smul
  one_actLeft := by
    change (η[A.X] ▷ M.X) ≫ ModObj.smul (M := A.X) (X := M.X) =
      (λ_ M.X).hom
    exact ModObj.one_smul_self A.X M.X
  left_assoc := by
    change (μ[A.X] ▷ M.X) ≫ ModObj.smul (M := A.X) (X := M.X) =
      (α_ A.X A.X M.X).hom ≫
        (A.X ◁ ModObj.smul (M := A.X) (X := M.X)) ≫
          ModObj.smul (M := A.X) (X := M.X)
    exact ModObj.mul_smul_self A.X M.X
  actRight := (β_ M.X A.X).hom ≫ M.mod.smul
  actRight_one := by
    change (M.X ◁ η[A.X]) ≫ braidedRightAction A M = (ρ_ M.X).hom
    exact rightSmul_one A M
  right_assoc := by
    change (M.X ◁ μ[A.X]) ≫ braidedRightAction A M =
      (α_ M.X A.X A.X).inv ≫
        (braidedRightAction A M ▷ A.X) ≫ braidedRightAction A M
    exact rightSmul_assoc A M
  middle_assoc := by
    change (ModObj.smul (M := A.X) (X := M.X) ▷ A.X) ≫
      braidedRightAction A M =
        (α_ A.X M.X A.X).hom ≫ (A.X ◁ braidedRightAction A M) ≫
          ModObj.smul (M := A.X) (X := M.X)
    exact smul_rightSmul A M

/-- The bimodule morphism induced by a morphism of modules. -/
abbrev associatedBimoduleMap {M N : Mod C A.X} (f : M ⟶ N) :
    associatedBimodule A M ⟶ associatedBimodule A N where
  hom := by
    change M.X ⟶ N.X
    exact f.hom
  left_act_hom := by
    change ModObj.smul (M := A.X) (X := M.X) ≫ f.hom =
      (A.X ◁ f.hom) ≫ ModObj.smul (M := A.X) (X := N.X)
    exact IsModHom.smul_hom
  right_act_hom := by
    change braidedRightAction A M ≫ f.hom =
      (f.hom ▷ A.X) ≫ braidedRightAction A N
    simp [braidedRightAction]

/-- The isomorphism identifying the associated regular module with the regular bimodule. -/
abbrev associatedRegularBimoduleIso :
    associatedBimodule A (Mod.regular A.X) ≅
  Bimod.regular ({ X := A.X } : Mon C) :=
  by
    exact Bimod.isoOfIso (Iso.refl A.X) (by
      simp [associatedBimodule, Bimod.regular, Mod.regular]) (by
      simp [associatedBimodule, Bimod.regular, Mod.regular,
        IsCommMonObj.mul_comm])

section Tensor

variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Balanced relative tensor product of internal modules. -/
@[reducible] noncomputable def relativeTensor :
    Mod C A.X ⥤ Mod C A.X ⥤ Mod C A.X := by
  let obj (M N : Mod C A.X) : Mod C A.X :=
    { X := (associatedBimodule A M).tensorBimod (associatedBimodule A N) |>.X
      mod :=
        { smul := ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).actLeft
          one_smul := by
            change (η[A.X] ▷ _) ≫
              ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).actLeft =
                (λ_ _).hom
            exact ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).one_actLeft
          mul_smul := by
            change (μ[A.X] ▷ _) ≫
              ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).actLeft =
                (α_ A.X A.X _).hom ≫
                  (A.X ◁ ((associatedBimodule A M).tensorBimod
                    (associatedBimodule A N)).actLeft) ≫
                    ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).actLeft
            exact ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).left_assoc } }
  let inner (M : Mod C A.X) : Mod C A.X ⥤ Mod C A.X :=
    { obj := obj M
      map := fun {N N'} g ↦
        let h := Bimod.whiskerLeft (associatedBimodule A M) (associatedBimoduleMap A g)
        Mod.Hom.mk' h.hom (by
          change ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).actLeft ≫ h.hom =
            (A.X ◁ h.hom) ≫
              ((associatedBimodule A M).tensorBimod (associatedBimodule A N')).actLeft
          exact h.left_act_hom)
      map_id := fun N ↦ by
        apply Mod.hom_ext
        exact congrArg Bimod.Hom.hom Bimod.whiskerLeft_id_bimod
      map_comp := fun g h ↦ by
        apply Mod.hom_ext
        exact congrArg Bimod.Hom.hom
          (Bimod.whiskerLeft_comp_bimod (associatedBimodule A M)
            (associatedBimoduleMap A g) (associatedBimoduleMap A h)) }
  exact
    { obj := inner
      map := fun {M M'} f ↦
        { app := fun N ↦
            let h := Bimod.whiskerRight (associatedBimoduleMap A f) (associatedBimodule A N)
            Mod.Hom.mk' h.hom (by
              change ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).actLeft ≫
                h.hom = (A.X ◁ h.hom) ≫
                  ((associatedBimodule A M').tensorBimod (associatedBimodule A N)).actLeft
              exact h.left_act_hom)
          naturality := fun {N N'} g ↦ by
            apply Mod.hom_ext
            exact congrArg Bimod.Hom.hom
              (Bimod.whisker_exchange_bimod (associatedBimoduleMap A f)
                (associatedBimoduleMap A g)) }
      map_id := fun M ↦ by
        ext N
        exact congrArg Bimod.Hom.hom Bimod.id_whiskerRight_bimod
      map_comp := fun f g ↦ by
        ext N
        exact congrArg Bimod.Hom.hom
          (Bimod.comp_whiskerRight_bimod (associatedBimoduleMap A f)
            (associatedBimoduleMap A g) (associatedBimodule A N)) }

/-- The relative tensor unit is the regular module. -/
def relativeTensorUnit : Mod C A.X := Mod.regular A.X

/-- Projection to the balanced relative tensor product. -/
@[reducible] noncomputable def relativeTensorπ (M N : Mod C A.X) :
    M.X ⊗ N.X ⟶ ((relativeTensor A).obj M).obj N |>.X := by
  change M.X ⊗ N.X ⟶
    ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).X
  exact coequalizer.π
    ((associatedBimodule A M).actRight ▷ (associatedBimodule A N).X)
    ((α_ (associatedBimodule A M).X A.X (associatedBimodule A N).X).hom ≫
      ((associatedBimodule A M).X ◁ (associatedBimodule A N).actLeft))

/-- The relative tensor projection is balanced. -/
theorem relativeTensorπ_balance (M N : Mod C A.X) :
    (braidedRightAction A M ▷ N.X) ≫ relativeTensorπ A M N =
      (α_ M.X A.X N.X).hom ≫
        (M.X ◁ ModObj.smul (M := A.X) (X := N.X)) ≫
          relativeTensorπ A M N := by
  simpa [relativeTensorπ, associatedBimodule, braidedRightAction, Bimod.tensorBimod,
    Bimod.TensorBimod.X, Category.assoc] using
    (coequalizer.condition
      ((associatedBimodule A M).actRight ▷ (associatedBimodule A N).X)
      ((α_ (associatedBimodule A M).X A.X (associatedBimodule A N).X).hom ≫
        ((associatedBimodule A M).X ◁ (associatedBimodule A N).actLeft)))

/-- The first actual arrow in the balancing coequalizer. -/
def relativeTensorFirstMap (M N : Mod C A.X) :
    (M.X ⊗ A.X) ⊗ N.X ⟶ M.X ⊗ N.X :=
  ((β_ M.X A.X).hom ≫ M.mod.smul) ▷ N.X

/-- The second actual arrow in the balancing coequalizer. -/
def relativeTensorSecondMap (M N : Mod C A.X) :
    (M.X ⊗ A.X) ⊗ N.X ⟶ M.X ⊗ N.X :=
  (α_ M.X A.X N.X).hom ≫ (M.X ◁ N.mod.smul)

/-- The complete carrier is the coequalizer of the public balancing arrows. -/
theorem relativeTensor_carrier (M N : Mod C A.X) :
    (((relativeTensor A).obj M).obj N).X =
      coequalizer (relativeTensorFirstMap A M N) (relativeTensorSecondMap A M N) := rfl

/-- The public projection is the actual selected coequalizer projection. -/
theorem relativeTensorπ_eq_coequalizer_π (M N : Mod C A.X) :
    relativeTensorπ A M N =
      coequalizer.π (relativeTensorFirstMap A M N) (relativeTensorSecondMap A M N) := rfl

/-- Balance stated entirely with public arrows and the original action. -/
@[reassoc]
theorem relativeTensorπ_balance_rightAction (M N : Mod C A.X) :
    (braidedRightAction A M ▷ N.X) ≫ relativeTensorπ A M N =
      (α_ M.X A.X N.X).hom ≫ (M.X ◁ N.mod.smul) ≫
        relativeTensorπ A M N := by
  exact relativeTensorπ_balance A M N

/-- The actual cofork presenting the complete relative-tensor carrier. -/
def relativeTensorCofork (M N : Mod C A.X) :
    Cofork (relativeTensorFirstMap A M N) (relativeTensorSecondMap A M N) :=
  Cofork.ofπ (relativeTensorπ A M N)
    (by simpa only [relativeTensorFirstMap, relativeTensorSecondMap, braidedRightAction,
        Category.assoc] using relativeTensorπ_balance_rightAction A M N)

/-- The public cofork is colimiting for the actual balancing arrows. -/
noncomputable def relativeTensorCoforkIsColimit (M N : Mod C A.X) :
    IsColimit (relativeTensorCofork A M N) := by
  change IsColimit (Cofork.ofπ
    (coequalizer.π (relativeTensorFirstMap A M N) (relativeTensorSecondMap A M N)) _)
  exact coequalizerIsCoequalizer _ _

/-- The complete relative-tensor projection is an epimorphism. -/
theorem relativeTensorπ_epi (M N : Mod C A.X) : Epi (relativeTensorπ A M N) := by
  change Epi (coequalizer.π (relativeTensorFirstMap A M N) (relativeTensorSecondMap A M N))
  infer_instance

/-- Right tensoring preserves epimorphy of this actual coequalizer projection. -/
theorem relativeTensorπ_whiskerRight_epi (M N : Mod C A.X) (Z : C) :
    Epi (relativeTensorπ A M N ▷ Z) := by
  change Epi ((tensorRight Z).map
    (coequalizer.π (relativeTensorFirstMap A M N) (relativeTensorSecondMap A M N)))
  infer_instance

/-- Left tensoring preserves epimorphy of this actual coequalizer projection. -/
theorem relativeTensorπ_whiskerLeft_epi (M N : Mod C A.X) (Z : C) :
    Epi (Z ◁ relativeTensorπ A M N) := by
  change Epi ((tensorLeft Z).map
    (coequalizer.π (relativeTensorFirstMap A M N) (relativeTensorSecondMap A M N)))
  infer_instance

/-- Two actual right tensor functors preserve this coequalizer projection. -/
theorem relativeTensorπ_whiskerRight_whiskerRight_epi
    (M N : Mod C A.X) (Z W : C) :
    Epi ((relativeTensorπ A M N ▷ Z) ▷ W) := by
  change Epi ((tensorRight Z ⋙ tensorRight W).map
    (coequalizer.π (relativeTensorFirstMap A M N) (relativeTensorSecondMap A M N)))
  infer_instance

/-- The left action on the actual quotient is characterized after projection. -/
@[reassoc]
theorem relativeTensorπ_smul (M N : Mod C A.X) :
    (A.X ◁ relativeTensorπ A M N) ≫
        (((relativeTensor A).obj M).obj N).mod.smul =
      (α_ A.X M.X N.X).inv ≫ (M.mod.smul ▷ N.X) ≫
        relativeTensorπ A M N := by
  exact Bimod.TensorBimod.whiskerLeft_π_actLeft (associatedBimodule A M) (associatedBimodule A N)

/-- Descend a balanced, left-linear map through the relative tensor. -/
noncomputable def relativeTensorDesc (M N P : Mod C A.X)
    (f : M.X ⊗ N.X ⟶ P.X)
    (hbal : (braidedRightAction A M ▷ N.X) ≫ f =
      (α_ M.X A.X N.X).hom ≫
        (M.X ◁ ModObj.smul (M := A.X) (X := N.X)) ≫ f)
    (hlin : (α_ A.X M.X N.X).inv ≫
        (ModObj.smul (M := A.X) (X := M.X) ▷ N.X) ≫ f =
      (A.X ◁ f) ≫ ModObj.smul (M := A.X) (X := P.X)) :
    ((relativeTensor A).obj M).obj N ⟶ P := by
  let fB : (associatedBimodule A M).X ⊗ (associatedBimodule A N).X ⟶ P.X := by
    change M.X ⊗ N.X ⟶ P.X
    exact f
  let hbal' :
      (associatedBimodule A M).actRight ▷ (associatedBimodule A N).X ≫ fB =
        ((α_ (associatedBimodule A M).X A.X (associatedBimodule A N).X).hom ≫
          ((associatedBimodule A M).X ◁ (associatedBimodule A N).actLeft)) ≫ fB := by
    change (braidedRightAction A M ▷ N.X) ≫ f =
      ((α_ M.X A.X N.X).hom ≫
        (M.X ◁ ModObj.smul (M := A.X) (X := N.X))) ≫ f
    simpa only [Category.assoc] using hbal
  let R : Mon C := { X := A.X }
  let Q := (associatedBimodule A M).tensorBimod (associatedBimodule A N)
  let πB : (associatedBimodule A M).X ⊗ (associatedBimodule A N).X ⟶ Q.X := by
    change (associatedBimodule A M).X ⊗ (associatedBimodule A N).X ⟶ coequalizer
      ((associatedBimodule A M).actRight ▷ (associatedBimodule A N).X)
      ((α_ (associatedBimodule A M).X A.X (associatedBimodule A N).X).hom ≫
        ((associatedBimodule A M).X ◁ (associatedBimodule A N).actLeft))
    exact coequalizer.π _ _
  let d : Q.X ⟶ P.X := by
    change coequalizer
      ((associatedBimodule A M).actRight ▷ (associatedBimodule A N).X)
      ((α_ (associatedBimodule A M).X A.X (associatedBimodule A N).X).hom ≫
        ((associatedBimodule A M).X ◁ (associatedBimodule A N).actLeft)) ⟶ P.X
    exact coequalizer.desc fB hbal'
  refine Mod.Hom.mk' (by
    change Q.X ⟶ P.X
    exact d) ?_
  let _ : Epi (R.X ◁ πB) := by
    change Epi ((tensorLeft R.X).map (coequalizer.π
      ((associatedBimodule A M).actRight ▷ (associatedBimodule A N).X)
      ((α_ (associatedBimodule A M).X A.X (associatedBimodule A N).X).hom ≫
        ((associatedBimodule A M).X ◁ (associatedBimodule A N).actLeft))))
    infer_instance
  · change Q.actLeft ≫ d = (R.X ◁ d) ≫
      ModObj.smul (M := A.X) (X := P.X)
    refine (cancel_epi (R.X ◁ πB)).1 ?_
    have hact : (R.X ◁ πB) ≫ Q.actLeft =
        (α_ R.X (associatedBimodule A M).X (associatedBimodule A N).X).inv ≫
          ((associatedBimodule A M).actLeft ▷ (associatedBimodule A N).X) ≫ πB := by
      dsimp only [R, Q, πB]
      exact Bimod.TensorBimod.whiskerLeft_π_actLeft
        (associatedBimodule A M) (associatedBimodule A N)
    change (R.X ◁ πB) ≫ Q.actLeft ≫ d =
      (R.X ◁ πB) ≫ (R.X ◁ d) ≫
          ModObj.smul (M := A.X) (X := P.X)
    rw [← Category.assoc, hact, Category.assoc]
    have hπd : πB ≫ d = f := by
      dsimp [πB, d, Q, Bimod.tensorBimod, Bimod.TensorBimod.X, fB]
      rw [coequalizer.π_desc]
    slice_lhs 3 5 => rw [hπd]
    rw [← whiskerLeft_comp_assoc, hπd]
    simpa [R] using hlin

/-- The descended map agrees with its input after the projection. -/
theorem relativeTensorDesc_π (M N P : Mod C A.X)
    (f : M.X ⊗ N.X ⟶ P.X)
    (hbal : (braidedRightAction A M ▷ N.X) ≫ f =
      (α_ M.X A.X N.X).hom ≫
        (M.X ◁ ModObj.smul (M := A.X) (X := N.X)) ≫ f)
    (hlin : (α_ A.X M.X N.X).inv ≫
        (ModObj.smul (M := A.X) (X := M.X) ▷ N.X) ≫ f =
      (A.X ◁ f) ≫ ModObj.smul (M := A.X) (X := P.X)) :
    relativeTensorπ A M N ≫
      (relativeTensorDesc A M N P f hbal hlin).hom = f :=
  by
    let fB : (associatedBimodule A M).X ⊗ (associatedBimodule A N).X ⟶ P.X := by
      change M.X ⊗ N.X ⟶ P.X
      exact f
    let hbal' :
        (associatedBimodule A M).actRight ▷ (associatedBimodule A N).X ≫ fB =
          ((α_ (associatedBimodule A M).X A.X (associatedBimodule A N).X).hom ≫
            ((associatedBimodule A M).X ◁ (associatedBimodule A N).actLeft)) ≫ fB := by
      change (braidedRightAction A M ▷ N.X) ≫ f =
        ((α_ M.X A.X N.X).hom ≫
          (M.X ◁ ModObj.smul (M := A.X) (X := N.X))) ≫ f
      simpa only [Category.assoc] using hbal
    exact coequalizer.π_desc fB hbal'

/-- Maps out of a relative tensor are determined after the projection. -/
theorem relativeTensor_hom_ext (M N P : Mod C A.X)
    (f g : ((relativeTensor A).obj M).obj N ⟶ P)
    (h : relativeTensorπ A M N ≫ f.hom =
      relativeTensorπ A M N ≫ g.hom) : f = g := by
  apply Mod.hom_ext
  apply coequalizer.hom_ext
  exact h

/-- The relative-tensor map induced by a morphism in the right factor. -/
private abbrev relativeTensorWhiskerLeft (M : Mod C A.X)
    {N N' : Mod C A.X} (g : N ⟶ N') :
    ((relativeTensor A).obj M).obj N ⟶
      ((relativeTensor A).obj M).obj N' :=
  ((relativeTensor A).obj M).map g

/-- The relative-tensor map induced by a morphism in the left factor. -/
private abbrev relativeTensorWhiskerRight {M M' : Mod C A.X}
    (f : M ⟶ M') (N : Mod C A.X) :
    ((relativeTensor A).obj M).obj N ⟶
      ((relativeTensor A).obj M').obj N :=
  ((relativeTensor A).map f).app N

local notation "mapSecondInput" =>
  (fun (A : CommMon C) (M : Mod C A.X) {N N' : Mod C A.X} (g : N ⟶ N') =>
    Functor.map (Functor.obj (relativeTensor A) M) g)
local notation "mapFirstInput" =>
  (fun (A : CommMon C) {M M' : Mod C A.X} (f : M ⟶ M') (N : Mod C A.X) =>
    NatTrans.app (Functor.map (relativeTensor A) f) N)

/-- Map induced by a pair of module morphisms. -/
def relativeTensorMap {M M' N N' : Mod C A.X}
    (f : M ⟶ M') (g : N ⟶ N') :
    ((relativeTensor A).obj M).obj N ⟶
      ((relativeTensor A).obj M').obj N' :=
  mapFirstInput A f N ≫
    mapSecondInput A M' g

private theorem relativeTensorWhiskerLeft_π (M : Mod C A.X)
    {N N' : Mod C A.X} (g : N ⟶ N') :
    relativeTensorπ A M N ≫ (mapSecondInput A M g).hom =
      (M.X ◁ g.hom) ≫ relativeTensorπ A M N' := by
  change (coequalizer.π
      ((associatedBimodule A M).actRight ▷ (associatedBimodule A N).X)
      ((α_ (associatedBimodule A M).X A.X (associatedBimodule A N).X).hom ≫
        ((associatedBimodule A M).X ◁ (associatedBimodule A N).actLeft))) ≫
      (Bimod.whiskerLeft (associatedBimodule A M) (associatedBimoduleMap A g)).hom =
    ((associatedBimodule A M).X ◁ (associatedBimoduleMap A g).hom) ≫
      coequalizer.π
        ((associatedBimodule A M).actRight ▷ (associatedBimodule A N').X)
        ((α_ (associatedBimodule A M).X A.X (associatedBimodule A N').X).hom ≫
          ((associatedBimodule A M).X ◁ (associatedBimodule A N').actLeft))
  dsimp [Bimod.whiskerLeft]
  erw [Limits.ι_colimMap]
  rw [parallelPairHom_app_one]

private theorem relativeTensorWhiskerRight_π {M M' : Mod C A.X}
    (f : M ⟶ M') (N : Mod C A.X) :
    relativeTensorπ A M N ≫ (mapFirstInput A f N).hom =
      (f.hom ▷ N.X) ≫ relativeTensorπ A M' N := by
  change (coequalizer.π
      ((associatedBimodule A M).actRight ▷ (associatedBimodule A N).X)
      ((α_ (associatedBimodule A M).X A.X (associatedBimodule A N).X).hom ≫
        ((associatedBimodule A M).X ◁ (associatedBimodule A N).actLeft))) ≫
      (Bimod.whiskerRight (associatedBimoduleMap A f) (associatedBimodule A N)).hom =
    ((associatedBimoduleMap A f).hom ▷ (associatedBimodule A N).X) ≫
      coequalizer.π
        ((associatedBimodule A M').actRight ▷ (associatedBimodule A N).X)
        ((α_ (associatedBimodule A M').X A.X (associatedBimodule A N).X).hom ≫
          ((associatedBimodule A M').X ◁ (associatedBimodule A N).actLeft))
  dsimp [Bimod.whiskerRight]
  erw [Limits.ι_colimMap]
  rw [parallelPairHom_app_one]

/-- The map induced on relative tensors is characterized by its composite
with the balanced-tensor projection. -/
theorem relativeTensorMap_π {M M' N N' : Mod C A.X}
    (f : M ⟶ M') (g : N ⟶ N') :
    relativeTensorπ A M N ≫ (relativeTensorMap A f g).hom =
      (f.hom ⊗ₘ g.hom) ≫ relativeTensorπ A M' N' := by
  unfold relativeTensorMap
  simp only [Mod.comp_hom']
  rw [← Category.assoc, relativeTensorWhiskerRight_π, Category.assoc,
    relativeTensorWhiskerLeft_π]
  rw [tensorHom_def]
  simp only [Category.assoc]

/-- The canonical bimodule isomorphism for the relative tensor of two modules. -/
noncomputable abbrev relativeTensorBimoduleIso (M N : Mod C A.X) :
    associatedBimodule A (((relativeTensor A).obj M).obj N) ≅
      (associatedBimodule A M).tensorBimod (associatedBimodule A N) :=
  Bimod.isoOfIso (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.comp_id, whiskerLeft_id,
    Category.id_comp]
    change ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).actLeft =
      ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).actLeft
    rfl) (by
    let R : Mon C := { X := A.X }
    let P : Bimod R R := associatedBimodule A M
    let Q : Bimod R R := associatedBimodule A N
    let T := P.tensorBimod Q
    let πB : P.X ⊗ Q.X ⟶ T.X := coequalizer.π
      (P.actRight ▷ Q.X)
      ((α_ P.X R.X Q.X).hom ≫ (P.X ◁ Q.actLeft))
    simp only [Iso.refl_hom, Category.comp_id, id_whiskerRight,
      Category.id_comp]
    change (β_ T.X R.X).hom ≫ T.actLeft = T.actRight
    let _ : Epi (πB ▷ R.X) := by
      change Epi ((tensorRight R.X).map (coequalizer.π
        (P.actRight ▷ Q.X)
        ((α_ P.X R.X Q.X).hom ≫ (P.X ◁ Q.actLeft))))
      infer_instance
    have hleft : (R.X ◁ πB) ≫ T.actLeft =
        (α_ R.X P.X Q.X).inv ≫ (P.actLeft ▷ Q.X) ≫ πB := by
      dsimp only [T, πB]
      exact Bimod.TensorBimod.whiskerLeft_π_actLeft P Q
    have hright : (πB ▷ R.X) ≫ T.actRight =
        (α_ P.X Q.X R.X).hom ≫ (P.X ◁ Q.actRight) ≫ πB := by
      dsimp only [T, πB]
      exact Bimod.TensorBimod.π_tensor_id_actRight P Q
    have hcondition : (P.actRight ▷ Q.X) ≫ πB =
        (α_ P.X R.X Q.X).hom ≫ (P.X ◁ Q.actLeft) ≫ πB := by
      dsimp [πB, T, Bimod.tensorBimod, Bimod.TensorBimod.X]
      simpa only [Category.assoc] using
        (coequalizer.condition
          (P.actRight ▷ Q.X)
          ((α_ P.X R.X Q.X).hom ≫ (P.X ◁ Q.actLeft)))
    refine (cancel_epi (πB ▷ R.X)).1 ?_
    rw [BraidedCategory.braiding_naturality_left_assoc]
    rw [hleft, hright]
    have hP : P.actRight =
        (β_ P.X R.X).hom ≫ P.actLeft := by
      dsimp only [P, R]
    have hQ : Q.actRight =
        (β_ Q.X R.X).hom ≫ Q.actLeft := by
      dsimp only [Q, R]
    rw [BraidedCategory.braiding_tensor_left_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    slice_lhs 4 5 =>
      rw [← comp_whiskerRight, ← hP]
    slice_lhs 4 5 =>
      rw [hcondition]
    rw [hQ, whiskerLeft_comp]
    simp)

/-- The actual quotient right action is induced from the second factor.
Its statement exposes no private bimodule or action constructor. -/
@[reassoc]
theorem relativeTensorπ_rightAction (M N : Mod C A.X) :
    (relativeTensorπ A M N ▷ A.X) ≫
        braidedRightAction A (((relativeTensor A).obj M).obj N) =
      (α_ M.X N.X A.X).hom ≫ (M.X ◁ braidedRightAction A N) ≫
        relativeTensorπ A M N := by
  let T := ((relativeTensor A).obj M).obj N
  have hact : braidedRightAction A T =
      ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).actRight := by
    have h := (relativeTensorBimoduleIso A M N).hom.right_act_hom
    change braidedRightAction A T ≫ 𝟙 _ =
      (𝟙 _ ▷ A.X) ≫ ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).actRight at h
    simpa only [Category.comp_id, id_whiskerRight, Category.id_comp] using h
  rw [hact]
  exact Bimod.TensorBimod.π_tensor_id_actRight (associatedBimodule A M) (associatedBimodule A N)

/-- Associator for the balanced relative tensor product. -/
noncomputable def relativeTensorAssociator (M N P : Mod C A.X) :
    ((relativeTensor A).obj (((relativeTensor A).obj M).obj N)).obj P ≅
      ((relativeTensor A).obj M).obj (((relativeTensor A).obj N).obj P) := by
  let MN := ((relativeTensor A).obj M).obj N
  let NP := ((relativeTensor A).obj N).obj P
  let eMN := relativeTensorBimoduleIso A M N
  let eNP := relativeTensorBimoduleIso A N P
  let eLeft :
      (associatedBimodule A MN).tensorBimod (associatedBimodule A P) ≅
        ((associatedBimodule A M).tensorBimod (associatedBimodule A N)).tensorBimod
          (associatedBimodule A P) :=
    { hom := Bimod.whiskerRight eMN.hom (associatedBimodule A P)
      inv := Bimod.whiskerRight eMN.inv (associatedBimodule A P)
      hom_inv_id := by
        rw [← Bimod.comp_whiskerRight_bimod, eMN.hom_inv_id,
          Bimod.id_whiskerRight_bimod]
      inv_hom_id := by
        rw [← Bimod.comp_whiskerRight_bimod, eMN.inv_hom_id,
          Bimod.id_whiskerRight_bimod] }
  let eRight :
      (associatedBimodule A M).tensorBimod
          ((associatedBimodule A N).tensorBimod (associatedBimodule A P)) ≅
        (associatedBimodule A M).tensorBimod (associatedBimodule A NP) :=
    { hom := Bimod.whiskerLeft (associatedBimodule A M) eNP.inv
      inv := Bimod.whiskerLeft (associatedBimodule A M) eNP.hom
      hom_inv_id := by
        rw [← Bimod.whiskerLeft_comp_bimod, eNP.inv_hom_id,
          Bimod.whiskerLeft_id_bimod]
      inv_hom_id := by
        rw [← Bimod.whiskerLeft_comp_bimod, eNP.hom_inv_id,
          Bimod.whiskerLeft_id_bimod] }
  let e := eLeft ≪≫
    Bimod.associatorBimod (associatedBimodule A M) (associatedBimodule A N)
      (associatedBimodule A P) ≪≫
      eRight
  refine
    { hom := Mod.Hom.mk' e.hom.hom ?_
      inv := Mod.Hom.mk' e.inv.hom ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · change ((associatedBimodule A MN).tensorBimod (associatedBimodule A P)).actLeft ≫
        e.hom.hom =
      (A.X ◁ e.hom.hom) ≫
        ((associatedBimodule A M).tensorBimod (associatedBimodule A NP)).actLeft
    exact e.hom.left_act_hom
  · change ((associatedBimodule A M).tensorBimod (associatedBimodule A NP)).actLeft ≫
        e.inv.hom =
      (A.X ◁ e.inv.hom) ≫
        ((associatedBimodule A MN).tensorBimod (associatedBimodule A P)).actLeft
    exact e.inv.left_act_hom
  · apply Mod.hom_ext
    change (e.hom ≫ e.inv).hom =
      (𝟙 ((associatedBimodule A MN).tensorBimod (associatedBimodule A P)) :
        (associatedBimodule A MN).tensorBimod (associatedBimodule A P) ⟶ _).hom
    exact congrArg Bimod.Hom.hom e.hom_inv_id
  · apply Mod.hom_ext
    change (e.inv ≫ e.hom).hom =
      (𝟙 ((associatedBimodule A M).tensorBimod (associatedBimodule A NP)) :
        (associatedBimodule A M).tensorBimod (associatedBimodule A NP) ⟶ _).hom
    exact congrArg Bimod.Hom.hom e.inv_hom_id

/-- The relative-tensor associator is characterized by the two iterated
balanced-tensor projections. -/
theorem relativeTensorAssociator_hom_π (M N P : Mod C A.X) :
    (relativeTensorπ A M N ▷ P.X) ≫
        relativeTensorπ A (((relativeTensor A).obj M).obj N) P ≫
          (relativeTensorAssociator A M N P).hom.hom =
      (α_ M.X N.X P.X).hom ≫
        (M.X ◁ relativeTensorπ A N P) ≫
          relativeTensorπ A M (((relativeTensor A).obj N).obj P) := by
  let R : Mon C := { X := A.X }
  let BM : Bimod R R := associatedBimodule A M
  let BN : Bimod R R := associatedBimodule A N
  let BP : Bimod R R := associatedBimodule A P
  let MN := ((relativeTensor A).obj M).obj N
  let NP := ((relativeTensor A).obj N).obj P
  let cMN := relativeTensorBimoduleIso A M N
  let cNP := relativeTensorBimoduleIso A N P
  let bπ (X Y : Bimod R R) : X.X ⊗ Y.X ⟶ (X.tensorBimod Y).X :=
    coequalizer.π (X.actRight ▷ Y.X)
      ((α_ X.X R.X Y.X).hom ≫ (X.X ◁ Y.actLeft))
  have hcMN : relativeTensorπ A M N ≫ cMN.hom.hom = bπ BM BN := by
    change bπ BM BN ≫ 𝟙 (BM.tensorBimod BN).X = bπ BM BN
    rw [Category.comp_id]
  have hwr :
      bπ (associatedBimodule A MN) BP ≫
          (Bimod.whiskerRight cMN.hom BP).hom =
        (cMN.hom.hom ▷ BP.X) ≫ bπ (BM.tensorBimod BN) BP := by
    dsimp only [bπ]
    dsimp [Bimod.whiskerRight]
    erw [Limits.ι_colimMap]
    rw [parallelPairHom_app_one]
  have hwl :
      bπ BM (BN.tensorBimod BP) ≫
          (Bimod.whiskerLeft BM cNP.inv).hom =
        (BM.X ◁ cNP.inv.hom) ≫ bπ BM (associatedBimodule A NP) := by
    dsimp only [bπ]
    dsimp [Bimod.whiskerLeft]
    erw [Limits.ι_colimMap]
    rw [parallelPairHom_app_one]
    rfl
  have ha :
      (bπ BM BN ▷ BP.X) ≫ bπ (BM.tensorBimod BN) BP ≫
          (Bimod.associatorBimod BM BN BP).hom.hom =
        (α_ BM.X BN.X BP.X).hom ≫ (BM.X ◁ bπ BN BP) ≫
          bπ BM (BN.tensorBimod BP) := by
    dsimp only [bπ]
    dsimp [Bimod.associatorBimod, Bimod.isoOfIso,
      Bimod.AssociatorBimod.hom]
    erw [coequalizer.π_desc]
    dsimp [Bimod.AssociatorBimod.homAux]
    erw [π_tensor_id_preserves_coequalizer_inv_desc]
  change (relativeTensorπ A M N ▷ BP.X) ≫
      relativeTensorπ A MN P ≫
        ((Bimod.whiskerRight cMN.hom BP).hom ≫
          (Bimod.associatorBimod BM BN BP).hom.hom ≫
            (Bimod.whiskerLeft BM cNP.inv).hom) = _
  slice_lhs 2 3 => erw [hwr]
  slice_lhs 1 2 => rw [← comp_whiskerRight, hcMN]
  slice_lhs 1 3 => rw [ha]
  slice_lhs 3 4 => rw [hwl]
  dsimp only [cNP]
  rw [show (relativeTensorBimoduleIso A N P).inv.hom = 𝟙 _ from rfl]
  rw [whiskerLeft_id, Category.id_comp]
  dsimp only [BM, BN, BP, bπ, NP, R, relativeTensorπ]
  unfold associatedBimodule
  rfl

/-- The left unit isomorphism for the relative tensor of modules. -/
noncomputable abbrev relativeTensorLeftUnitIso (M : Mod C A.X) :
    ((relativeTensor A).obj (relativeTensorUnit A)).obj M ≅ M := by
  unfold relativeTensorUnit
  let eReg := associatedRegularBimoduleIso A
  let eWhisker :
      (associatedBimodule A (Mod.regular A.X)).tensorBimod (associatedBimodule A M) ≅
        (Bimod.regular ({ X := A.X } : Mon C)).tensorBimod
          (associatedBimodule A M) :=
    { hom := Bimod.whiskerRight eReg.hom (associatedBimodule A M)
      inv := Bimod.whiskerRight eReg.inv (associatedBimodule A M)
      hom_inv_id := by
        erw [← Bimod.comp_whiskerRight_bimod, eReg.hom_inv_id,
          Bimod.id_whiskerRight_bimod]
      inv_hom_id := by
        erw [← Bimod.comp_whiskerRight_bimod, eReg.inv_hom_id,
          Bimod.id_whiskerRight_bimod] }
  let e := eWhisker ≪≫ Bimod.leftUnitorBimod (associatedBimodule A M)
  refine
    { hom := Mod.Hom.mk' e.hom.hom ?_
      inv := Mod.Hom.mk' e.inv.hom ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · change ((associatedBimodule A (Mod.regular A.X)).tensorBimod
        (associatedBimodule A M)).actLeft ≫
        e.hom.hom = (A.X ◁ e.hom.hom) ≫ (associatedBimodule A M).actLeft
    exact e.hom.left_act_hom
  · change (associatedBimodule A M).actLeft ≫ e.inv.hom =
      (A.X ◁ e.inv.hom) ≫
        ((associatedBimodule A (Mod.regular A.X)).tensorBimod
          (associatedBimodule A M)).actLeft
    exact e.inv.left_act_hom
  · apply Mod.hom_ext
    change (e.hom ≫ e.inv).hom =
      (𝟙 ((associatedBimodule A (Mod.regular A.X)).tensorBimod (associatedBimodule A M)) :
        (associatedBimodule A (Mod.regular A.X)).tensorBimod (associatedBimodule A M) ⟶ _).hom
    exact congrArg Bimod.Hom.hom e.hom_inv_id
  · apply Mod.hom_ext
    change (e.inv ≫ e.hom).hom =
      (𝟙 (associatedBimodule A M) : associatedBimodule A M ⟶ _).hom
    exact congrArg Bimod.Hom.hom e.inv_hom_id

/-- The right unit isomorphism for the relative tensor of modules. -/
noncomputable abbrev relativeTensorRightUnitIso (M : Mod C A.X) :
    ((relativeTensor A).obj M).obj (relativeTensorUnit A) ≅ M := by
  unfold relativeTensorUnit
  let eReg := associatedRegularBimoduleIso A
  let eWhisker :
      (associatedBimodule A M).tensorBimod (associatedBimodule A (Mod.regular A.X)) ≅
        (associatedBimodule A M).tensorBimod
          (Bimod.regular ({ X := A.X } : Mon C)) :=
    { hom := Bimod.whiskerLeft (associatedBimodule A M) eReg.hom
      inv := Bimod.whiskerLeft (associatedBimodule A M) eReg.inv
      hom_inv_id := by
        erw [← Bimod.whiskerLeft_comp_bimod, eReg.hom_inv_id,
          Bimod.whiskerLeft_id_bimod]
      inv_hom_id := by
        erw [← Bimod.whiskerLeft_comp_bimod, eReg.inv_hom_id,
          Bimod.whiskerLeft_id_bimod]
        }
  let e := eWhisker ≪≫ Bimod.rightUnitorBimod (associatedBimodule A M)
  refine
    { hom := Mod.Hom.mk' e.hom.hom ?_
      inv := Mod.Hom.mk' e.inv.hom ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · change ((associatedBimodule A M).tensorBimod
        (associatedBimodule A (Mod.regular A.X))).actLeft ≫
        e.hom.hom = (A.X ◁ e.hom.hom) ≫ (associatedBimodule A M).actLeft
    exact e.hom.left_act_hom
  · change (associatedBimodule A M).actLeft ≫ e.inv.hom =
      (A.X ◁ e.inv.hom) ≫
        ((associatedBimodule A M).tensorBimod
          (associatedBimodule A (Mod.regular A.X))).actLeft
    exact e.inv.left_act_hom
  · apply Mod.hom_ext
    change (e.hom ≫ e.inv).hom =
      (𝟙 ((associatedBimodule A M).tensorBimod (associatedBimodule A (Mod.regular A.X))) :
        (associatedBimodule A M).tensorBimod (associatedBimodule A (Mod.regular A.X)) ⟶ _).hom
    exact congrArg Bimod.Hom.hom e.hom_inv_id
  · apply Mod.hom_ext
    change (e.inv ≫ e.hom).hom =
      (𝟙 (associatedBimodule A M) : associatedBimodule A M ⟶ _).hom
    exact congrArg Bimod.Hom.hom e.inv_hom_id

private theorem relativeTensorLeftUnitor_π (M : Mod C A.X) :
    relativeTensorπ A (relativeTensorUnit A) M ≫
        (relativeTensorLeftUnitIso A M).hom.hom = M.mod.smul := by
  unfold relativeTensorUnit
  let R : Mon C := { X := A.X }
  let BM : Bimod R R := associatedBimodule A M
  let eReg := associatedRegularBimoduleIso A
  let bπ (X Y : Bimod R R) :
      X.X ⊗ Y.X ⟶ (X.tensorBimod Y).X :=
    coequalizer.π (X.actRight ▷ Y.X)
      ((α_ X.X R.X Y.X).hom ≫ (X.X ◁ Y.actLeft))
  have hwr : bπ (associatedBimodule A (Mod.regular A.X)) BM ≫
      (Bimod.whiskerRight eReg.hom BM).hom =
      (eReg.hom.hom ▷ BM.X) ≫
        bπ (Bimod.regular ({ X := A.X } : Mon C)) BM := by
    dsimp only [bπ]
    dsimp [Bimod.whiskerRight]
    erw [Limits.ι_colimMap]
    rw [parallelPairHom_app_one]
  have hπ : bπ (Bimod.regular R) BM ≫
      (Bimod.leftUnitorBimod BM).hom.hom = BM.actLeft := by
    let Reg := Bimod.regular R
    have hbal : (Reg.actRight ▷ BM.X) ≫ BM.actLeft =
        ((α_ Reg.X R.X BM.X).hom ≫ (Reg.X ◁ BM.actLeft)) ≫
          BM.actLeft := by
      dsimp only [Reg]
      dsimp [Bimod.regular]
      simpa only [Category.assoc] using BM.left_assoc
    dsimp only [bπ]
    unfold Bimod.leftUnitorBimod Bimod.isoOfIso
      Bimod.LeftUnitorBimod.hom Bimod.tensorBimod
      Bimod.TensorBimod.X
    dsimp [Reg, Bimod.regular] at hbal ⊢
    with_reducible_and_instances
      change coequalizer.π _ _ ≫
        coequalizer.desc BM.actLeft hbal = BM.actLeft
    exact coequalizer.π_desc BM.actLeft hbal
  change bπ (associatedBimodule A (Mod.regular A.X)) BM ≫
      ((Bimod.whiskerRight eReg.hom BM).hom ≫
        (Bimod.leftUnitorBimod BM).hom.hom) = BM.actLeft
  rw [← Category.assoc]
  refine (congrArg
    (fun k => k ≫ (Bimod.leftUnitorBimod BM).hom.hom) hwr).trans ?_
  rw [Category.assoc, hπ]
  change (𝟙 A.X ▷ BM.X) ≫ BM.actLeft = BM.actLeft
  rw [id_whiskerRight, Category.id_comp]

private theorem relativeTensorRightUnitor_π (M : Mod C A.X) :
    relativeTensorπ A M (relativeTensorUnit A) ≫
        (relativeTensorRightUnitIso A M).hom.hom = braidedRightAction A M := by
  unfold relativeTensorUnit
  let R : Mon C := { X := A.X }
  let BM : Bimod R R := associatedBimodule A M
  let eReg := associatedRegularBimoduleIso A
  let bπ (X Y : Bimod R R) :
      X.X ⊗ Y.X ⟶ (X.tensorBimod Y).X :=
    coequalizer.π (X.actRight ▷ Y.X)
      ((α_ X.X R.X Y.X).hom ≫ (X.X ◁ Y.actLeft))
  have hwl : bπ BM (associatedBimodule A (Mod.regular A.X)) ≫
      (Bimod.whiskerLeft BM eReg.hom).hom =
      (BM.X ◁ eReg.hom.hom) ≫ bπ BM (Bimod.regular R) := by
    dsimp only [bπ]
    dsimp [Bimod.whiskerLeft]
    erw [Limits.ι_colimMap]
    rw [parallelPairHom_app_one]
  have hπ : bπ BM (Bimod.regular R) ≫
      (Bimod.rightUnitorBimod BM).hom.hom = BM.actRight := by
    let Reg := Bimod.regular R
    have hbal : (BM.actRight ▷ Reg.X) ≫ BM.actRight =
        ((α_ BM.X R.X Reg.X).hom ≫ (BM.X ◁ Reg.actLeft)) ≫
          BM.actRight := by
      dsimp only [Reg]
      dsimp [Bimod.regular]
      rw [Category.assoc, BM.right_assoc, Iso.hom_inv_id_assoc]
    dsimp only [bπ]
    unfold Bimod.rightUnitorBimod Bimod.isoOfIso
      Bimod.RightUnitorBimod.hom Bimod.tensorBimod
      Bimod.TensorBimod.X
    dsimp [Reg, Bimod.regular] at hbal ⊢
    with_reducible_and_instances
      change coequalizer.π _ _ ≫
        coequalizer.desc BM.actRight hbal = BM.actRight
    exact coequalizer.π_desc BM.actRight hbal
  change bπ BM (associatedBimodule A (Mod.regular A.X)) ≫
      ((Bimod.whiskerLeft BM eReg.hom).hom ≫
        (Bimod.rightUnitorBimod BM).hom.hom) = BM.actRight
  rw [← Category.assoc]
  refine (congrArg
    (fun k => k ≫ (Bimod.rightUnitorBimod BM).hom.hom) hwl).trans ?_
  rw [Category.assoc, hπ]
  change (BM.X ◁ 𝟙 A.X) ≫ BM.actRight = BM.actRight
  rw [whiskerLeft_id, Category.id_comp]


/-- Explicit monoidal structure on modules given by the relative tensor. -/
@[instance_reducible] noncomputable def instMonoidalCategory :
    MonoidalCategory (Mod C A.X) := by
  have whiskerLeft_π (M : Mod C A.X) {N N' : Mod C A.X} (g : N ⟶ N') :
      relativeTensorπ A M N ≫ (mapSecondInput A M g).hom =
        (M.X ◁ g.hom) ≫ relativeTensorπ A M N' := by
    exact (by exact relativeTensorWhiskerLeft_π A M g)
  have whiskerRight_π {M M' : Mod C A.X} (f : M ⟶ M')
      (N : Mod C A.X) :
      relativeTensorπ A M N ≫ (mapFirstInput A f N).hom =
        (f.hom ▷ N.X) ≫ relativeTensorπ A M' N := by
    exact (by exact relativeTensorWhiskerRight_π A f N)
  have leftUnitor_π (M : Mod C A.X) :
      relativeTensorπ A (relativeTensorUnit A) M ≫
          (relativeTensorLeftUnitIso A M).hom.hom = M.mod.smul := by
    exact (by exact relativeTensorLeftUnitor_π A M)
  have rightUnitor_π (M : Mod C A.X) :
      relativeTensorπ A M (relativeTensorUnit A) ≫
          (relativeTensorRightUnitIso A M).hom.hom = braidedRightAction A M := by
    exact (by exact relativeTensorRightUnitor_π A M)
  refine
    { tensorObj := fun M N ↦ ((relativeTensor A).obj M).obj N
      whiskerLeft := fun M {_ _} g ↦ mapSecondInput A M g
      whiskerRight := fun {_ _} f N ↦ mapFirstInput A f N
      tensorHom := fun f g ↦ relativeTensorMap A f g
      tensorUnit := relativeTensorUnit A
      associator := relativeTensorAssociator A
      leftUnitor := relativeTensorLeftUnitIso A
      rightUnitor := relativeTensorRightUnitIso A
      tensorHom_def := by intros; rfl
      id_tensorHom_id := by
        intro M N
        have hR : mapFirstInput A (𝟙 M) N = 𝟙 _ := by
          exact congrArg (fun t ↦ t.app N) ((relativeTensor A).map_id M)
        have hL : mapSecondInput A M (𝟙 N) = 𝟙 _ := by
          exact ((relativeTensor A).obj M).map_id N
        change mapFirstInput A (𝟙 M) N ≫ mapSecondInput A M (𝟙 N) = 𝟙 _
        rw [hR, hL, Category.id_comp]
      tensorHom_comp_tensorHom := by
        intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
        have hR : mapFirstInput A (f₁ ≫ g₁) X₂ =
            mapFirstInput A f₁ X₂ ≫
              mapFirstInput A g₁ X₂ := by
          exact congrArg (fun t ↦ t.app X₂)
            ((relativeTensor A).map_comp f₁ g₁)
        have hL : mapSecondInput A Z₁ (f₂ ≫ g₂) =
            mapSecondInput A Z₁ f₂ ≫
              mapSecondInput A Z₁ g₂ := by
          exact ((relativeTensor A).obj Z₁).map_comp f₂ g₂
        have hexchange :
            mapSecondInput A Y₁ f₂ ≫
                mapFirstInput A g₁ Y₂ =
              mapFirstInput A g₁ X₂ ≫
                mapSecondInput A Z₁ f₂ := by
          exact ((relativeTensor A).map g₁).naturality f₂
        unfold relativeTensorMap
        simp only [Category.assoc]
        slice_lhs 2 3 => rw [hexchange]
        slice_lhs 1 2 => rw [← hR]
        slice_lhs 2 3 => rw [← hL]
      whiskerLeft_id := by
        intro M N
        exact ((relativeTensor A).obj M).map_id N
      id_whiskerRight := by
        intro M N
        exact congrArg (fun t ↦ t.app N) ((relativeTensor A).map_id M)
      associator_naturality := by
        intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
        have hleftTransport :
            (relativeTensorπ A X₁ X₂ ▷ X₃.X) ≫
                ((relativeTensorMap A f₁ f₂).hom ⊗ₘ f₃.hom) =
              (((f₁.hom ⊗ₘ f₂.hom) ⊗ₘ f₃.hom)) ≫
                (relativeTensorπ A Y₁ Y₂ ▷ Y₃.X) := by
          rw [tensorHom_def, ← Category.assoc, ← comp_whiskerRight,
            relativeTensorMap_π A f₁ f₂, comp_whiskerRight]
          slice_lhs 2 3 => rw [← whisker_exchange]
          rw [tensorHom_def (f₁.hom ⊗ₘ f₂.hom) f₃.hom]
          simp only [Category.assoc]
        have hrightTransport :
            (X₁.X ◁ relativeTensorπ A X₂ X₃) ≫
                (f₁.hom ⊗ₘ (relativeTensorMap A f₂ f₃).hom) =
              (f₁.hom ⊗ₘ (f₂.hom ⊗ₘ f₃.hom)) ≫
                (Y₁.X ◁ relativeTensorπ A Y₂ Y₃) := by
          rw [tensorHom_def]
          slice_lhs 1 2 => rw [whisker_exchange]
          slice_lhs 2 3 =>
            rw [← whiskerLeft_comp, relativeTensorMap_π A f₂ f₃,
              whiskerLeft_comp]
          rw [tensorHom_def f₁.hom (f₂.hom ⊗ₘ f₃.hom),
            tensorHom_def f₂.hom f₃.hom, whiskerLeft_comp]
          simp only [Category.assoc]
        apply relativeTensor_hom_ext A
          (((relativeTensor A).obj X₁).obj X₂) X₃
        let _ : Epi (relativeTensorπ A X₁ X₂ ▷ X₃.X) := by
          change Epi ((tensorRight X₃.X).map (coequalizer.π
            ((associatedBimodule A X₁).actRight ▷ (associatedBimodule A X₂).X)
            ((α_ (associatedBimodule A X₁).X A.X (associatedBimodule A X₂).X).hom ≫
              ((associatedBimodule A X₁).X ◁ (associatedBimodule A X₂).actLeft))))
          infer_instance
        apply (cancel_epi (relativeTensorπ A X₁ X₂ ▷ X₃.X)).1
        simp only [Mod.comp_hom']
        slice_lhs 2 3 => rw [relativeTensorMap_π A]
        slice_lhs 1 2 => rw [hleftTransport]
        slice_lhs 2 4 => rw [relativeTensorAssociator_hom_π A]
        slice_rhs 1 3 => rw [relativeTensorAssociator_hom_π A]
        slice_rhs 3 4 => rw [relativeTensorMap_π A]
        slice_rhs 2 3 => rw [hrightTransport]
        slice_lhs 1 2 => rw [associator_naturality]
        simp only [Category.assoc]
      leftUnitor_naturality := by
        intro M N f
        apply relativeTensor_hom_ext A (relativeTensorUnit A) M
        simp only [Mod.comp_hom']
        slice_lhs 1 2 => rw [whiskerLeft_π]
        slice_lhs 2 3 => rw [leftUnitor_π]
        slice_rhs 1 2 => rw [leftUnitor_π]
        change (A.X ◁ f.hom) ≫ N.mod.smul = M.mod.smul ≫ f.hom
        exact (IsModHom.smul_hom (A := A.X) (f := f.hom)).symm
      rightUnitor_naturality := by
        intro M N f
        apply relativeTensor_hom_ext A M (relativeTensorUnit A)
        simp only [Mod.comp_hom']
        slice_lhs 1 2 => rw [whiskerRight_π]
        slice_lhs 2 3 => rw [rightUnitor_π]
        slice_rhs 1 2 => rw [rightUnitor_π]
        dsimp only [relativeTensorUnit, Mod.regular]
        simp [braidedRightAction]
      pentagon := by
        intro W X Y Z
        let WX := ((relativeTensor A).obj W).obj X
        let WXY := ((relativeTensor A).obj WX).obj Y
        let YZ := ((relativeTensor A).obj Y).obj Z
        apply relativeTensor_hom_ext A WXY Z
        let _ : Epi (relativeTensorπ A WX Y ▷ Z.X) := by
          change Epi ((tensorRight Z.X).map (coequalizer.π
            ((associatedBimodule A WX).actRight ▷ (associatedBimodule A Y).X)
            ((α_ (associatedBimodule A WX).X A.X (associatedBimodule A Y).X).hom ≫
              ((associatedBimodule A WX).X ◁ (associatedBimodule A Y).actLeft))))
          infer_instance
        let _ : Epi (relativeTensorπ A W X ▷ Y.X) := by
          change Epi ((tensorRight Y.X).map (coequalizer.π
            ((associatedBimodule A W).actRight ▷ (associatedBimodule A X).X)
            ((α_ (associatedBimodule A W).X A.X (associatedBimodule A X).X).hom ≫
              ((associatedBimodule A W).X ◁ (associatedBimodule A X).actLeft))))
          infer_instance
        let _ : Epi
            ((relativeTensorπ A W X ▷ Y.X) ▷ Z.X) := by
          change Epi ((tensorRight Y.X ⋙ tensorRight Z.X).map
            (coequalizer.π
              ((associatedBimodule A W).actRight ▷ (associatedBimodule A X).X)
              ((α_ (associatedBimodule A W).X A.X (associatedBimodule A X).X).hom ≫
                ((associatedBimodule A W).X ◁ (associatedBimodule A X).actLeft))))
          infer_instance
        have hAssocRight :
            ((relativeTensorπ A W X ▷ Y.X) ▷ Z.X) ≫
                (relativeTensorπ A WX Y ▷ Z.X) ≫
                  ((relativeTensorAssociator A W X Y).hom.hom ▷ Z.X) =
              ((α_ W.X X.X Y.X).hom ▷ Z.X) ≫
                ((W.X ◁ relativeTensorπ A X Y) ▷ Z.X) ≫
                  (relativeTensorπ A W
                    (((relativeTensor A).obj X).obj Y) ▷ Z.X) := by
          rw [← comp_whiskerRight, ← comp_whiskerRight,
            relativeTensorAssociator_hom_π A, comp_whiskerRight,
            comp_whiskerRight]
        have hAssocFinal := relativeTensorAssociator_hom_π A W X YZ
        apply (cancel_epi (relativeTensorπ A WX Y ▷ Z.X)).1
        apply (cancel_epi
          ((relativeTensorπ A W X ▷ Y.X) ▷ Z.X)).1
        simp only [Mod.comp_hom']
        slice_lhs 3 4 => rw [whiskerRight_π]
        slice_lhs 1 3 => rw [hAssocRight]
        slice_lhs 3 5 => rw [relativeTensorAssociator_hom_π A]
        slice_lhs 5 6 => rw [whiskerLeft_π]
        slice_rhs 2 4 => rw [relativeTensorAssociator_hom_π A]
        slice_lhs 2 3 => rw [associator_naturality_middle]
        slice_lhs 3 5 =>
          rw [← whiskerLeft_comp, ← whiskerLeft_comp,
            relativeTensorAssociator_hom_π A, whiskerLeft_comp,
            whiskerLeft_comp]
        simp only [Category.assoc]
        slice_rhs 1 2 => rw [associator_naturality_left]
        slice_rhs 2 3 => rw [← whisker_exchange]
        slice_rhs 3 5 => erw [hAssocFinal]
        slice_rhs 2 3 => rw [associator_naturality_right]
        slice_lhs 1 3 => rw [pentagon]
        simp only [Category.assoc]
        dsimp only [YZ]
      triangle := by
        intro M N
        apply relativeTensor_hom_ext A
          (((relativeTensor A).obj M).obj (relativeTensorUnit A)) N
        let _ : Epi
            (relativeTensorπ A M (relativeTensorUnit A) ▷ N.X) := by
          change Epi ((tensorRight N.X).map (coequalizer.π
            ((associatedBimodule A M).actRight ▷
              (associatedBimodule A (relativeTensorUnit A)).X)
            ((α_ (associatedBimodule A M).X A.X
                (associatedBimodule A (relativeTensorUnit A)).X).hom ≫
              ((associatedBimodule A M).X ◁
                (associatedBimodule A (relativeTensorUnit A)).actLeft))))
          infer_instance
        apply (cancel_epi
          (relativeTensorπ A M (relativeTensorUnit A) ▷ N.X)).1
        simp only [Mod.comp_hom']
        slice_lhs 1 3 => rw [relativeTensorAssociator_hom_π A]
        slice_lhs 3 4 => rw [whiskerLeft_π]
        slice_lhs 2 3 => rw [← whiskerLeft_comp, leftUnitor_π]
        slice_rhs 2 3 => rw [whiskerRight_π]
        slice_rhs 1 2 =>
          rw [← comp_whiskerRight, rightUnitor_π]
        change (α_ M.X A.X N.X).hom ≫
            (M.X ◁ N.mod.smul) ≫ relativeTensorπ A M N =
          (braidedRightAction A M ▷ N.X) ≫ relativeTensorπ A M N
        exact (relativeTensorπ_balance A M N).symm }

section UnitorProjection

/-- The relative-tensor monoidal structure used in the unit projection equations. -/
local instance unitProjectionMonoidalCategory : MonoidalCategory (Mod C A.X) :=
  instMonoidalCategory A

/-- The left unitor for the selected relative-tensor monoidal structure is
characterized after the balanced-tensor projection by the module action. -/
theorem relativeTensorLeftUnitor_hom_π (M : Mod C A.X) :
    relativeTensorπ A (relativeTensorUnit A) M ≫ (λ_ M).hom.hom =
      M.mod.smul := by
  change relativeTensorπ A (relativeTensorUnit A) M ≫
      (relativeTensorLeftUnitIso A M).hom.hom = M.mod.smul
  exact relativeTensorLeftUnitor_π A M

/-- The right unitor for the selected relative-tensor monoidal structure is
characterized after the balanced-tensor projection by the induced right
action. -/
theorem relativeTensorRightUnitor_hom_π (M : Mod C A.X) :
    relativeTensorπ A M (relativeTensorUnit A) ≫ (ρ_ M).hom.hom =
      (β_ M.X A.X).hom ≫ M.mod.smul := by
  change relativeTensorπ A M (relativeTensorUnit A) ≫
      (relativeTensorRightUnitIso A M).hom.hom = braidedRightAction A M
  exact relativeTensorRightUnitor_π A M

end UnitorProjection

end Tensor

end Braided

section Symmetric

variable [SymmetricCategory C]
variable (A : CommMon C)

section Tensor

local notation "mapSecondInput" =>
  (fun (A : CommMon C) (M : Mod C A.X) {N N' : Mod C A.X} (g : N ⟶ N') =>
    Functor.map (Functor.obj (relativeTensor A) M) g)
local notation "mapFirstInput" =>
  (fun (A : CommMon C) {M M' : Mod C A.X} (f : M ⟶ M') (N : Mod C A.X) =>
    NatTrans.app (Functor.map (relativeTensor A) f) N)


variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Symmetry isomorphism for the balanced relative tensor product. -/
noncomputable def relativeTensorBraiding (M N : Mod C A.X) :
    ((relativeTensor A).obj M).obj N ≅ ((relativeTensor A).obj N).obj M := by
  let braidHom (M N : Mod C A.X) :
      ((relativeTensor A).obj M).obj N ⟶ ((relativeTensor A).obj N).obj M :=
    relativeTensorDesc A M N (((relativeTensor A).obj N).obj M)
      ((β_ M.X N.X).hom ≫ relativeTensorπ A N M)
      (by
        simp only [Lean.Elab.WF.paramLet, braidedRightAction, comp_whiskerRight,
          Category.assoc, BraidedCategory.braiding_naturality_left_assoc,
          BraidedCategory.braiding_tensor_left_hom,
          BraidedCategory.braiding_naturality_right_assoc,
          BraidedCategory.braiding_tensor_right_hom, Iso.hom_inv_id_assoc]
        slice_lhs 6 8 => erw [← relativeTensorπ_balance A N M]
        rw [braidedRightAction, comp_whiskerRight]
        slice_lhs 5 6 =>
          rw [← comp_whiskerRight, SymmetricCategory.symmetry,
            id_whiskerRight]
        simp)
      (by
        have hact :
            (A.X ◁ relativeTensorπ A N M) ≫
                (((relativeTensor A).obj N).obj M).mod.smul =
              (α_ A.X N.X M.X).inv ≫ (N.mod.smul ▷ M.X) ≫
                relativeTensorπ A N M := by
          change (A.X ◁ coequalizer.π
              ((associatedBimodule A N).actRight ▷ (associatedBimodule A M).X)
              ((α_ (associatedBimodule A N).X A.X (associatedBimodule A M).X).hom ≫
                ((associatedBimodule A N).X ◁ (associatedBimodule A M).actLeft))) ≫
                ((associatedBimodule A N).tensorBimod (associatedBimodule A M)).actLeft =
            (α_ A.X N.X M.X).inv ≫ (N.mod.smul ▷ M.X) ≫
              coequalizer.π
                ((associatedBimodule A N).actRight ▷ (associatedBimodule A M).X)
                ((α_ (associatedBimodule A N).X A.X (associatedBimodule A M).X).hom ≫
                  ((associatedBimodule A N).X ◁ (associatedBimodule A M).actLeft))
          exact Bimod.TensorBimod.whiskerLeft_π_actLeft
            (associatedBimodule A N) (associatedBimodule A M)
        rw [whiskerLeft_comp, Category.assoc, hact]
        simp only [Lean.Elab.WF.paramLet, selfLeftAction_actionObj,
          BraidedCategory.braiding_naturality_left_assoc,
          BraidedCategory.braiding_tensor_left_hom, Category.assoc,
          Iso.inv_hom_id_assoc]
        slice_lhs 4 6 =>
          erw [← relativeTensorπ_balance A N M]
        rw [braidedRightAction, comp_whiskerRight]
        slice_lhs 3 4 =>
          rw [← comp_whiskerRight, SymmetricCategory.symmetry,
            id_whiskerRight]
        simp)
  have braidHom_π (M N : Mod C A.X) :
      relativeTensorπ A M N ≫ (braidHom M N).hom =
        (β_ M.X N.X).hom ≫ relativeTensorπ A N M := by
    dsimp only [braidHom]
    exact relativeTensorDesc_π A M N (((relativeTensor A).obj N).obj M)
      ((β_ M.X N.X).hom ≫ relativeTensorπ A N M) _ _
  refine
    { hom := braidHom M N
      inv := braidHom N M
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply relativeTensor_hom_ext A M N
    simp only [Mod.comp_hom']
    rw [← Category.assoc, braidHom_π, Category.assoc,
      braidHom_π]
    simp
  · apply relativeTensor_hom_ext A N M
    simp only [Mod.comp_hom']
    rw [← Category.assoc, braidHom_π, Category.assoc,
      braidHom_π]
    simp

/-- The relative-tensor braiding is characterized by the ambient braiding
after the balanced-tensor projection. -/
theorem relativeTensorBraiding_hom_π (M N : Mod C A.X) :
    relativeTensorπ A M N ≫ (relativeTensorBraiding A M N).hom.hom =
      (β_ M.X N.X).hom ≫ relativeTensorπ A N M := by
  dsimp only [relativeTensorBraiding]
  exact relativeTensorDesc_π A M N (((relativeTensor A).obj N).obj M)
    ((β_ M.X N.X).hom ≫ relativeTensorπ A N M) _ _

/-- The relative braiding is involutive. -/
theorem relativeTensorSymmetry (M N : Mod C A.X) :
    (relativeTensorBraiding A M N).hom ≫
      (relativeTensorBraiding A N M).hom = 𝟙 _ := by
  apply relativeTensor_hom_ext A M N
  simp only [Mod.comp_hom']
  rw [← Category.assoc, relativeTensorBraiding_hom_π,
    Category.assoc, relativeTensorBraiding_hom_π]
  simp

/-- Explicit symmetric structure on modules for the relative tensor. -/
@[instance_reducible] noncomputable def instSymmetricCategory :
    @SymmetricCategory (Mod C A.X) _ (instMonoidalCategory A) := by
  letI : MonoidalCategory (Mod C A.X) := instMonoidalCategory A
  have whiskerLeft_π (M : Mod C A.X) {N N' : Mod C A.X} (g : N ⟶ N') :
      relativeTensorπ A M N ≫ (mapSecondInput A M g).hom =
        (M.X ◁ g.hom) ≫ relativeTensorπ A M N' := by
    exact (by exact relativeTensorWhiskerLeft_π A M g)
  have whiskerRight_π {M M' : Mod C A.X} (f : M ⟶ M')
      (N : Mod C A.X) :
      relativeTensorπ A M N ≫ (mapFirstInput A f N).hom =
        (f.hom ▷ N.X) ≫ relativeTensorπ A M' N := by
    exact (by exact relativeTensorWhiskerRight_π A f N)
  have associatorInv_π (M N P : Mod C A.X) :
      (M.X ◁ relativeTensorπ A N P) ≫
          relativeTensorπ A M (((relativeTensor A).obj N).obj P) ≫
            (relativeTensorAssociator A M N P).inv.hom =
        (α_ M.X N.X P.X).inv ≫
          (relativeTensorπ A M N ▷ P.X) ≫
            relativeTensorπ A (((relativeTensor A).obj M).obj N) P := by
    let e := relativeTensorAssociator A M N P
    let eX :
        (((relativeTensor A).obj
            (((relativeTensor A).obj M).obj N)).obj P).X ≅
          (((relativeTensor A).obj M).obj
            (((relativeTensor A).obj N).obj P)).X :=
      { hom := e.hom.hom
        inv := e.inv.hom
        hom_inv_id := congrArg Mod.Hom.hom e.hom_inv_id
        inv_hom_id := congrArg Mod.Hom.hom e.inv_hom_id }
    let _ : IsIso eX.hom := eX.isIso_hom
    apply (cancel_mono eX.hom).1
    dsimp only [eX]
    simp only [Category.assoc]
    rw [show e.inv.hom ≫ e.hom.hom = 𝟙 _ from eX.inv_hom_id,
      Category.comp_id, relativeTensorAssociator_hom_π A]
    simp
  refine
    { braiding := relativeTensorBraiding A
      braiding_naturality_right := by
        intro M N N' g
        change mapSecondInput A M g ≫
            (relativeTensorBraiding A M N').hom =
          (relativeTensorBraiding A M N).hom ≫
            mapFirstInput A g M
        apply relativeTensor_hom_ext A M N
        simp only [Mod.comp_hom']
        slice_lhs 1 2 => rw [whiskerLeft_π]
        slice_lhs 2 3 => rw [relativeTensorBraiding_hom_π A]
        slice_rhs 1 2 => rw [relativeTensorBraiding_hom_π A]
        slice_rhs 2 3 => rw [whiskerRight_π]
        slice_lhs 1 2 => rw [BraidedCategory.braiding_naturality_right]
        simp only [Category.assoc]
      braiding_naturality_left := by
        intro M M' f N
        change mapFirstInput A f N ≫
            (relativeTensorBraiding A M' N).hom =
          (relativeTensorBraiding A M N).hom ≫
            mapSecondInput A N f
        apply relativeTensor_hom_ext A M N
        simp only [Mod.comp_hom']
        slice_lhs 1 2 => rw [whiskerRight_π]
        slice_lhs 2 3 => rw [relativeTensorBraiding_hom_π A]
        slice_rhs 1 2 => rw [relativeTensorBraiding_hom_π A]
        slice_rhs 2 3 => rw [whiskerLeft_π]
        slice_lhs 1 2 => rw [BraidedCategory.braiding_naturality_left]
        simp only [Category.assoc]
      hexagon_forward := by
        intro M N P
        let MN := ((relativeTensor A).obj M).obj N
        let NP := ((relativeTensor A).obj N).obj P
        change (relativeTensorAssociator A M N P).hom ≫
            (relativeTensorBraiding A M NP).hom ≫
              (relativeTensorAssociator A N P M).hom =
          mapFirstInput A
                (relativeTensorBraiding A M N).hom P ≫
            (relativeTensorAssociator A N M P).hom ≫
              mapSecondInput A N
                (relativeTensorBraiding A M P).hom
        apply relativeTensor_hom_ext A MN P
        let _ : Epi (relativeTensorπ A M N ▷ P.X) := by
          change Epi ((tensorRight P.X).map (coequalizer.π
            ((associatedBimodule A M).actRight ▷ (associatedBimodule A N).X)
            ((α_ (associatedBimodule A M).X A.X (associatedBimodule A N).X).hom ≫
              ((associatedBimodule A M).X ◁ (associatedBimodule A N).actLeft))))
          infer_instance
        apply (cancel_epi (relativeTensorπ A M N ▷ P.X)).1
        simp only [Mod.comp_hom']
        slice_lhs 1 3 => rw [relativeTensorAssociator_hom_π A]
        slice_lhs 3 4 => rw [relativeTensorBraiding_hom_π A]
        slice_lhs 2 3 =>
          rw [BraidedCategory.braiding_naturality_right]
        slice_lhs 3 5 => rw [relativeTensorAssociator_hom_π A]
        slice_rhs 2 3 => rw [whiskerRight_π]
        slice_rhs 1 2 =>
          rw [← comp_whiskerRight, relativeTensorBraiding_hom_π A,
            comp_whiskerRight]
        slice_rhs 2 4 => rw [relativeTensorAssociator_hom_π A]
        slice_rhs 4 5 => rw [whiskerLeft_π]
        slice_rhs 3 4 =>
          rw [← whiskerLeft_comp, relativeTensorBraiding_hom_π A,
            whiskerLeft_comp]
        slice_lhs 1 3 => rw [BraidedCategory.hexagon_forward]
        simp only [Category.assoc]
      hexagon_reverse := by
        intro M N P
        let NP := ((relativeTensor A).obj N).obj P
        let MN := ((relativeTensor A).obj M).obj N
        let MP := ((relativeTensor A).obj M).obj P
        change (relativeTensorAssociator A M N P).inv ≫
            (relativeTensorBraiding A MN P).hom ≫
              (relativeTensorAssociator A P M N).inv =
          mapSecondInput A M
                (relativeTensorBraiding A N P).hom ≫
            (relativeTensorAssociator A M P N).inv ≫
              mapFirstInput A
                (relativeTensorBraiding A M P).hom N
        apply relativeTensor_hom_ext A M NP
        let _ : Epi (M.X ◁ relativeTensorπ A N P) := by
          change Epi ((tensorLeft M.X).map (coequalizer.π
            ((associatedBimodule A N).actRight ▷ (associatedBimodule A P).X)
            ((α_ (associatedBimodule A N).X A.X (associatedBimodule A P).X).hom ≫
              ((associatedBimodule A N).X ◁ (associatedBimodule A P).actLeft))))
          infer_instance
        apply (cancel_epi (M.X ◁ relativeTensorπ A N P)).1
        simp only [Mod.comp_hom']
        slice_lhs 1 3 => rw [associatorInv_π]
        slice_lhs 3 4 => rw [relativeTensorBraiding_hom_π A]
        slice_lhs 2 3 =>
          rw [BraidedCategory.braiding_naturality_left]
        slice_lhs 3 5 => rw [associatorInv_π]
        slice_rhs 2 3 => rw [whiskerLeft_π]
        slice_rhs 1 2 =>
          rw [← whiskerLeft_comp, relativeTensorBraiding_hom_π A,
            whiskerLeft_comp]
        slice_rhs 2 4 => rw [associatorInv_π]
        slice_rhs 4 5 => rw [whiskerRight_π]
        slice_rhs 3 4 =>
          rw [← comp_whiskerRight, relativeTensorBraiding_hom_π A,
            comp_whiskerRight]
        slice_lhs 1 3 => rw [BraidedCategory.hexagon_reverse]
        simp only [Category.assoc]
      symmetry := relativeTensorSymmetry A }


end Tensor

end Symmetric

end CategoryTheory.Mod
