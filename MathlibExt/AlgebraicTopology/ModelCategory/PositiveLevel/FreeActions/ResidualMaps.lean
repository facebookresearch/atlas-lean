/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.ComponentMaps

/-!
# Entire original paired-orbit copower maps of free R-modules

Every original finite-action arrow is compared with the original residual scalar
tensor map on each original orbit summand. The comparison uses the actual Day
coefficient maps, the whole original block equivalence, and the existing free
paired-action colimit comparison.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe v u

open CategoryTheory Limits MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped CategoryTheory.MonObj CategoryTheory.Prod
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

namespace HomotopicalAlgebra.PositiveLevelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The original paired action retained by every residual coefficient arrow. -/
local instance residualPairedBlockAction (n m : ℕ) :
    MulAction (pairedBlockGroup n m) (pairedBlockAlphabet n m) := pairedBlockAction n m

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  (R : DayFunctor I C)

omit [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)] in
/-- The actual original residual coefficient map is equivariant for both original block actions. -/
theorem pairedCoefficientAction_naturality (n m : ℕ) {A B : degreeActionCategory (C := C) n}
    (f : A ⟶ B)
    (a : pairedBlockGroup n m) :
    (pairedCoefficientAction R n m A a).asHom ≫
      (R.functor.obj (card (m - n)) ◁ f.app (SingleObj.star (Equiv.Perm (Fin n)))) =
        (R.functor.obj (card (m - n)) ◁ f.app (SingleObj.star (Equiv.Perm (Fin n)))) ≫
          (pairedCoefficientAction R n m B a).asHom := by
  let g := R.functor.map a.1.asIso.hom
  let s := finAutEquiv (card n) a.2
  let k := f.app (SingleObj.star (Equiv.Perm (Fin n)))
  have hn : A.map s ≫ k = k ≫ B.map s := f.naturality s
  rw [pairedCoefficientAction_apply, pairedCoefficientAction_apply, ← id_tensorHom]
  change (g ⊗ₘ A.map s) ≫ (𝟙 _ ⊗ₘ k) = (𝟙 _ ⊗ₘ k) ≫ (g ⊗ₘ B.map s)
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  exact congrArg (fun t => g ⊗ₘ t) hn

/-- The complete normalized paired coefficient arrow on the original action groupoid. -/
def normalizedCoefficientMap (n m : ℕ) {A B : degreeActionCategory (C := C) n} (f : A ⟶ B) :
    normalizedCoefficientDiagram R n m A ⟶ normalizedCoefficientDiagram R n m B :=
  ActionCategory.coefficientNatTrans (pairedBlockGroup n m) (pairedBlockAlphabet n m)
    (R.functor.obj (card (m - n)) ⊗ A.obj (SingleObj.star (Equiv.Perm (Fin n))))
    (R.functor.obj (card (m - n)) ⊗ B.obj (SingleObj.star (Equiv.Perm (Fin n))))
    (pairedCoefficientAction R n m A) (pairedCoefficientAction R n m B)
    (R.functor.obj (card (m - n)) ◁ f.app (SingleObj.star (Equiv.Perm (Fin n))))
    (pairedCoefficientAction_naturality R n m f)

omit [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)] in
/-- The actual original block inclusion retains the whole original coefficient map. -/
theorem pairedBlockInclusion_coefficientMap (n m : ℕ) {A B : degreeActionCategory (C := C) n}
    (f : A ⟶ B) :
    Functor.whiskerLeft (pairedBlockInclusion n m) (actionComponentMap R n m f) =
        normalizedCoefficientMap R n m f := by
  ext x
  exact actionComponentMap_app R n m f ((pairedBlockInclusion n m).obj x)

omit [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)] in
/-- The same original orbit coordinates carry every original paired coefficient map. -/
theorem normalizedCoefficientCopowerIso_naturality (n m : ℕ)
    {A B : degreeActionCategory (C := C) n} (f : A ⟶ B) :
    colimMap (normalizedCoefficientMap R n m f) ≫ (normalizedCoefficientCopowerIso R n m B).hom =
      (normalizedCoefficientCopowerIso R n m A).hom ≫
        Limits.Sigma.map
            (fun _ : MulAction.orbitRel.Quotient (pairedBlockGroup n m) (pairedBlockAlphabet n m) =>
          R.functor.obj (card (m - n)) ◁ f.app (SingleObj.star (Equiv.Perm (Fin n)))) :=
  ActionCategory.freeActionColimitCopowerIso_naturality (pairedBlockGroup n m)
      (pairedBlockAlphabet n m)
    (R.functor.obj (card (m - n)) ⊗ A.obj (SingleObj.star (Equiv.Perm (Fin n))))
    (pairedCoefficientAction R n m A)
    (pairedBlockMulAction_free (card (m - n)) (card n) (card m))
    (R.functor.obj (card (m - n)) ⊗ B.obj (SingleObj.star (Equiv.Perm (Fin n))))
    (pairedCoefficientAction R n m B)
    (R.functor.obj (card (m - n)) ◁ f.app (SingleObj.star (Equiv.Perm (Fin n))))
    (pairedCoefficientAction_naturality R n m f)

variable [MonObj R]

/-- The original normalized free-module colimit comparison retains every actual input-map value. -/
theorem actionNormalizedComponentIso_naturality (n m : ℕ) {A B : degreeActionCategory (C := C) n}
    (f : A ⟶ B) :
    ((degreeActionFreeAt R n).map f).hom.natTrans.app (card m) ≫
        (actionNormalizedComponentIso R n m B).hom =
      (actionNormalizedComponentIso R n m A).hom ≫ colimMap (normalizedCoefficientMap R n m f) := by
  let j := pairedBlockInclusion n m
  have hFinal : colimMap (actionComponentMap R n m f) ≫
      (Functor.Final.colimitIso j (actionComponentDiagram R n m B)).inv =
        (Functor.Final.colimitIso j (actionComponentDiagram R n m A)).inv ≫
          colimMap (Functor.whiskerLeft j (actionComponentMap R n m f)) :=
    (Functor.Final.colimIso j).inv.naturality (actionComponentMap R n m f)
  rw [pairedBlockInclusion_coefficientMap] at hFinal
  have hComp := actionComponentIso_naturality R n m f
  change ((degreeActionFreeAt R n).map f).hom.natTrans.app (card m) ≫
      ((actionComponentIso R n m B).hom ≫
          (Functor.Final.colimitIso j (actionComponentDiagram R n m B)).inv) =
        ((actionComponentIso R n m A).hom ≫
            (Functor.Final.colimitIso j (actionComponentDiagram R n m A)).inv) ≫
          colimMap (normalizedCoefficientMap R n m f)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (Functor.Final.colimitIso j (actionComponentDiagram R n m B)).inv)
        hComp).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => (actionComponentIso R n m A).hom ≫ t) hFinal).trans
            (Category.assoc _ _ _).symm)))

/-- Every actual original evaluated free-module arrow is the original residual tensor map on each
orbit summand. -/
def actionResidualCopowerArrowIso (n m : ℕ) {A B : degreeActionCategory (C := C) n} (f : A ⟶ B) :
    Arrow.mk ((CategoryTheory.Mod.dayEvaluation R (card m)).map ((degreeActionFreeAt R n).map f)) ≅
      Arrow.mk (Limits.Sigma.map
        (fun _ : MulAction.orbitRel.Quotient (pairedBlockGroup n m) (pairedBlockAlphabet n m) =>
          R.functor.obj (card (m - n)) ◁ f.app (SingleObj.star (Equiv.Perm (Fin n))))) := by
  refine Arrow.isoMk (actionResidualCopowerObjectIso R n m A)
      (actionResidualCopowerObjectIso R n m B) ?_
  have h1 := actionNormalizedComponentIso_naturality R n m f
  have h2 := normalizedCoefficientCopowerIso_naturality R n m f
  have h := (congrArg (fun t => t ≫ (normalizedCoefficientCopowerIso R n m B).hom) h1).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => (actionNormalizedComponentIso R n m A).hom ≫ t) h2).trans
          (Category.assoc _ _ _).symm))
  change ((actionNormalizedComponentIso R n m A).hom ≫
      (normalizedCoefficientCopowerIso R n m A).hom) ≫
      Limits.Sigma.map
          (fun _ : MulAction.orbitRel.Quotient (pairedBlockGroup n m) (pairedBlockAlphabet n m) =>
        R.functor.obj (card (m - n)) ◁ f.app (SingleObj.star (Equiv.Perm (Fin n)))) =
      ((degreeActionFreeAt R n).map f).hom.natTrans.app (card m) ≫
        (actionNormalizedComponentIso R n m B).hom ≫ (normalizedCoefficientCopowerIso R n m B).hom
  exact h.symm.trans (Category.assoc _ _ _)

end HomotopicalAlgebra.PositiveLevelModel
