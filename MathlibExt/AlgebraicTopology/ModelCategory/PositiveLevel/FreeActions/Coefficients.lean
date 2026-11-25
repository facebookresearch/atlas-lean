/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.BlockEquivalence
public import MathlibExt.CategoryTheory.Action.FreeActionCopower

/-!
# Original arbitrary-action free R-module residual coefficients

The pure coefficient diagram uses the original complement and input group
maps. Its actual free action colimit is a copower on the original orbit set.
These formulas retain an arbitrary Day coefficient, without a monoid structure
on that pure coefficient diagram.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe v u

open CategoryTheory Limits MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped CategoryTheory.Prod CategoryTheory.MonObj
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

namespace HomotopicalAlgebra.PositiveLevelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The actual combined scalar and input permutation action on block bijections. -/
local instance coefficientPairedBlockAction (n m : ℕ) :
    MulAction (pairedBlockGroup n m) (pairedBlockAlphabet n m) := pairedBlockAction n m

/-- The actual paired source endomorphisms, retaining the input permutation coordinate. -/
def pairedBlockSourceEnd (n m : ℕ) : pairedBlockGroup n m →*
    End (card (m - n), SingleObj.star (Equiv.Perm (Fin n))) where
  toFun a := .of ⟨a.1.asIso.hom, finAutEquiv (card n) a.2⟩
  map_one' := by
    apply End.ext
    apply Prod.ext
    · rfl
    · change finAutEquiv (card n) 1 = 1
      exact map_one _
  map_mul' a b := by
    apply End.ext
    apply Prod.ext
    · rfl
    · change finAutEquiv (card n) (a.2 * b.2) = finAutEquiv (card n) a.2 * finAutEquiv (card n) b.2
      exact map_mul _ _ _

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  (B : DayFunctor I C)

/-- The pure actual paired coefficient action on the residual scalar and finite-action input. -/
def pairedCoefficientAction (n m : ℕ) (A : degreeActionCategory (C := C) n) :
    pairedBlockGroup n m →* End
        (B.functor.obj (card (m - n)) ⊗ A.obj (SingleObj.star (Equiv.Perm (Fin n)))) :=
  (Functor.mapEnd (card (m - n), SingleObj.star (Equiv.Perm (Fin n))) (B.functor ⊠ A)).comp
    (pairedBlockSourceEnd n m)

omit [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)] in
/-- Every actual paired coefficient arrow has its original tensor-map formula. -/
theorem pairedCoefficientAction_apply (n m : ℕ) (A : degreeActionCategory (C := C) n)
    (a : pairedBlockGroup n m) :
    (pairedCoefficientAction B n m A a).asHom =
      B.functor.map a.1.asIso.hom ⊗ₘ A.map (finAutEquiv (card n) a.2) := by
  change (B.functor.map a.1.asIso.hom ▷ A.obj (SingleObj.star (Equiv.Perm (Fin n)))) ≫
    (B.functor.obj (card (m - n)) ◁ A.map (finAutEquiv (card n) a.2)) = _
  exact (tensorHom_def _ _).symm

/-- The whole normalized coefficient diagram on the original actual orbit action groupoid. -/
abbrev normalizedCoefficientDiagram (n m : ℕ) (A : degreeActionCategory (C := C) n) :
    ActionCategory (pairedBlockGroup n m) (pairedBlockAlphabet n m) ⥤ C :=
  ActionCategory.coefficientDiagram (pairedBlockGroup n m) (pairedBlockAlphabet n m)
    (B.functor.obj (card (m - n)) ⊗ A.obj (SingleObj.star (Equiv.Perm (Fin n))))
    (pairedCoefficientAction B n m A)

omit [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)] in
/-- The actual paired inclusion retains the original entire coefficient functor, including every
map. -/
theorem pairedBlockInclusion_coefficientDiagram (n m : ℕ) (A : degreeActionCategory (C := C) n) :
    pairedBlockInclusion n m ⋙ actionComponentDiagram B n m A = normalizedCoefficientDiagram B n m
        A := rfl

/-- The original paired action colimit is its actual orbit-indexed residual coefficient copower. -/
def normalizedCoefficientCopowerIso (n m : ℕ) (A : degreeActionCategory (C := C) n) :
    colimit (normalizedCoefficientDiagram B n m A) ≅
      ∐ fun _ : MulAction.orbitRel.Quotient (pairedBlockGroup n m) (pairedBlockAlphabet n m) =>
        B.functor.obj (card (m - n)) ⊗ A.obj (SingleObj.star (Equiv.Perm (Fin n))) :=
  ActionCategory.freeActionColimitCopowerIso (pairedBlockGroup n m) (pairedBlockAlphabet n m)
    (B.functor.obj (card (m - n)) ⊗ A.obj (SingleObj.star (Equiv.Perm (Fin n))))
    (pairedCoefficientAction B n m A)
    (pairedBlockMulAction_free (card (m - n)) (card n) (card m))

variable [MonObj B]

/-- The actual original free R-module coefficient is the whole normalized arbitrary-action
coefficient colimit. -/
def actionNormalizedComponentIso (n m : ℕ) (A : degreeActionCategory (C := C) n) :
    ((degreeActionFreeAt B n).obj A).X.functor.obj (card m) ≅ colimit
        (normalizedCoefficientDiagram B n m A) :=
  actionComponentIso B n m A ≪≫
    (Functor.Final.colimitIso (pairedBlockInclusion n m) (actionComponentDiagram B n m A)).symm

/-- Every actual original component of a free R-module on arbitrary finite action is its original
residual copower. -/
def actionResidualCopowerObjectIso (n m : ℕ) (A : degreeActionCategory (C := C) n) :
    ((degreeActionFreeAt B n).obj A).X.functor.obj (card m) ≅
      ∐ fun _ : MulAction.orbitRel.Quotient (pairedBlockGroup n m) (pairedBlockAlphabet n m) =>
        B.functor.obj (card (m - n)) ⊗ A.obj (SingleObj.star (Equiv.Perm (Fin n))) :=
  actionNormalizedComponentIso B n m A ≪≫ normalizedCoefficientCopowerIso B n m A

end HomotopicalAlgebra.PositiveLevelModel
