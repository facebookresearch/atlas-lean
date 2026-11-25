/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.Components
public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Basic

/-!
# Original degree-zero maps of finite-action positive generators

The actual block coefficient category is empty below the generating degree.
Its original colimit identifies the original free R-module component with the
initial object, for every genuine finite-action input. No scalar or unit
cofibrancy is used in this calculation.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.PositiveLevelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  (R : DayFunctor I C) [MonObj R]

/-- Below the actual generating degree, the entire original coefficient category is empty. -/
theorem actionComponentIndex_empty {n m : ℕ} (h : m < n) :
    IsEmpty (CostructuredArrow (actionTensorIndex n) (card m)) := by
  refine ⟨fun d => ?_⟩
  have hObj : (d.left.1 ⊗ card n).of = (card m).of :=
    FintypeCat.Skeleton.is_skeletal ⟨d.hom.iso⟩
  have hLen := congrArg FintypeCat.Skeleton.len hObj
  change d.left.1.of.len + n = m at hLen
  have hnle : n ≤ m := by
    rw [← hLen]
    exact Nat.le_add_left n d.left.1.of.len
  exact (Nat.not_le_of_gt h) hnle

/-- The original free component is initial for every finite-action input below its degree. -/
def actionBelowObjectIso {n m : ℕ} (h : m < n) (A : degreeActionCategory (C := C) n) :
    ((degreeActionFreeAt R n).obj A).X.functor.obj (card m) ≅ ⊥_ C := by
  let _ : IsEmpty (CostructuredArrow (actionTensorIndex n) (card m)) := actionComponentIndex_empty h
  let hInitial := isColimitEquivIsInitialOfIsEmpty C
    (colimit.cocone (actionComponentDiagram R n m A))
        (colimit.isColimit (actionComponentDiagram R n m A))
  exact actionComponentIso R n m A ≪≫ (initialIsoIsInitial hInitial).symm

/-- The complete original evaluated free functor below degree is the constant initial functor. -/
def actionBelowIso {n m : ℕ} (h : m < n) :
    degreeActionFreeAt R n ⋙ CategoryTheory.Mod.dayEvaluation R (card m) ≅
      (Functor.const (degreeActionCategory (C := C) n)).obj (⊥_ C) := by
  refine NatIso.ofComponents (fun A => actionBelowObjectIso R h A) ?_
  intro A B f
  exact (initialIsInitial.ofIso (actionBelowObjectIso R h A).symm).hom_ext _ _

/-- The original degree-zero component of every actual positive finite-action free map is an
isomorphism. -/
theorem actionFree_zero_isIso {n : ℕ} (hn : 0 < n)
    {A B : degreeActionCategory (C := C) n} (f : A ⟶ B) :
    IsIso ((zeroEvaluation R).map ((degreeActionFreeAt R n).map f)) := by
  let e := actionBelowIso R hn
  let χ : Arrow.mk ((zeroEvaluation R).map ((degreeActionFreeAt R n).map f)) ≅ Arrow.mk (𝟙 (⊥_ C))
      :=
    Arrow.isoMk (e.app A) (e.app B) (e.hom.naturality f).symm
  exact ((isomorphisms C).arrow_iso_iff χ).mpr (inferInstance : IsIso (𝟙 (⊥_ C)))

/-- Every actual chosen positive finite-action generator retains an isomorphic original degree-zero
component. -/
theorem actionPositiveGenerators_le_zeroIsomorphisms
    (K : ∀ n, MorphismProperty (degreeActionCategory (C := C) n)) :
    actionGenerators R true K ≤ zeroIsomorphisms R := by
  intro A B f hf
  obtain ⟨q⟩ := hf
  change IsIso ((zeroEvaluation R).map ((degreeActionFreeAt R q.1.1).map q.2.1.hom))
  exact actionFree_zero_isIso R (q.1.2 rfl) q.2.1.hom

/-- The ordinary finite-action free generator family contains the very same positive maps and
labels. -/
theorem actionPositiveGenerators_le_ordinary
    (K : ∀ n, MorphismProperty (degreeActionCategory (C := C) n)) :
    actionGenerators R true K ≤ actionGenerators R false K := by
  intro A B f hf
  obtain ⟨q⟩ := hf
  exact ofHoms.mk (f := fun t : Σ n : {n : ℕ // false = true → 0 < n}, (K n.1).toSet =>
    (degreeActionFreeAt R t.1.1).map t.2.1.hom) ⟨⟨q.1.1, by simp⟩, q.2⟩

/-- A finite-action positive right map with isomorphic degree zero is an ordinary right map. -/
theorem actionPositiveRight_zero_le_ordinaryRight
    (K : ∀ n, MorphismProperty (degreeActionCategory (C := C) n)) :
    (actionGenerators R true K).rlp ⊓ zeroIsomorphisms R ≤ (actionGenerators R false K).rlp := by
  intro A B f hf
  apply (actionGenerators_rlp_iff R false K f).mpr
  intro n _
  by_cases hn : 0 < n
  · exact (actionGenerators_rlp_iff R true K f).mp hf.1 n (fun _ => hn)
  · have hzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    let _ : IsIso ((zeroEvaluation R).map f) := hf.2
    let _ (a : degreeActionIndex 0) : IsIso (((degreeActionEvaluation R 0).map f).app a) := by
      change IsIso ((zeroEvaluation R).map f)
      exact hf.2
    let _ : IsIso ((degreeActionEvaluation R 0).map f) := NatIso.isIso_of_isIso_app _
    exact (K 0).rlp_of_isIso _

end HomotopicalAlgebra.PositiveLevelModel
