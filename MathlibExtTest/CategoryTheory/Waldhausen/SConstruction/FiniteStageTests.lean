/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Zero
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.FiniteStage

/-!
# Finite Waldhausen-stage consumer tests

Consumer checks for `horiz`/`vert` endpoint behavior, `IsStage` diagonal-zero
and cofiber-triple projections, and the actual interval squares. A diagram in
`AddCommGrpCat` with strict row `ℤ ⟶ ℤ ⟶ 0` constructs a stage, proves its
`(0, 1)` value is nonzero, and tests the strict and both equal-index squares.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.FiniteStageTests

section AbstractClients

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- `horiz` fixes the left endpoint. -/
example :
    (horiz (show (0 : Fin 3) ≤ 1 by decide)
      (show (1 : Fin 3) ≤ 2 by decide)).left = 𝟙 (0 : Fin 3) :=
  rfl

/-- `horiz` advances the right endpoint. -/
example :
    (horiz (show (0 : Fin 3) ≤ 1 by decide)
      (show (1 : Fin 3) ≤ 2 by decide)).right =
      homOfLE (show (1 : Fin 3) ≤ 2 by decide) :=
  rfl

/-- `vert` advances the left endpoint. -/
example :
    (vert (show (0 : Fin 3) ≤ 1 by decide)
      (show (1 : Fin 3) ≤ 2 by decide)).left =
      homOfLE (show (0 : Fin 3) ≤ 1 by decide) :=
  rfl

/-- `vert` fixes the right endpoint. -/
example :
    (vert (show (0 : Fin 3) ≤ 1 by decide)
      (show (1 : Fin 3) ≤ 2 by decide)).right = 𝟙 (2 : Fin 3) :=
  rfl

/-- `IsStage 1` diagonal-zero extraction at a concrete `Fin 2` index. -/
example (A : Ar 1 ⥤ C) (h : IsStage 1 A) :
    IsZero (A.obj (diag (1 : Fin 2))) :=
  h.diag_isZero (1 : Fin 2)

/-- `IsStage 2` cofiber extraction on the canonical `(0,1) ⟶ (0,2) ⟶ (1,2)` maps. -/
example (A : Ar 2 ⥤ C) (h : IsStage 2 A) :
    IsCofibrationSequence
      (A.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)))
      (A.map (vert (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide))) :=
  h.cofiber_triple (show (0 : Fin 3) ≤ 1 by decide)
    (show (1 : Fin 3) ≤ 2 by decide)

/-- `IsStage 2` actual-square pushout at concrete `(0,1,2)`. -/
example (A : Ar 2 ⥤ C) (h : IsStage 2 A) :
    IsPushout
      (A.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)))
      (A.map (toDiag (show (0 : Fin 3) ≤ 1 by decide)))
      (A.map (vert (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)))
      (A.map (fromDiag (show (1 : Fin 3) ≤ 2 by decide))) :=
  isPushout_actualSquare h _ _

end AbstractClients

open ZeroObject

private local instance : WaldhausenCategoryWithoutGluing AddCommGrpCat where
  cofibrations := ⊤
  weakEquivalences := MorphismProperty.isomorphisms _
  cofibrations_isMultiplicative := inferInstance
  cofibrations_respectsIso := inferInstance
  weakEquivalences_isMultiplicative := inferInstance
  weakEquivalences_respectsIso := inferInstance
  zero_isCofibration _ _ := trivial
  cofibration_pushout i _ _ f :=
    ⟨pushout f i, pushout.inl f i, pushout.inr f i, IsPushout.of_hasPushout f i, trivial⟩

/-- The nonzero intervals are `(0, 1)` and `(0, 2)`. -/
private def active (A : Ar 2) : Prop := A.left = 0 ∧ A.right ≠ 0

private instance (A : Ar 2) : Decidable (active A) :=
  inferInstanceAs (Decidable (A.left = 0 ∧ A.right ≠ 0))

private noncomputable def splitObj (A : Ar 2) : AddCommGrpCat :=
  if active A then AddCommGrpCat.of ℤ else 0

private noncomputable def splitMap {A B : Ar 2} (_ : A ⟶ B) : splitObj A ⟶ splitObj B :=
  if h : active A ∧ active B then eqToHom (by simp [splitObj, h.1, h.2]) else 0

private theorem inactive_isZero {A : Ar 2} (h : ¬ active A) : IsZero (splitObj A) := by
  simp only [splitObj, ite_eq_right h]
  exact isZero_zero _

/-- The strict triple of this diagram is `ℤ --id→ ℤ → 0`. -/
private noncomputable def splitDiagram : Ar 2 ⥤ AddCommGrpCat where
  obj := splitObj
  map := splitMap
  map_id A := by
    by_cases h : active A
    · simp [splitMap, h]
    · simpa [splitMap, h] using (inactive_isZero h).eq_of_src 0 (𝟙 (splitObj A))
  map_comp {A B D} f g := by
    by_cases ha : active A <;> by_cases hb : active B <;> by_cases hd : active D <;>
      simp [splitMap, ha, hb, hd]
    have hl : B.left ≤ D.left := leOfHom g.left
    have hr : A.right ≤ B.right := leOfHom f.right
    have hleft : B.left = 0 := le_antisymm (hd.1 ▸ hl) (Fin.zero_le _)
    have hright : B.right ≠ 0 := by
      intro eq
      exact ha.2 (le_antisymm (eq ▸ hr) (Fin.zero_le _))
    exact (hb ⟨hleft, hright⟩).elim

private theorem split_diag_zero (i : Fin 3) : IsZero (splitDiagram.obj (diag i)) := by
  apply inactive_isZero
  rintro ⟨hi, hn⟩
  exact hn hi

private theorem split_isStage : IsStage 2 splitDiagram := by
  refine ⟨split_diag_zero, ?_⟩
  intro i j k hij hjk
  refine ⟨trivial, 0, 0, ?_⟩
  by_cases eq : i = j
  · subst j
    have hv : vert hij hjk = 𝟙 _ := by ext <;> apply Subsingleton.elim
    rw [hv, CategoryTheory.Functor.map_id]
    have hzero : IsIso (0 : splitDiagram.obj (diag i) ⟶ (0 : AddCommGrpCat)) :=
      (split_diag_zero i).isIso (isZero_zero _) _
    exact @IsPushout.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ hzero (by infer_instance)
      ⟨(split_diag_zero i).eq_of_src _ _⟩
  by_cases eq' : j = k
  · subst k
    have hh : horiz hij hjk = 𝟙 _ := by ext <;> apply Subsingleton.elim
    rw [hh, CategoryTheory.Functor.map_id]
    have hzero : IsIso (0 : (0 : AddCommGrpCat) ⟶ splitDiagram.obj (diag j)) :=
      (isZero_zero _).isIso (split_diag_zero j) _
    exact @IsPushout.of_vert_isIso _ _ _ _ _ _ _ _ _ _ (by infer_instance) hzero
      ⟨(split_diag_zero j).eq_of_tgt _ _⟩
  have hi : i = 0 := Fin.ext (by change i.val = 0; omega)
  have hj : j = 1 := Fin.ext (by change j.val = 1; omega)
  have hk : k = 2 := Fin.ext (by change k.val = 2; omega)
  subst i; subst j; subst k
  have hz : IsZero (splitDiagram.obj (interval (1 : Fin 3) 2 hjk)) :=
    inactive_isZero (A := interval (1 : Fin 3) 2 hjk) (by
      change ¬ ((1 : Fin 3) = 0 ∧ (2 : Fin 3) ≠ 0)
      decide)
  have hzero : IsIso (0 : (0 : AddCommGrpCat) ⟶ splitDiagram.obj (interval (1 : Fin 3) 2 hjk)) :=
    (isZero_zero _).isIso hz _
  have hhorizontal : IsIso (splitDiagram.map (horiz hij hjk)) := by
    change IsIso (splitMap (horiz hij hjk))
    have ha : active (interval (0 : Fin 3) 1 hij) := by
      change (0 : Fin 3) = 0 ∧ (1 : Fin 3) ≠ 0
      decide
    have hb : active (interval (0 : Fin 3) 2 (hij.trans hjk)) := by
      change (0 : Fin 3) = 0 ∧ (2 : Fin 3) ≠ 0
      decide
    simp only [splitMap, dite_eq_left (And.intro ha hb)]
    infer_instance
  exact @IsPushout.of_vert_isIso _ _ _ _ _ _ _ _ _ _ hhorizontal hzero ⟨hz.eq_of_tgt _ _⟩

example : ¬ IsZero (splitDiagram.obj (interval (0 : Fin 3) 1 (by decide))) := by
  change ¬ IsZero (AddCommGrpCat.of ℤ)
  intro hz
  have h := hz.eq_of_src (𝟙 (AddCommGrpCat.of ℤ)) 0
  have h1 := congrArg (fun f : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ => f (1 : ℤ)) h
  simp at h1

private theorem split_actualSquare {i j k : Fin 3} (hij : i ≤ j) (hjk : j ≤ k) :
    IsPushout (splitDiagram.map (horiz hij hjk)) (splitDiagram.map (toDiag hij))
      (splitDiagram.map (vert hij hjk)) (splitDiagram.map (fromDiag hjk)) :=
  isPushout_actualSquare split_isStage hij hjk

-- Exercise the three actual interval squares without assuming a stage exists.
example : IsPushout
    (splitDiagram.map (horiz (i := 0) (j := 1) (k := 2) (by decide) (by decide)))
    (splitDiagram.map (toDiag (i := 0) (j := 1) (by decide)))
    (splitDiagram.map (vert (i := 0) (j := 1) (k := 2) (by decide) (by decide)))
    (splitDiagram.map (fromDiag (j := 1) (k := 2) (by decide))) :=
  split_actualSquare _ _

example : IsPushout
    (splitDiagram.map (horiz (i := 0) (j := 0) (k := 1) (by decide) (by decide)))
    (splitDiagram.map (toDiag (i := 0) (j := 0) (by decide)))
    (splitDiagram.map (vert (i := 0) (j := 0) (k := 1) (by decide) (by decide)))
    (splitDiagram.map (fromDiag (j := 0) (k := 1) (by decide))) :=
  split_actualSquare _ _

example : IsPushout
    (splitDiagram.map (horiz (i := 0) (j := 1) (k := 1) (by decide) (by decide)))
    (splitDiagram.map (toDiag (i := 0) (j := 1) (by decide)))
    (splitDiagram.map (vert (i := 0) (j := 1) (k := 1) (by decide) (by decide)))
    (splitDiagram.map (fromDiag (j := 1) (k := 1) (by decide))) :=
  split_actualSquare _ _

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.FiniteStageTests
