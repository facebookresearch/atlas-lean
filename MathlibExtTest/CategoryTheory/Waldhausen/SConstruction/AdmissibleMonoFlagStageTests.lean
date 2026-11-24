/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlagStage
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Reindex
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOne
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageTwo

/-!
# Tests for quotient-completed Stages from admissible-mono flags

The tests exercise flags of lengths zero, one, three, and five; the generic
interval exactness and pushout laws; restriction along a monotone simplex
map; and comparison with the existing degree-one and degree-two Stages.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlagStageTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-! Importing the module installs neither a Waldhausen structure nor global
cokernels on the ambient exact category. -/

/--
error: failed to synthesize
  WaldhausenCategoryWithoutGluing C
-/
#guard_msgs (error, substring := true) in
#synth WaldhausenCategoryWithoutGluing C

/--
error: failed to synthesize
  HasCokernels C
-/
#guard_msgs (error, substring := true) in
#synth HasCokernels C

local instance : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- The empty zero-based flag. -/
def flagZero : AdmissibleMonoFlag C 0 where
  chain := ComposableArrows.mk₀ (0 : C)
  first_isZero := isZero_zero C
  step_admissible i hi := by omega

/-- The basic zero-to-object flag. -/
def flagOne (X : C) : AdmissibleMonoFlag C 1 where
  chain := ComposableArrows.mk₁ (0 : (0 : C) ⟶ X)
  first_isZero := isZero_zero C
  step_admissible i hi := by
    have hi0 : i = 0 := by omega
    subst i
    exact IsAdmissibleMono.fromZero _

/-- A length-three split flag, used to exercise several successive row
pushouts. -/
def flagThree (X : C) : AdmissibleMonoFlag C 3 where
  chain := ComposableArrows.mk₃ (0 : (0 : C) ⟶ X) (𝟙 X) (𝟙 X)
  first_isZero := isZero_zero C
  step_admissible i hi := by
    have hi012 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi012 with rfl | rfl | rfl
    · exact IsAdmissibleMono.fromZero _
    · exact IsAdmissibleMono.id _
    · exact IsAdmissibleMono.id _

/-- A length-five split flag, used as a recursion/performance regression. -/
def flagFive (X : C) : AdmissibleMonoFlag C 5 where
  chain := ComposableArrows.mk₅ (0 : (0 : C) ⟶ X)
    (𝟙 X) (𝟙 X) (𝟙 X) (𝟙 X)
  first_isZero := isZero_zero C
  step_admissible i hi := by
    have hi01234 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi01234 with rfl | rfl | rfl | rfl | rfl
    · exact IsAdmissibleMono.fromZero _
    · exact IsAdmissibleMono.id _
    · exact IsAdmissibleMono.id _
    · exact IsAdmissibleMono.id _
    · exact IsAdmissibleMono.id _

/-- A genuinely nontrivial split flag `0 ⟶ X ⟶ X ⊞ Y`. -/
def splitFlagTwo (X Y : C) : AdmissibleMonoFlag C 2 where
  chain := ComposableArrows.mk₂ (0 : (0 : C) ⟶ X)
    (biprod.inl : X ⟶ X ⊞ Y)
  first_isZero := isZero_zero C
  step_admissible i hi := by
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · exact IsAdmissibleMono.fromZero _
    · exact isAdmissibleMono_f (isAdmissibleExact_split X Y)

/-- An admissible exact sequence gives a zero-based length-two flag. -/
def flagTwoOfExact {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : f ≫ g = 0) (h : IsAdmissibleExact (ShortComplex.mk f g w)) :
    AdmissibleMonoFlag C 2 where
  chain := ComposableArrows.mk₂ (0 : (0 : C) ⟶ X) f
  first_isZero := isZero_zero C
  step_admissible i hi := by
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · exact IsAdmissibleMono.fromZero _
    · exact isAdmissibleMono_f h

/-! The construction works at all requested finite lengths. -/

example : Stage C 0 := flagZero.toStage

example (X : C) : Stage C 1 := (flagOne X).toStage

example (X : C) : Stage C 3 := (flagThree X).toStage

example (X : C) : Stage C 5 := (flagFive X).toStage

example (X Y : C) : Stage C 2 := (splitFlagTwo X Y).toStage

noncomputable example (X Y : C) :
    (splitFlagTwo X Y).intervalQuotient (1 : Fin 3) 2 (by decide) ≅ Y :=
  (splitFlagTwo X Y).intervalIsoOfExact (by decide)
    (biprod.snd : X ⊞ Y ⟶ Y)
    (by
      change (biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.snd = 0
      exact biprod.inl_snd)
    (by
      change IsAdmissibleExact
        (ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) biprod.snd _)
      exact isAdmissibleExact_split X Y)

/-! Public cell, leg, pushout, and exactness laws. -/

example (X : C) {i j : Fin 4} (hij : i ≤ j) :
    IsAdmissibleExact
      (ShortComplex.mk ((flagThree X).chain.map (homOfLE hij))
        ((flagThree X).intervalπ i j hij)
        ((flagThree X).interval_comp_π i j hij)) :=
  (flagThree X).interval_exact i j hij

example (X : C) {i j k : Fin 4} (hij : i ≤ j) (hjk : j ≤ k) :
    IsPushout
      ((flagThree X).intervalπ i j hij)
      ((flagThree X).chain.map (homOfLE hjk))
      ((flagThree X).intervalMap hij (hij.trans hjk) le_rfl hjk)
      ((flagThree X).intervalπ i k (hij.trans hjk)) :=
  (flagThree X).intervalSquare_isPushout hij hjk

example (X : C) {i j k : Fin 6} (hij : i ≤ j) (hjk : j ≤ k) :
    IsAdmissibleExact
      (ShortComplex.mk
        ((flagFive X).intervalMap hij (hij.trans hjk) le_rfl hjk)
        ((flagFive X).intervalMap (hij.trans hjk) hjk hij le_rfl)
        ((flagFive X).intervalMap_comp_eq_zero hij hjk)) :=
  (flagFive X).interval_triple_exact hij hjk

example (X : C) {i j k : Fin 4} (hij : i ≤ j) (hjk : j ≤ k) :
    (flagThree X).toStage.obj.map (horiz hij hjk) =
      (flagThree X).intervalMap hij (hij.trans hjk) le_rfl hjk := by
  simp

example (X : C) {i j k : Fin 4} (hij : i ≤ j) (hjk : j ≤ k) :
    (flagThree X).toStage.obj.map (vert hij hjk) =
      (flagThree X).intervalMap (hij.trans hjk) hjk hij le_rfl := by
  simp

/-! Monotone restriction computes by restricting interval endpoints; it does
not assert equality with a separately chosen quotient completion. -/

example {a b : SimplexCategory} (α : a ⟶ b)
    (F : AdmissibleMonoFlag C b.len)
    {i j : Fin (a.len + 1)} (hij : i ≤ j) :
    ((reindexStage (C := C) α).obj F.toStage).obj.obj
        (interval i j hij) =
      F.intervalQuotient (SimplexCategory.Hom.toOrderHom α i)
        (SimplexCategory.Hom.toOrderHom α j)
        ((SimplexCategory.Hom.toOrderHom α).monotone hij) := by
  change F.toStage.obj.obj ((indexFunctor α).obj (interval i j hij)) = _
  rw [indexFunctor_obj_interval]
  rfl

/-! The zero row agrees with the established degree-one Stage. -/

noncomputable example (X : C) :
    ((stageOne C).obj X).obj.obj (interval (0 : Fin 2) 1 (by decide)) ≅
      (flagOne X).toStage.obj.obj (interval 0 1 (by decide)) :=
  eqToIso (stageOne_obj_interval_zero_one C X (by decide)) ≪≫
    (flagOne X).zeroRowIso 1

/-! For an admissible exact sequence, the three cells agree with the
established degree-two Stage; the quotient comparison has the prescribed
projection. -/

section DegreeTwo

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  (w : f ≫ g = 0) (h : IsAdmissibleExact (ShortComplex.mk f g w))

noncomputable example :
    (flagTwoOfExact f g w h).toStage.obj.obj
        (interval (0 : Fin 3) 1 (by decide)) ≅
      (stageTwo C X Y Z f g
        (ExactCategory.isCofibrationSequence_of_isAdmissibleExact h)).obj.obj
          (interval 0 1 (by decide)) :=
  ((flagTwoOfExact f g w h).zeroRowIso 1).symm ≪≫
    eqToIso (stageTwo_obj_01 C X Y Z f g
      (ExactCategory.isCofibrationSequence_of_isAdmissibleExact h) (by decide)).symm

noncomputable example :
    (flagTwoOfExact f g w h).toStage.obj.obj
        (interval (0 : Fin 3) 2 (by decide)) ≅
      (stageTwo C X Y Z f g
        (ExactCategory.isCofibrationSequence_of_isAdmissibleExact h)).obj.obj
          (interval 0 2 (by decide)) :=
  ((flagTwoOfExact f g w h).zeroRowIso 2).symm ≪≫
    eqToIso (stageTwo_obj_02 C X Y Z f g
      (ExactCategory.isCofibrationSequence_of_isAdmissibleExact h) (by decide)).symm

noncomputable example :
    (flagTwoOfExact f g w h).toStage.obj.obj
        (interval (1 : Fin 3) 2 (by decide)) ≅
      (stageTwo C X Y Z f g
        (ExactCategory.isCofibrationSequence_of_isAdmissibleExact h)).obj.obj
          (interval 1 2 (by decide)) :=
  (flagTwoOfExact f g w h).intervalIsoOfExact (by decide) g
      (by
        change f ≫ g = 0
        exact w)
      (by
        change IsAdmissibleExact (ShortComplex.mk f g _)
        exact h) ≪≫
    eqToIso (stageTwo_obj_12 C X Y Z f g
      (ExactCategory.isCofibrationSequence_of_isAdmissibleExact h) (by decide)).symm

example :
    (flagTwoOfExact f g w h).intervalπ (1 : Fin 3) 2 (by decide) ≫
        ((flagTwoOfExact f g w h).intervalIsoOfExact
          (by decide) g
          (by
            change f ≫ g = 0
            exact w)
          (by
            change IsAdmissibleExact (ShortComplex.mk f g _)
            exact h)).hom = g := by
  exact (flagTwoOfExact f g w h).intervalπ_intervalIsoOfExact_hom
    (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) g
    (by
      change f ≫ g = 0
      exact w)
    (by
      change IsAdmissibleExact (ShortComplex.mk f g _)
      exact h)

end DegreeTwo

/-! Universe-polymorphic client checks. -/

section UniverseZero

variable {C₀ : Type} [Category C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

example (X : C₀) :
    letI : WaldhausenCategoryWithoutGluing C₀ := ExactCategory.waldhausenCategory C₀
    Stage C₀ 3 := (flagThree X).toStage

end UniverseZero

section UniverseOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

example (X : C₁) :
    letI : WaldhausenCategoryWithoutGluing C₁ := ExactCategory.waldhausenCategory C₁
    Stage C₁ 5 := (flagFive X).toStage

end UniverseOne

/-! The module deliberately installs no ambient limits or selector functor. -/

/--
error: failed to synthesize
  HasPushouts C
-/
#guard_msgs (error, substring := true) in
#synth HasPushouts C

/--
error: Unknown constant `CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag.toStageFunctor`
-/
#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag.toStageFunctor

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlagStageTests

end
