/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Monoidal.Sequence.Day

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped ExternalProduct MonoidalCategory

namespace CategoryTheory.SequenceDayTests

universe v u

#check @Sequence
#check @Sequence.evaluation
#check @Sequence.freeAt
#check @Sequence.freeAtEvaluationAdjunction
#check @Sequence.tensorObjIso
#check @Sequence.tensorObjIso_η
#check @Sequence.tensorUnitZeroIso
#check @Sequence.tensorUnitSuccIso

#check @Sequence.{0, 0}
#check @Sequence.{1, 1}
#check @Sequence.{0, 1}
#check @Sequence.{1, 0}
#check @Sequence.tensorObjIso.{0, 0}
#check @Sequence.tensorObjIso.{1, 1}
#check @Sequence.tensorObjIso.{0, 1}
#check @Sequence.tensorObjIso.{1, 0}
#check @Sequence.evaluation.{0, 0}
#check @Sequence.evaluation.{1, 1}
#check @Sequence.evaluation.{0, 1}
#check @Sequence.evaluation.{1, 0}
#check @Sequence.freeAt.{0, 0}
#check @Sequence.freeAt.{1, 1}
#check @Sequence.freeAt.{0, 1}
#check @Sequence.freeAt.{1, 0}
#check @Sequence.freeAtEvaluationAdjunction.{0, 0}
#check @Sequence.freeAtEvaluationAdjunction.{1, 1}
#check @Sequence.freeAtEvaluationAdjunction.{0, 1}
#check @Sequence.freeAtEvaluationAdjunction.{1, 0}
#check @Sequence.tensorObjIso_η.{0, 0}
#check @Sequence.tensorObjIso_η.{1, 1}
#check @Sequence.tensorObjIso_η.{0, 1}
#check @Sequence.tensorObjIso_η.{1, 0}
#check @Sequence.tensorUnitZeroIso.{0, 0}
#check @Sequence.tensorUnitZeroIso.{1, 1}
#check @Sequence.tensorUnitZeroIso.{0, 1}
#check @Sequence.tensorUnitZeroIso.{1, 0}
#check @Sequence.tensorUnitSuccIso.{0, 0}
#check @Sequence.tensorUnitSuccIso.{1, 1}
#check @Sequence.tensorUnitSuccIso.{0, 1}
#check @Sequence.tensorUnitSuccIso.{1, 0}

section Evaluation

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
variable [∀ i j : Sequence.Index, HasCoproductsOfShape (i ⟶ j) V]
variable (A : V) (X : Sequence V) (n : ℕ)

example : V ⥤ Sequence V := Sequence.freeAt V n
example : Sequence V ⥤ V := Sequence.evaluation V n

example :
    (Sequence.freeAt V n).map
        ((Sequence.freeAtEvaluationAdjunction V n).unit.app A) ≫
      (Sequence.freeAtEvaluationAdjunction V n).counit.app
        ((Sequence.freeAt V n).obj A) =
      𝟙 ((Sequence.freeAt V n).obj A) :=
  (Sequence.freeAtEvaluationAdjunction V n).left_triangle_components A

example :
    (Sequence.freeAtEvaluationAdjunction V n).unit.app
        ((Sequence.evaluation V n).obj X) ≫
      (Sequence.evaluation V n).map
        ((Sequence.freeAtEvaluationAdjunction V n).counit.app X) =
      𝟙 ((Sequence.evaluation V n).obj X) :=
  (Sequence.freeAtEvaluationAdjunction V n).right_triangle_components X

end Evaluation

section Day

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
variable
  [∀ (F G : Sequence.Index ⥤ V),
    (tensor Sequence.Index).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ Sequence.Index)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (W : V) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow (tensor Sequence.Index) d) (tensorLeft W)]
  [∀ (W : V) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow (tensor Sequence.Index) d) (tensorRight W)]
  [∀ (W : V) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        (Functor.fromPUnit.{0} (𝟙_ Sequence.Index)) d) (tensorLeft W)]
  [∀ (W : V) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        (Functor.fromPUnit.{0} (𝟙_ Sequence.Index)) d) (tensorRight W)]
  [∀ (W : V) (d : Sequence.Index × Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        ((𝟭 Sequence.Index).prod
          (Functor.fromPUnit.{0} (𝟙_ Sequence.Index))) d)
      (tensorRight W)]
  [∀ (W : V) (d : Sequence.Index × Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        ((tensor Sequence.Index).prod (𝟭 Sequence.Index)) d)
      (tensorRight W)]
  [∀ n : ℕ, HasCoproductsOfShape (Fin (n + 1)) V]
  [HasInitial V]

variable (X Y : Sequence V) (n : ℕ)

example :
    (X ⊗ Y).functor.obj (Sequence.index n) ≅
      ∐ fun p : Fin (n + 1) =>
        X.functor.obj (Sequence.index (p : ℕ)) ⊗
          Y.functor.obj (Sequence.index (n - (p : ℕ))) :=
  Sequence.tensorObjIso X Y n

example :
    (X ⊗ Y).functor.obj (Sequence.index 0) ≅
      ∐ fun p : Fin 1 =>
        X.functor.obj (Sequence.index (p : ℕ)) ⊗
          Y.functor.obj (Sequence.index (0 - (p : ℕ))) :=
  Sequence.tensorObjIso X Y 0

example :
    (X ⊗ Y).functor.obj (Sequence.index 1) ≅
      ∐ fun p : Fin 2 =>
        X.functor.obj (Sequence.index (p : ℕ)) ⊗
          Y.functor.obj (Sequence.index (1 - (p : ℕ))) :=
  Sequence.tensorObjIso X Y 1

example :
    (X ⊗ Y).functor.obj (Sequence.index 2) ≅
      ∐ fun p : Fin 3 =>
        X.functor.obj (Sequence.index (p : ℕ)) ⊗
          Y.functor.obj (Sequence.index (2 - (p : ℕ))) :=
  Sequence.tensorObjIso X Y 2

example (p : Fin (n + 1)) :
    (DayFunctor.η X Y).app
          (Sequence.index (p : ℕ), Sequence.index (n - (p : ℕ))) ≫
        (X ⊗ Y).functor.map
          (eqToHom
            ((Sequence.tensorObj_index (p : ℕ) (n - (p : ℕ))).trans
              (congrArg Sequence.index
                (Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt))))) ≫
        (Sequence.tensorObjIso X Y n).hom =
      Sigma.ι
        (fun q : Fin (n + 1) =>
          X.functor.obj (Sequence.index (q : ℕ)) ⊗
            Y.functor.obj (Sequence.index (n - (q : ℕ)))) p :=
  Sequence.tensorObjIso_η X Y n p

example :
    (𝟙_ (Sequence V)).functor.obj (Sequence.index 0) ≅ 𝟙_ V :=
  Sequence.tensorUnitZeroIso V

example :
    (𝟙_ (Sequence V)).functor.obj (Sequence.index 1) ≅ ⊥_ V :=
  Sequence.tensorUnitSuccIso V 0

example :
    (𝟙_ (Sequence V)).functor.obj (Sequence.index 2) ≅ ⊥_ V :=
  Sequence.tensorUnitSuccIso V 1

example (_p : Fin (n + 1)) : True := by
  fail_if_success
    exact (show
      (DayFunctor.η X Y).app
            (Sequence.index (_p : ℕ), Sequence.index (n - (_p : ℕ))) ≫
          (X ⊗ Y).functor.map
            (eqToHom
              ((Sequence.tensorObj_index (_p : ℕ) (n - (_p : ℕ))).trans
                (congrArg Sequence.index
                  (Nat.add_sub_of_le (Nat.le_of_lt_succ _p.isLt))))) ≫
          (Sequence.tensorObjIso X Y n).inv =
        Sigma.ι
          (fun q : Fin (n + 1) =>
            X.functor.obj (Sequence.index (q : ℕ)) ⊗
              Y.functor.obj (Sequence.index (n - (q : ℕ)))) _p from
      Sequence.tensorObjIso_η X Y n _p)
  trivial

end Day

#print axioms Sequence.evaluation
#print axioms Sequence.freeAt
#print axioms Sequence.freeAtEvaluationAdjunction
#print axioms Sequence.tensorObjIso
#print axioms Sequence.tensorObjIso_η
#print axioms Sequence.tensorUnitZeroIso
#print axioms Sequence.tensorUnitSuccIso

end CategoryTheory.SequenceDayTests
