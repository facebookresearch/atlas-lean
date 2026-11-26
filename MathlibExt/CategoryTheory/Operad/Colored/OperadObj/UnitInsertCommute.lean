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

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.UnitLaws
public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Hom
public import MathlibExt.CategoryTheory.Operad.OperadObj.UnitInsertionNaturality
public import MathlibExt.CategoryTheory.Operad.Colored.SubstitutionUnit

/-!
# Unit-insert commutation with collection maps

For a collection map `α : O ⟶ P` preserving the operadic units, the
right- and left-unit insertions commute with `α`: applying `α` before
inserting equals inserting before `HomData.sourceHom α`.

## Informal proof

Unfold the insertions, use insertion-prefix naturality, and check the
residual family equation from the factor-hom definitions: the singleton
block by `singletonIso` naturality plus `α.naturality`, the unit blocks
by the unit-preservation hypothesis.

These commutation lemmas discharge the unit-insert steps of the algebra
unit laws with `α := A.a`: the unit-preservation premise is then
definitionally the induced-unit equation
(`(freeOperadObj A.A).unit c ≫ A.a.app _`). Note the direction matters:
`α := freeUnit.app _` would demand `unit ≫ A.a ≫ freeUnit = unit`,
which is not an algebra law (only `freeUnit ≫ A.a = 𝟙` holds).
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe w v u

namespace ColoredOperadObj

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

/-- Family equation behind right-insert naturality: the pushed-forward
nested map followed by the codomain factor hom equals the domain factor
hom followed by the factorwise collection map. -/
private theorem rightNestedMap_factorHom {O P : ColoredSymmetricCollection Color V}
    {ηO : ColoredOperadUnit O} {ηP : ColoredOperadUnit P} (α : O ⟶ P)
    (hη : ∀ c, ηO c ≫ α.app (ColoredSubstitutionData.unitProfile c) = ηP c)
    (Q : ColoredProfile Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
          (CategoryTheory.Operad.UnitInsertion.rightNestedFamilyMap (α.app Q)
            Q.inputs) ≫
        UnitInsertion.rightFactorHom P ηP Q =
      UnitInsertion.rightFactorHom O ηO Q ≫
        HomData.factorHom α (ColoredSubstitutionData.rightUnit Q) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
        refine heq_of_eq ?_
        have nat1 :=
          (FiniteTensor.singletonIso (V := V)).hom.naturality (α.app Q)
        have nat2 :=
          α.naturality (ColoredSubstitutionData.rightUnitOuterHom Q)
        change (FiniteTensor.tensor (V := V)).map
                ((FiniteFamily.singleton (C := V)).map (α.app Q)) ≫
              ((FiniteTensor.singletonIso (V := V)).hom.app (P.obj Q) ≫
                P.map (ColoredSubstitutionData.rightUnitOuterHom Q)) =
            ((FiniteTensor.singletonIso (V := V)).hom.app (O.obj Q) ≫
                O.map (ColoredSubstitutionData.rightUnitOuterHom Q)) ≫
              α.app ((ColoredSubstitutionData.rightUnit Q).outerProfile)
        calc (FiniteTensor.tensor (V := V)).map
                  ((FiniteFamily.singleton (C := V)).map (α.app Q)) ≫
                ((FiniteTensor.singletonIso (V := V)).hom.app (P.obj Q) ≫
                  P.map (ColoredSubstitutionData.rightUnitOuterHom Q))
            = ((FiniteTensor.tensor (V := V)).map
                  ((FiniteFamily.singleton (C := V)).map (α.app Q)) ≫
                (FiniteTensor.singletonIso (V := V)).hom.app
                  (P.obj Q)) ≫
              P.map (ColoredSubstitutionData.rightUnitOuterHom Q) :=
              (Category.assoc _ _ _).symm
          _ = ((FiniteTensor.singletonIso (V := V)).hom.app (O.obj Q) ≫
                α.app Q) ≫
              P.map (ColoredSubstitutionData.rightUnitOuterHom Q) :=
              congrArg
                (fun m =>
                  m ≫ P.map (ColoredSubstitutionData.rightUnitOuterHom Q))
                nat1
          _ = (FiniteTensor.singletonIso (V := V)).hom.app (O.obj Q) ≫
              (α.app Q ≫
                P.map (ColoredSubstitutionData.rightUnitOuterHom Q)) :=
              Category.assoc _ _ _
          _ = (FiniteTensor.singletonIso (V := V)).hom.app (O.obj Q) ≫
              (O.map (ColoredSubstitutionData.rightUnitOuterHom Q) ≫
                α.app
                  ((ColoredSubstitutionData.rightUnit Q).outerProfile)) :=
              congrArg
                (fun m =>
                  (FiniteTensor.singletonIso (V := V)).hom.app (O.obj Q) ≫
                    m)
                nat2.symm
          _ = ((FiniteTensor.singletonIso (V := V)).hom.app (O.obj Q) ≫
                O.map (ColoredSubstitutionData.rightUnitOuterHom Q)) ≫
              α.app ((ColoredSubstitutionData.rightUnit Q).outerProfile) :=
              (Category.assoc _ _ _).symm
    | some i =>
        refine heq_of_eq ?_
        change (FiniteTensor.tensor (V := V)).map
                (𝟙 FiniteFamily.empty) ≫
              ηP (Q.inputColor i) =
            ηO (Q.inputColor i) ≫
              α.app
                (ColoredSubstitutionData.unitProfile (Q.inputColor i))
        have e1 : (FiniteTensor.tensor (V := V)).map
              (𝟙 FiniteFamily.empty) ≫
            ηP (Q.inputColor i) = ηP (Q.inputColor i) :=
          (congrArg (fun m => m ≫ ηP (Q.inputColor i))
            (Functor.map_id _ _)).trans (Category.id_comp _)
        exact e1.trans (hη (Q.inputColor i)).symm

/-- Family equation behind left-insert naturality: the pushed-forward
nested map followed by the codomain factor hom equals the domain factor
hom followed by the factorwise collection map. -/
private theorem leftNestedMap_factorHom {O P : ColoredSymmetricCollection Color V}
    {ηO : ColoredOperadUnit O} {ηP : ColoredOperadUnit P} (α : O ⟶ P)
    (hη : ∀ c, ηO c ≫ α.app (ColoredSubstitutionData.unitProfile c) = ηP c)
    (Q : ColoredProfile Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
          (CategoryTheory.Operad.UnitInsertion.leftNestedFamilyMap
            (α.app Q)) ≫
        UnitInsertion.leftFactorHom P ηP Q =
      UnitInsertion.leftFactorHom O ηO Q ≫
        HomData.factorHom α (ColoredSubstitutionData.leftUnit Q) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
        refine heq_of_eq ?_
        have nat :=
          α.naturality (ColoredSubstitutionData.leftUnitOuterHom Q)
        have hηc := hη Q.outputColor
        change (FiniteTensor.tensor (V := V)).map
                (𝟙 FiniteFamily.empty) ≫
              (ηP Q.outputColor ≫
                P.map (ColoredSubstitutionData.leftUnitOuterHom Q)) =
            (ηO Q.outputColor ≫
                O.map (ColoredSubstitutionData.leftUnitOuterHom Q)) ≫
              α.app ((ColoredSubstitutionData.leftUnit Q).outerProfile)
        have e1 : (FiniteTensor.tensor (V := V)).map
              (𝟙 FiniteFamily.empty) ≫
            (ηP Q.outputColor ≫
              P.map (ColoredSubstitutionData.leftUnitOuterHom Q)) =
            ηP Q.outputColor ≫
              P.map (ColoredSubstitutionData.leftUnitOuterHom Q) :=
          (congrArg
            (fun m =>
              m ≫
                (ηP Q.outputColor ≫
                  P.map (ColoredSubstitutionData.leftUnitOuterHom Q)))
            (Functor.map_id _ _)).trans (Category.id_comp _)
        have e2 : (ηP Q.outputColor ≫
              P.map (ColoredSubstitutionData.leftUnitOuterHom Q)) =
            (ηO Q.outputColor ≫
                α.app
                  (ColoredSubstitutionData.unitProfile Q.outputColor)) ≫
              P.map (ColoredSubstitutionData.leftUnitOuterHom Q) :=
          congrArg
            (fun m =>
              m ≫ P.map (ColoredSubstitutionData.leftUnitOuterHom Q))
            hηc.symm
        have e3 : (ηO Q.outputColor ≫
              α.app (ColoredSubstitutionData.unitProfile Q.outputColor)) ≫
            P.map (ColoredSubstitutionData.leftUnitOuterHom Q) =
            ηO Q.outputColor ≫
              (α.app
                  (ColoredSubstitutionData.unitProfile Q.outputColor) ≫
                P.map (ColoredSubstitutionData.leftUnitOuterHom Q)) :=
          Category.assoc _ _ _
        have e4 : ηO Q.outputColor ≫
              (α.app
                  (ColoredSubstitutionData.unitProfile Q.outputColor) ≫
                P.map (ColoredSubstitutionData.leftUnitOuterHom Q)) =
            ηO Q.outputColor ≫
              (O.map (ColoredSubstitutionData.leftUnitOuterHom Q) ≫
                α.app
                  ((ColoredSubstitutionData.leftUnit Q).outerProfile)) :=
          congrArg (fun m => ηO Q.outputColor ≫ m) nat.symm
        have e5 : ηO Q.outputColor ≫
              (O.map (ColoredSubstitutionData.leftUnitOuterHom Q) ≫
                α.app
                  ((ColoredSubstitutionData.leftUnit Q).outerProfile)) =
            (ηO Q.outputColor ≫
                O.map (ColoredSubstitutionData.leftUnitOuterHom Q)) ≫
              α.app ((ColoredSubstitutionData.leftUnit Q).outerProfile) :=
          (Category.assoc _ _ _).symm
        exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
    | some u =>
        refine heq_of_eq ?_
        have nat1 :=
          (FiniteTensor.singletonIso (V := V)).hom.naturality (α.app Q)
        change (FiniteTensor.tensor (V := V)).map
                ((FiniteFamily.singleton (C := V)).map (α.app Q)) ≫
              (FiniteTensor.singletonIso (V := V)).hom.app (P.obj Q) =
            (FiniteTensor.singletonIso (V := V)).hom.app (O.obj Q) ≫
              α.app Q
        exact nat1

/-- Right-unit insertion is natural in the collection map for
unit-preserving maps: applying `α` before inserting equals inserting
before `HomData.sourceHom α`. -/
theorem rightUnitInsert_naturality {O P : ColoredSymmetricCollection Color V}
    {ηO : ColoredOperadUnit O} {ηP : ColoredOperadUnit P} (α : O ⟶ P)
    (hη : ∀ c, ηO c ≫ α.app (ColoredSubstitutionData.unitProfile c) = ηP c)
    (Q : ColoredProfile Color) :
    α.app Q ≫ rightUnitInsert P ηP Q =
      rightUnitInsert O ηO Q ≫
        HomData.sourceHom α (ColoredSubstitutionData.rightUnit Q) := by
  have hPre :=
    CategoryTheory.Operad.UnitInsertion.rightInsertPrefix_natural (α.app Q)
      Q.inputs
  have hFamR := rightNestedMap_factorHom α hη Q
  have hMap : (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
            (CategoryTheory.Operad.UnitInsertion.rightNestedFamilyMap
              (α.app Q) Q.inputs)) ≫
        (FiniteTensor.tensor (V := V)).map
          (UnitInsertion.rightFactorHom P ηP Q) =
        (FiniteTensor.tensor (V := V)).map
          (UnitInsertion.rightFactorHom O ηO Q) ≫
        (FiniteTensor.tensor (V := V)).map
          (HomData.factorHom α
            (ColoredSubstitutionData.rightUnit Q)) :=
    (Functor.map_comp _ _ _).symm.trans
      ((congrArg (FiniteTensor.tensor (V := V)).map hFamR).trans
        (Functor.map_comp _ _ _))
  change α.app Q ≫
        (CategoryTheory.Operad.UnitInsertion.rightInsertPrefix (P.obj Q)
            Q.inputs ≫
          (FiniteTensor.tensor (V := V)).map
            (UnitInsertion.rightFactorHom P ηP Q)) =
      (CategoryTheory.Operad.UnitInsertion.rightInsertPrefix (O.obj Q)
          Q.inputs ≫
        (FiniteTensor.tensor (V := V)).map
          (UnitInsertion.rightFactorHom O ηO Q)) ≫
        (FiniteTensor.tensor (V := V)).map
          (HomData.factorHom α (ColoredSubstitutionData.rightUnit Q))
  calc α.app Q ≫
          (CategoryTheory.Operad.UnitInsertion.rightInsertPrefix (P.obj Q)
              Q.inputs ≫
            (FiniteTensor.tensor (V := V)).map
              (UnitInsertion.rightFactorHom P ηP Q))
        = (α.app Q ≫
            CategoryTheory.Operad.UnitInsertion.rightInsertPrefix (P.obj Q)
              Q.inputs) ≫
          (FiniteTensor.tensor (V := V)).map
            (UnitInsertion.rightFactorHom P ηP Q) :=
          (Category.assoc _ _ _).symm
      _ = (CategoryTheory.Operad.UnitInsertion.rightInsertPrefix (O.obj Q)
              Q.inputs ≫
            (FiniteTensor.tensor (V := V)).map
              ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
                (CategoryTheory.Operad.UnitInsertion.rightNestedFamilyMap
                  (α.app Q) Q.inputs))) ≫
          (FiniteTensor.tensor (V := V)).map
            (UnitInsertion.rightFactorHom P ηP Q) :=
          congrArg
            (fun m =>
              m ≫
                (FiniteTensor.tensor (V := V)).map
                  (UnitInsertion.rightFactorHom P ηP Q))
            hPre
      _ = CategoryTheory.Operad.UnitInsertion.rightInsertPrefix (O.obj Q)
            Q.inputs ≫
          ((FiniteTensor.tensor (V := V)).map
              ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
                (CategoryTheory.Operad.UnitInsertion.rightNestedFamilyMap
                  (α.app Q) Q.inputs)) ≫
            (FiniteTensor.tensor (V := V)).map
              (UnitInsertion.rightFactorHom P ηP Q)) :=
          Category.assoc _ _ _
      _ = CategoryTheory.Operad.UnitInsertion.rightInsertPrefix (O.obj Q)
            Q.inputs ≫
          ((FiniteTensor.tensor (V := V)).map
              (UnitInsertion.rightFactorHom O ηO Q) ≫
            (FiniteTensor.tensor (V := V)).map
              (HomData.factorHom α
                (ColoredSubstitutionData.rightUnit Q))) :=
          congrArg
            (fun m =>
              CategoryTheory.Operad.UnitInsertion.rightInsertPrefix (O.obj Q)
                Q.inputs ≫ m)
            hMap
      _ = (CategoryTheory.Operad.UnitInsertion.rightInsertPrefix (O.obj Q)
              Q.inputs ≫
            (FiniteTensor.tensor (V := V)).map
              (UnitInsertion.rightFactorHom O ηO Q)) ≫
          (FiniteTensor.tensor (V := V)).map
            (HomData.factorHom α (ColoredSubstitutionData.rightUnit Q)) :=
          (Category.assoc _ _ _).symm

/-- Left-unit insertion is natural in the collection map for
unit-preserving maps: applying `α` before inserting equals inserting
before `HomData.sourceHom α`. -/
theorem leftUnitInsert_naturality {O P : ColoredSymmetricCollection Color V}
    {ηO : ColoredOperadUnit O} {ηP : ColoredOperadUnit P} (α : O ⟶ P)
    (hη : ∀ c, ηO c ≫ α.app (ColoredSubstitutionData.unitProfile c) = ηP c)
    (Q : ColoredProfile Color) :
    α.app Q ≫ leftUnitInsert P ηP Q =
      leftUnitInsert O ηO Q ≫
        HomData.sourceHom α (ColoredSubstitutionData.leftUnit Q) := by
  have hPre :=
    CategoryTheory.Operad.UnitInsertion.leftInsertPrefix_natural (α.app Q)
  have hFamL := leftNestedMap_factorHom α hη Q
  have hMap : (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
            (CategoryTheory.Operad.UnitInsertion.leftNestedFamilyMap
              (α.app Q))) ≫
        (FiniteTensor.tensor (V := V)).map
          (UnitInsertion.leftFactorHom P ηP Q) =
        (FiniteTensor.tensor (V := V)).map
          (UnitInsertion.leftFactorHom O ηO Q) ≫
        (FiniteTensor.tensor (V := V)).map
          (HomData.factorHom α
            (ColoredSubstitutionData.leftUnit Q)) :=
    (Functor.map_comp _ _ _).symm.trans
      ((congrArg (FiniteTensor.tensor (V := V)).map hFamL).trans
        (Functor.map_comp _ _ _))
  change α.app Q ≫
        (CategoryTheory.Operad.UnitInsertion.leftInsertPrefix (P.obj Q) ≫
          (FiniteTensor.tensor (V := V)).map
            (UnitInsertion.leftFactorHom P ηP Q)) =
      (CategoryTheory.Operad.UnitInsertion.leftInsertPrefix (O.obj Q) ≫
        (FiniteTensor.tensor (V := V)).map
          (UnitInsertion.leftFactorHom O ηO Q)) ≫
        (FiniteTensor.tensor (V := V)).map
          (HomData.factorHom α (ColoredSubstitutionData.leftUnit Q))
  calc α.app Q ≫
          (CategoryTheory.Operad.UnitInsertion.leftInsertPrefix
              (P.obj Q) ≫
            (FiniteTensor.tensor (V := V)).map
              (UnitInsertion.leftFactorHom P ηP Q))
        = (α.app Q ≫
            CategoryTheory.Operad.UnitInsertion.leftInsertPrefix
              (P.obj Q)) ≫
          (FiniteTensor.tensor (V := V)).map
            (UnitInsertion.leftFactorHom P ηP Q) :=
          (Category.assoc _ _ _).symm
      _ = (CategoryTheory.Operad.UnitInsertion.leftInsertPrefix
              (O.obj Q) ≫
            (FiniteTensor.tensor (V := V)).map
              ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
                (CategoryTheory.Operad.UnitInsertion.leftNestedFamilyMap
                  (α.app Q)))) ≫
          (FiniteTensor.tensor (V := V)).map
            (UnitInsertion.leftFactorHom P ηP Q) :=
          congrArg
            (fun m =>
              m ≫
                (FiniteTensor.tensor (V := V)).map
                  (UnitInsertion.leftFactorHom P ηP Q))
            hPre
      _ = CategoryTheory.Operad.UnitInsertion.leftInsertPrefix (O.obj Q) ≫
          ((FiniteTensor.tensor (V := V)).map
              ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map
                (CategoryTheory.Operad.UnitInsertion.leftNestedFamilyMap
                  (α.app Q))) ≫
            (FiniteTensor.tensor (V := V)).map
              (UnitInsertion.leftFactorHom P ηP Q)) :=
          Category.assoc _ _ _
      _ = CategoryTheory.Operad.UnitInsertion.leftInsertPrefix (O.obj Q) ≫
          ((FiniteTensor.tensor (V := V)).map
              (UnitInsertion.leftFactorHom O ηO Q) ≫
            (FiniteTensor.tensor (V := V)).map
              (HomData.factorHom α
                (ColoredSubstitutionData.leftUnit Q))) :=
          congrArg
            (fun m =>
              CategoryTheory.Operad.UnitInsertion.leftInsertPrefix
                (O.obj Q) ≫ m)
            hMap
      _ = (CategoryTheory.Operad.UnitInsertion.leftInsertPrefix (O.obj Q) ≫
            (FiniteTensor.tensor (V := V)).map
              (UnitInsertion.leftFactorHom O ηO Q)) ≫
          (FiniteTensor.tensor (V := V)).map
            (HomData.factorHom α (ColoredSubstitutionData.leftUnit Q)) :=
          (Category.assoc _ _ _).symm

end ColoredOperadObj

end CategoryTheory.Operad
