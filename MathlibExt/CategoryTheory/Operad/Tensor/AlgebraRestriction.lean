/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Operad.Tensor.FreeAlgebraConstruction
public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Hom

/-!
# Restriction of tensor operadic algebras

Restriction along an actual colored operad morphism keeps the original
carrier and precomposes every tensor operation with the original coefficient
map. Its unit, substitution and algebra-morphism laws use the same maps.

This focused API is extracted without changing its declarations from
`MathlibExt/CategoryTheory/Operad/Tensor/LaxAlgebraTransport.lean`. The source
and integration correspondence is recorded in
`docs/spectra/integration/a5-lax-profile-operad.md`.
-/

@[expose] public section
set_option autoImplicit false

namespace CategoryTheory.Operad.Tensor

open CategoryTheory

universe uColor u₁ v₁

variable {W : Type uColor} {C : Type u₁} [Category.{v₁} C] [FiniteTensor C]

namespace Restriction

variable {O P : ColoredOperadObj W C}

/-- Restrict every original tensor operation along the original operad coefficient map. -/
def operations (f : O ⟶ P) {A B : W → C} (a : Operations P.toCollection A B) :
    Operations O.toCollection A B where
  app d q := (analyticSummandCollectionMap A f.toCollectionHom).app q ≫ a.app d q
  equivariance d q r e := by
    rw [← Category.assoc, (analyticSummandCollectionMap A f.toCollectionHom).naturality e,
      Category.assoc, a.equivariance d e]

private theorem unitFactors_comp (f : O ⟶ P) (A : W → C) (d : W) :
    unitFactors O A d ≫
        (analyticFactorsCollectionMap A f.toCollectionHom).app (AnalyticIndex.unary d) =
      unitFactors P A d := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      with_unfolding_all exact heq_of_eq (f.map_unit d)
    | some i =>
      with_unfolding_all exact heq_of_eq (Category.comp_id _)

/-- Restriction retains the original unit insertion and the original unit coefficient equation. -/
theorem unitInsertion_comp (f : O ⟶ P) (A : W → C) (d : W) :
    unitInsertion O A d ≫
        (analyticSummandCollectionMap A f.toCollectionHom).app (AnalyticIndex.unary d) =
      unitInsertion P A d := by
  change UnitInsertion.leftInsertFromFactor (A d) (unitFactors O A d) ≫
      (FiniteTensor.tensor (V := C)).map
        ((analyticFactorsCollectionMap A f.toCollectionHom).app (AnalyticIndex.unary d)) =
    UnitInsertion.leftInsertFromFactor (A d) (unitFactors P A d)
  rw [UnitInsertion.leftInsertFromFactor_comp, unitFactors_comp]

/-- Map the original coefficient of every inner-first substitution block. -/
def nestedMap (f : O ⟶ P) (A : W → C) (s : ColoredSubstitutionData W) :
    nestedOperationFactors O.toCollection A s ⟶ nestedOperationFactors P.toCollection A s where
  equiv := Equiv.refl _
  hom i := match i with
    | none => (FiniteFamily.singleton (C := C)).map (f.toCollectionHom.app s.outerProfile)
    | some i => (analyticFactorsCollectionMap A f.toCollectionHom).app (profileInputs
      (s.inner.obj i))

/-- Map all original coefficients in the coefficient-first block and retain all leaf inputs. -/
def inputMap (f : O ⟶ P) (A : W → C) (s : ColoredSubstitutionData W) :
    substitutionInputFactors O.toCollection A s ⟶ substitutionInputFactors P.toCollection A s where
  equiv := Equiv.refl _
  hom i := match i with
    | none => ColoredOperadObj.HomData.factorHom f.toCollectionHom s
    | some i => (FiniteFamily.singleton (C := C)).map (𝟙 (A (s.totalProfile.inputColor i)))

private theorem innerMap_comp (f : O ⟶ P) {A : W → C}
    (a : Operations P.toCollection A A) (s : ColoredSubstitutionData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (nestedMap f A s) ≫
        innerOperationMap a s =
      innerOperationMap (operations f a) s ≫
        (analyticFactorsCollectionMap A f.toCollectionHom).app (profileInputs s.outerProfile) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      with_unfolding_all
        exact heq_of_eq ((FiniteTensor.singletonIso (V := C)).hom.naturality
          (f.toCollectionHom.app s.outerProfile))
    | some i =>
      with_unfolding_all exact heq_of_eq (Category.comp_id _).symm

private theorem regrouping_comp (f : O ⟶ P) (A : W → C) (s : ColoredSubstitutionData W) :
    (FiniteFamily.flatten (C := C)).map (nestedMap f A s) ≫
        (substitutionFactorsIso P.toCollection A s).hom =
      (substitutionFactorsIso O.toCollection A s).hom ≫
        (FiniteFamily.flatten (C := C)).map (inputMap f A s) := by
  apply FiniteFamily.Hom_ext
  · ext i
    rcases i with ⟨i, j⟩
    cases i with
    | none => cases j; rfl
    | some i => cases j <;> rfl
  · intro i
    rcases i with ⟨i, j⟩
    cases i with
    | none =>
      cases j
      with_unfolding_all
        change HEq (f.toCollectionHom.app s.outerProfile ≫ 𝟙 _)
          (𝟙 _ ≫ f.toCollectionHom.app s.outerProfile)
        exact heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)
    | some i =>
      cases j with
      | none =>
        with_unfolding_all
          change HEq (f.toCollectionHom.app (s.inner.obj i) ≫ 𝟙 _)
            (𝟙 _ ≫ f.toCollectionHom.app (s.inner.obj i))
          exact heq_of_eq ((Category.comp_id _).trans (Category.id_comp _).symm)
      | some j => with_unfolding_all exact heq_of_eq rfl

private theorem coefficientMap_comp (f : O ⟶ P) (A : W → C) (s : ColoredSubstitutionData W) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (inputMap f A s) ≫
        operadCoefficientMap P A s =
      operadCoefficientMap O A s ≫
        (analyticFactorsCollectionMap A f.toCollectionHom).app (profileInputs s.totalProfile) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    cases i with
    | none =>
      with_unfolding_all exact heq_of_eq (f.map_subst s).symm
    | some i =>
      with_unfolding_all
        change HEq
          ((FiniteTensor.tensor (V := C)).map
            ((FiniteFamily.singleton (C := C)).map (𝟙 (A (s.totalProfile.inputColor i)))) ≫
              (FiniteTensor.singletonIso (V := C)).hom.app (A (s.totalProfile.inputColor i)))
          ((FiniteTensor.singletonIso (V := C)).hom.app (A (s.totalProfile.inputColor i)) ≫ 𝟙 _)
        exact heq_of_eq (by rw [Functor.map_id, Functor.map_id]; simp)

/-- The restricted inner-first route evaluates exactly the mapped original coefficient blocks. -/
theorem substitutionInner (f : O ⟶ P) {A : W → C}
    (a : Operations P.toCollection A A) (s : ColoredSubstitutionData W) :
    algebraSubstitutionInner (operations f a) s =
      (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map (nestedMap f A s)) ≫
        algebraSubstitutionInner a s := by
  let t := FiniteTensor.tensor (V := C)
  let n := nestedMap f A s
  let c := (analyticFactorsCollectionMap A f.toCollectionHom).app (profileInputs s.outerProfile)
  have hn : t.map ((FiniteFamily.flatten (C := C)).map n) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app (nestedOperationFactors P.toCollection A s) =
    (FiniteTensor.flattenIso (V := C)).hom.app (nestedOperationFactors O.toCollection A s) ≫
      t.map ((FiniteFamily.map t).map n) :=
    (FiniteTensor.flattenIso (V := C)).hom.naturality n
  have hm : (FiniteFamily.map t).map n ≫ innerOperationMap a s =
      innerOperationMap (operations f a) s ≫ c := innerMap_comp f a s
  have ht := congrArg t.map hm
  simp only [Functor.map_comp] at ht
  symm
  change t.map ((FiniteFamily.flatten (C := C)).map n) ≫
      ((FiniteTensor.flattenIso (V := C)).hom.app (nestedOperationFactors P.toCollection A s) ≫
        t.map (innerOperationMap a s) ≫ a.app s.outputColor (profileInputs s.outerProfile)) =
    (FiniteTensor.flattenIso (V := C)).hom.app (nestedOperationFactors O.toCollection A s) ≫
      t.map (innerOperationMap (operations f a) s) ≫
        (t.map c ≫ a.app s.outputColor (profileInputs s.outerProfile))
  with_unfolding_all
    rw [← Category.assoc, ← Category.assoc, hn]
    let l := (FiniteTensor.flattenIso (V := C)).hom.app (nestedOperationFactors O.toCollection A s)
    let i := t.map ((FiniteFamily.map t).map n)
    let j := t.map (innerOperationMap a s)
    let i' := t.map (innerOperationMap (operations f a) s)
    let j' := t.map c
    let out := a.app s.outputColor (profileInputs s.outerProfile)
    have hmid : i ≫ j ≫ out = i' ≫ j' ≫ out :=
      (Category.assoc i j out).symm.trans
        ((congrArg (· ≫ out) ht).trans (Category.assoc i' j' out))
    exact (Category.assoc l i (j ≫ out)).trans
      ((congrArg (l ≫ ·) hmid).trans (Category.assoc l i' (j' ≫ out)).symm)

/-- The restricted coefficient-first route uses the original operad substitution square. -/
theorem substitutionInputs (f : O ⟶ P) (A : W → C) (s : ColoredSubstitutionData W) :
    (FiniteTensor.tensor (V := C)).map ((FiniteFamily.flatten (C := C)).map (nestedMap f A s)) ≫
        operadSubstitutionInputs P A s =
      operadSubstitutionInputs O A s ≫
        (analyticSummandCollectionMap A f.toCollectionHom).app (profileInputs s.totalProfile) := by
  let t := FiniteTensor.tensor (V := C)
  let m := inputMap f A s
  have hg := congrArg t.map (regrouping_comp f A s)
  simp only [Functor.map_comp] at hg
  have hm : t.map ((FiniteFamily.flatten (C := C)).map m) ≫
      (FiniteTensor.flattenIso (V := C)).hom.app (substitutionInputFactors P.toCollection A s) =
    (FiniteTensor.flattenIso (V := C)).hom.app (substitutionInputFactors O.toCollection A s) ≫
      t.map ((FiniteFamily.map t).map m) :=
    (FiniteTensor.flattenIso (V := C)).hom.naturality m
  have hc := congrArg t.map (coefficientMap_comp f A s)
  simp only [Functor.map_comp] at hc
  change t.map ((FiniteFamily.flatten (C := C)).map (nestedMap f A s)) ≫
      (t.map (substitutionFactorsIso P.toCollection A s).hom ≫
        (FiniteTensor.flattenIso (V := C)).hom.app (substitutionInputFactors P.toCollection A s) ≫
          t.map (operadCoefficientMap P A s)) =
    (t.map (substitutionFactorsIso O.toCollection A s).hom ≫
      (FiniteTensor.flattenIso (V := C)).hom.app (substitutionInputFactors O.toCollection A s) ≫
        t.map (operadCoefficientMap O A s)) ≫
      t.map ((analyticFactorsCollectionMap A f.toCollectionHom).app (profileInputs s.totalProfile))
  with_unfolding_all
    rw [← Category.assoc, ← Category.assoc, hg]
    have h₁ := congrArg
      (fun k => t.map (substitutionFactorsIso O.toCollection A s).hom ≫ k ≫
        t.map (operadCoefficientMap P A s)) hm
    have h₂ := congrArg
      (fun k => t.map (substitutionFactorsIso O.toCollection A s).hom ≫
        (FiniteTensor.flattenIso (V := C)).hom.app
          (substitutionInputFactors O.toCollection A s) ≫ k) hc
    exact (by simpa only [Category.assoc] using h₁.trans (by
      simpa only [Category.assoc] using h₂))

end Restriction

/-- The original algebra restricted along an original colored operad morphism. -/
def Algebra.restrict {O P : ColoredOperadObj W C} (f : O ⟶ P) (A : Algebra P) : Algebra O where
  carrier := A.carrier
  operations := Restriction.operations f A.operations
  unit d := by
    change unitInsertion O A.carrier d ≫
      ((analyticSummandCollectionMap A.carrier f.toCollectionHom).app (AnalyticIndex.unary d) ≫
        A.operations.app d (AnalyticIndex.unary d)) = 𝟙 _
    rw [← Category.assoc, Restriction.unitInsertion_comp, A.unit]
  substitution s := by
    with_unfolding_all
      rw [Restriction.substitutionInner, A.substitution]
      change (FiniteTensor.tensor (V := C)).map
          ((FiniteFamily.flatten (C := C)).map (Restriction.nestedMap f A.carrier s)) ≫
        (operadSubstitutionInputs P A.carrier s ≫
          A.operations.app s.outputColor (profileInputs s.totalProfile)) =
        operadSubstitutionInputs O A.carrier s ≫
          ((analyticSummandCollectionMap A.carrier f.toCollectionHom).app (profileInputs
            s.totalProfile) ≫
            A.operations.app s.outputColor (profileInputs s.totalProfile))
      let l := (FiniteTensor.tensor (V := C)).map
        ((FiniteFamily.flatten (C := C)).map (Restriction.nestedMap f A.carrier s))
      let i := operadSubstitutionInputs P A.carrier s
      let l' := operadSubstitutionInputs O A.carrier s
      let i' := (analyticSummandCollectionMap A.carrier f.toCollectionHom).app
        (profileInputs s.totalProfile)
      let out := A.operations.app s.outputColor (profileInputs s.totalProfile)
      exact (Category.assoc l i out).symm.trans
        ((congrArg (· ≫ out) (Restriction.substitutionInputs f A.carrier s)).trans
          (Category.assoc l' i' out))

/-- The full restriction functor retains the original carrier maps and every operation square. -/
def restrictionFunctor {O P : ColoredOperadObj W C} (f : O ⟶ P) : Algebra P ⥤ Algebra O where
  obj := Algebra.restrict f
  map {A B} g :=
    { hom := g.hom
      comm d q := by
        change ((analyticSummandCollectionMap A.carrier f.toCollectionHom).app q ≫
            A.operations.app d q) ≫ g.hom d =
          (analyticSummandCarrierMap O.toCollection g.hom).app q ≫
            ((analyticSummandCollectionMap B.carrier f.toCollectionHom).app q ≫
              B.operations.app d q)
        rw [Category.assoc, g.comm, ← Category.assoc]
        have h := congrArg (fun k : NatTrans _ _ => k.app q)
          (analyticSummandCollectionCarrier_mixed A.carrier f.toCollectionHom g.hom)
        simpa only [NatTrans.comp_app, Category.assoc] using congrArg (· ≫ B.operations.app d q) h }
  map_id A := Algebra.Hom.ext rfl
  map_comp f g := Algebra.Hom.ext rfl

end CategoryTheory.Operad.Tensor
