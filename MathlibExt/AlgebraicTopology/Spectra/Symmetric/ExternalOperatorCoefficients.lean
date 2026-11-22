/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorCategory
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.ExternalModulePresentation

/-!
# Original external sphere coefficients in operator order

The value braid places the indexed object first and the coefficient second.
All original finite-index maps, associators and coefficient products remain
in the complete equations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.MonoidalCategory
open scoped ExternalProduct CategoryTheory.MonObj

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The complete original ordinary sphere-module presentation. -/
abbrev SphereData (T : V) := DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X

variable {T : V}

/-- The entire original coefficient map with its explicit source and target objects. -/
def coefficient (d : SphereData T) (a n : I) :
    (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ⊗ d.diagram.obj n ⟶
      d.diagram.obj (a ⊗ n) := d.action.app (a, n)

/-- Every original coefficient-index arrow retains the full external action square. -/
theorem coefficient_natural (d : SphereData T) {a b : I} (f : a ⟶ b) (n : I) :
    ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map f ▷ d.diagram.obj n) ≫
      coefficient d b n = coefficient d a n ≫ d.diagram.map (f ▷ n) := by
  have h := d.action.naturality ((f, 𝟙 n) : (a, n) ⟶ (b, n))
  simpa only [externalProductBifunctor_obj_map, Functor.comp_map, tensor,
    Functor.map_id, whiskerLeft_id, Category.comp_id, tensorHom_id, coefficient] using! h

/-- Every original object-index arrow retains the full external action square. -/
theorem index_natural (d : SphereData T) (a : I) {n k : I} (f : n ⟶ k) :
    ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ◁ d.diagram.map f) ≫
      coefficient d a k = coefficient d a n ≫ d.diagram.map (a ◁ f) := by
  have h := d.action.naturality ((𝟙 a, f) : (a, n) ⟶ (a, k))
  simpa only [externalProductBifunctor_obj_map, Functor.comp_map, tensor,
    Functor.map_id, id_whiskerRight, Category.id_comp, id_tensorHom, coefficient] using! h

/-- The entire empty external coefficient is the original value and index unitor map. -/
theorem coefficient_unit (d : SphereData T) (n : I) :
    coefficient d (𝟙_ I) n = (λ_ (d.diagram.obj n)).hom ≫ d.diagram.map (λ_ n).inv := by
  let z : (𝟙_ V) ⊗ d.diagram.obj n ⟶ d.diagram.obj ((𝟙_ I) ⊗ n) := coefficient d (𝟙_ I) n
  have h := d.unit n
  have hs := congrArg (fun t => (t ▷ d.diagram.obj n) ≫ z)
    (genericSphereDayMonoid_unit T)
  have hi : (𝟙 (𝟙_ V) ▷ d.diagram.obj n) ≫ z = z := by
    rw [id_whiskerRight, Category.id_comp]
  exact hi.symm.trans (hs.symm.trans h)

/-- Full external associativity in the original target-associator direction. -/
theorem coefficient_assoc_hom (d : SphereData T) (a b n : I) :
    (α_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b) (d.diagram.obj n)).hom ≫
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ◁ coefficient d b n ≫
      coefficient d a (b ⊗ n) =
    coefficientMultiplication T a b ▷ d.diagram.obj n ≫ coefficient d (a ⊗ b) n ≫
      d.diagram.map (α_ a b n).hom := by
  have h : coefficientMultiplication T a b ▷ d.diagram.obj n ≫ coefficient d (a ⊗ b) n =
      (α_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
        ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b) (d.diagram.obj n)).hom ≫
        (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ◁ coefficient d b n ≫
        coefficient d a (b ⊗ n) ≫ d.diagram.map (α_ a b n).inv := by
    have h := d.assoc a b n
    rw [genericSphereDayMonoid_multiplication] at h
    exact h
  have h' := congrArg (fun t => t ≫ d.diagram.map (α_ a b n).hom) h
  have hi : d.diagram.map (α_ a b n).inv ≫ d.diagram.map (α_ a b n).hom = 𝟙 _ :=
    (d.diagram.mapIso (α_ a b n)).inv_hom_id
  simpa only [Category.assoc, hi, Category.comp_id] using h'.symm

/-- The whole original external coefficient with the object before its coefficient. -/
def coefficientAction (d : SphereData T) (a n : I) :
    d.diagram.obj n ⊗ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ⟶
      d.diagram.obj (a ⊗ n) :=
  (β_ (d.diagram.obj n) ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)).hom ≫
    coefficient d a n

omit [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The complete value-braiding routes for two successive external coefficients. -/
theorem coefficient_braiding_route (X A B : V) :
    (α_ X A B).inv ≫ ((β_ X A).hom ▷ B) ≫ (β_ (A ⊗ X) B).hom =
      (X ◁ (β_ A B).hom) ≫ (β_ X (B ⊗ A)).hom ≫ (α_ B A X).hom := by
  have h := congrArg (fun t => (α_ X A B).inv ≫ t ≫ (α_ B A X).hom) (tripleReverse X A B)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- All original right-ordered coefficients associate with the complete reversed block product. -/
theorem coefficientAction_assoc (d : SphereData T) (a b n : I) :
    (α_ (d.diagram.obj n) ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b)).inv ≫
      (coefficientAction d a n ▷ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b) ≫
      coefficientAction d b (a ⊗ n) =
    (d.diagram.obj n ◁ reverseMultiplication T a b) ≫ coefficientAction d (b ⊗ a) n ≫
      d.diagram.map (α_ b a n).hom := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let X := d.diagram.obj n
  let A := P.obj a
  let B := P.obj b
  have hn : (coefficient d a n ▷ B) ≫ (β_ (d.diagram.obj (a ⊗ n)) B).hom =
      (β_ (A ⊗ X) B).hom ≫ (B ◁ coefficient d a n) :=
    braiding_naturality_left (coefficient d a n) B
  have hm := coefficient_assoc_hom d b a n
  have hb : (β_ X (B ⊗ A)).hom ≫ (coefficientMultiplication T b a ▷ X) =
      (X ◁ coefficientMultiplication T b a) ≫ (β_ X (P.obj (b ⊗ a))).hom :=
    (braiding_naturality_right X (coefficientMultiplication T b a)).symm
  change (α_ X A B).inv ≫ ((β_ X A).hom ≫ coefficient d a n) ▷ B ≫
    ((β_ (d.diagram.obj (a ⊗ n)) B).hom ≫ coefficient d b (a ⊗ n)) =
    (X ◁ reverseMultiplication T a b) ≫ ((β_ X (P.obj (b ⊗ a))).hom ≫
      coefficient d (b ⊗ a) n) ≫ d.diagram.map (α_ b a n).hom
  simp only [comp_whiskerRight, Category.assoc]
  slice_lhs 3 4 => rw [hn]
  simp only [Category.assoc]
  slice_lhs 1 3 => rw [coefficient_braiding_route]
  simp only [Category.assoc]
  slice_lhs 3 5 => rw [hm]
  slice_lhs 2 3 => rw [hb]
  simp only [Category.assoc, reverseMultiplication, whiskerLeft_comp]
  rfl

end CategoryTheory.Spectra.Symmetric.OperatorCoend
