/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorUnit

/-!
# Associativity on the original generic sphere operator coefficients

The complete finite labels associate by the original index pentagon.
The reverse coefficient ordering associates by the original value braidings
and sphere tensorators, with the complete source associator map retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

/-- All three whole finite labels retain the original index associator and pentagon. -/
theorem compositionLabel_assoc (n k l m : I) (q : Labels n k) (r : Labels k l) (s : Labels l m) :
    ((α_ s.left r.left q.left).hom ▷ n) ≫
      compositionLabel n l m
        (CostructuredArrow.mk (Y := r.left ⊗ q.left) (compositionLabel n k l q r)) s =
    compositionLabel n k m q
      (CostructuredArrow.mk (Y := s.left ⊗ r.left) (compositionLabel k l m r s)) := by
  change ((α_ s.left r.left q.left).hom ▷ n) ≫
    (α_ s.left (r.left ⊗ q.left) n).hom ≫
    (s.left ◁ ((α_ r.left q.left n).hom ≫ (r.left ◁ q.hom) ≫ r.hom)) ≫ s.hom =
    (α_ (s.left ⊗ r.left) q.left n).hom ≫ ((s.left ⊗ r.left) ◁ q.hom) ≫
    (α_ s.left r.left k).hom ≫ (s.left ◁ r.hom) ≫ s.hom
  simp only [whiskerLeft_comp, Category.assoc]
  slice_lhs 1 3 => rw [pentagon]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← associator_naturality_right]
  rfl

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]

/-- The original coefficient ordering of an operator composite. -/
def reverseMultiplication (T : V) (a b : I) :
    (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ⊗
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b ⟶
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj (b ⊗ a) :=
  (β_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
    ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b)).hom ≫ coefficientMultiplication T b a

/-- The original sphere tensorators retain the complete indexed associativity equation. -/
theorem coefficientMultiplication_assoc (T : V) (a b c : I) :
    coefficientMultiplication T a b ▷ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj c ≫
      coefficientMultiplication T (a ⊗ b) c ≫
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map (α_ a b c).hom =
    (α_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj c)).hom ≫
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ◁ coefficientMultiplication T b c ≫
      coefficientMultiplication T a (b ⊗ c) := genericSphereSequence_block_assoc T a b c

/-- Both complete value-braiding routes reverse the three original coefficient blocks coherently. -/
theorem tripleReverse (A B C : V) :
    ((β_ A B).hom ▷ C) ≫ (β_ (B ⊗ A) C).hom ≫ (α_ C B A).inv =
      (α_ A B C).hom ≫ (A ◁ (β_ B C).hom) ≫ (β_ A (C ⊗ B)).hom := by
  rw [braiding_tensor_left_hom, braiding_tensor_right_hom]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg (fun f => (α_ A B C).hom ≫ f ≫ (α_ C B A).inv) (yang_baxter A B C)

/-- Every original reverse coefficient multiplication associates through the original index map. -/
theorem reverseMultiplication_assoc (T : V) (a b c : I) :
    reverseMultiplication T a b ▷ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj c ≫
      reverseMultiplication T (b ⊗ a) c =
    (α_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj c)).hom ≫
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ◁ reverseMultiplication T b c ≫
      reverseMultiplication T a (c ⊗ b) ≫
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map (α_ c b a).hom := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let A := P.obj a
  let B := P.obj b
  let C := P.obj c
  let left := (C ◁ coefficientMultiplication T b a) ≫ coefficientMultiplication T c (b ⊗ a)
  let right := (coefficientMultiplication T c b ▷ A) ≫ coefficientMultiplication T (c ⊗ b) a
  have hm : right ≫ P.map (α_ c b a).hom = (α_ C B A).hom ≫ left := by
    simpa only [left, right, Category.assoc] using coefficientMultiplication_assoc T c b a
  have hInv : left = (α_ C B A).inv ≫ right ≫ P.map (α_ c b a).hom := by
    have h := congrArg (fun t => (α_ C B A).inv ≫ t) hm
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
  have hL : (coefficientMultiplication T b a ▷ C) ≫ (β_ (P.obj (b ⊗ a)) C).hom =
      (β_ (B ⊗ A) C).hom ≫ (C ◁ coefficientMultiplication T b a) :=
    braiding_naturality_left (coefficientMultiplication T b a) C
  have hR : (A ◁ coefficientMultiplication T c b) ≫ (β_ A (P.obj (c ⊗ b))).hom =
      (β_ A (C ⊗ B)).hom ≫ (coefficientMultiplication T c b ▷ A) :=
    braiding_naturality_right A (coefficientMultiplication T c b)
  have hFinal : ((β_ A B).hom ▷ C) ≫ (β_ (B ⊗ A) C).hom ≫ left =
      (α_ A B C).hom ≫ (A ◁ (β_ B C).hom) ≫ (β_ A (C ⊗ B)).hom ≫ right ≫
        P.map (α_ c b a).hom := by
    rw [hInv]
    slice_lhs 1 3 => rw [tripleReverse]
    simp only [right, Category.assoc]
  simp only [reverseMultiplication, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  slice_lhs 2 3 => rw [hL]
  slice_rhs 3 4 => rw [hR]
  simp only [Category.assoc]
  simpa only [left, right, Category.assoc] using hFinal

end CategoryTheory.Spectra.Symmetric.OperatorCoend
