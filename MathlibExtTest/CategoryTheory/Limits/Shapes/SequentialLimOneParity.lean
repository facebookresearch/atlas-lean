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

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialLimOneParity

/-!
# Even-odd sequential-product clients

These clients evaluate the unsigned and odd-sign product comparisons, their
projection formulas and the matrix form of the standard difference.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCountableProducts C] [HasBinaryBiproducts C]

variable (A : ℕᵒᵖ ⥤ C) (m : ℕ)

example : parityIndexEquiv (Sum.inl 0) = 0 := by simp
example : parityIndexEquiv (Sum.inr 0) = 1 := by simp
example : parityIndexEquiv (Sum.inl 1) = 2 := by simp
example : parityIndexEquiv (Sum.inr 1) = 3 := by simp

example : parityEvenFamily A m = A.obj (op (2 * m)) := by simp
example : parityOddFamily A m = A.obj (op (2 * m + 1)) := by simp
example : parityEvenProduct A = ∏ᶜ parityEvenFamily A := rfl
example : parityOddProduct A = ∏ᶜ parityOddFamily A := rfl
example : parityProduct A = (parityEvenProduct A ⊞ parityOddProduct A) := rfl

example : parityProduct A ≅ sequentialProduct A := parityProductIso A
example : parityProduct A ≅ sequentialProduct A := paritySignIso A

example :
    (parityProductIso A).hom ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m) =
      biprod.fst ≫ Pi.π (parityEvenFamily A) m := by
  exact parityProductIso_hom_even_π A m

example :
    (parityProductIso A).hom ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m + 1) =
      biprod.snd ≫ Pi.π (parityOddFamily A) m := by
  exact parityProductIso_hom_odd_π A m

example :
    (parityProductIso A).hom ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) 0 =
      biprod.fst ≫ Pi.π (parityEvenFamily A) 0 := by
  simpa using parityProductIso_hom_even_π A 0

example :
    (parityProductIso A).hom ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) 3 =
      biprod.snd ≫ Pi.π (parityOddFamily A) 1 := by
  simpa using parityProductIso_hom_odd_π A 1

example :
    (paritySignIso A).hom ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) 0 =
      biprod.fst ≫ Pi.π (parityEvenFamily A) 0 := by
  simpa using paritySignIso_hom_even_π A 0

example :
    (paritySignIso A).hom ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) 1 =
      -(biprod.snd ≫ Pi.π (parityOddFamily A) 0) := by
  simpa using paritySignIso_hom_odd_π A 0

example :
    (paritySignIso A).hom ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) 2 =
      biprod.fst ≫ Pi.π (parityEvenFamily A) 1 := by
  simpa using paritySignIso_hom_even_π A 1

example :
    parityOddToEvenMap A ≫ Pi.π (parityEvenFamily A) m =
      Pi.π (parityOddFamily A) m ≫
        A.map (homOfLE (by omega : 2 * m ≤ 2 * m + 1)).op := by
  exact parityOddToEvenMap_π A m

example :
    parityNextEvenToOddMap A ≫ Pi.π (parityOddFamily A) m =
      Pi.π (parityEvenFamily A) (m + 1) ≫
        A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op := by
  exact parityNextEvenToOddMap_π A m

example :
    parityOddToEvenMap A ≫ Pi.π (parityEvenFamily A) 0 =
      Pi.π (parityOddFamily A) 0 ≫
        A.map (homOfLE (by omega : 0 ≤ 1)).op := by
  simpa using parityOddToEvenMap_π A 0

example :
    parityNextEvenToOddMap A ≫ Pi.π (parityOddFamily A) 0 =
      Pi.π (parityEvenFamily A) 1 ≫
        A.map (homOfLE (by omega : 1 ≤ 2)).op := by
  simpa using parityNextEvenToOddMap_π A 0

example :
    parityDifference A ≫ biprod.fst ≫
        Pi.π (parityEvenFamily A) m =
      biprod.fst ≫ Pi.π (parityEvenFamily A) m -
        (biprod.snd ≫ Pi.π (parityOddFamily A) m ≫
          A.map (homOfLE (by omega : 2 * m ≤ 2 * m + 1)).op) := by
  exact parityDifference_even_π A m

example :
    parityDifference A ≫ biprod.snd ≫
        Pi.π (parityOddFamily A) m =
      (biprod.fst ≫ Pi.π (parityEvenFamily A) (m + 1) ≫
          A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op) -
        (biprod.snd ≫ Pi.π (parityOddFamily A) m) := by
  exact parityDifference_odd_π A m

example :
    parityDifference A ≫ biprod.fst ≫
        Pi.π (parityEvenFamily A) 0 =
      biprod.fst ≫ Pi.π (parityEvenFamily A) 0 -
        (biprod.snd ≫ Pi.π (parityOddFamily A) 0 ≫
          A.map (homOfLE (by omega : 0 ≤ 1)).op) := by
  exact parityDifference_even_π A 0

example :
    parityDifference A ≫ biprod.snd ≫
        Pi.π (parityOddFamily A) 0 =
      (biprod.fst ≫ Pi.π (parityEvenFamily A) 1 ≫
          A.map (homOfLE (by omega : 1 ≤ 2)).op) -
        (biprod.snd ≫ Pi.π (parityOddFamily A) 0) := by
  exact parityDifference_odd_π A 0

example :
    parityDifference A ≫ biprod.fst ≫
        Pi.π (parityEvenFamily A) 1 =
      biprod.fst ≫ Pi.π (parityEvenFamily A) 1 -
        (biprod.snd ≫ Pi.π (parityOddFamily A) 1 ≫
          A.map (homOfLE (by omega : 2 ≤ 3)).op) := by
  exact parityDifference_even_π A 1

example :
    parityDifference A ≫ (paritySignIso A).hom =
      (parityProductIso A).hom ≫ sequentialDifference A := by
  exact parityDifference_comp_signIso A

end CategoryTheory.Limits

end
