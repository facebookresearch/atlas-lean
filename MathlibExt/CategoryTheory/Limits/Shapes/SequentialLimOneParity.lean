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

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialLimOne
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.Logic.Equiv.Nat

/-!
# Even-odd coordinates for the sequential difference

The product of an inverse sequence decomposes into its even and odd factors.
The standard one-minus-shift map has an explicit matrix in these coordinates,
with a sign change on the odd target factors. Projection formulas characterize
the coordinate comparison and the signed difference.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- The equivalence that lists the even indices before the odd indices. -/
abbrev parityIndexEquiv : ℕ ⊕ ℕ ≃ ℕ :=
  Equiv.natSumNatEquivNat

/-- The even summand of the parity index equivalence sends m to 2m. -/
@[simp]
theorem parityIndexEquiv_inl (m : ℕ) :
    parityIndexEquiv (Sum.inl m) = 2 * m := by
  simp [parityIndexEquiv]

/-- The odd summand of the parity index equivalence sends m to 2m + 1. -/
@[simp]
theorem parityIndexEquiv_inr (m : ℕ) :
    parityIndexEquiv (Sum.inr m) = 2 * m + 1 := by
  simp [parityIndexEquiv]

/-- The objects of a tower indexed through the parity equivalence. -/
abbrev parityTowerFamily (A : ℕᵒᵖ ⥤ C) : ℕ ⊕ ℕ → C :=
  fun i ↦ A.obj (op (parityIndexEquiv i))

/-- The even objects of a tower. -/
abbrev parityEvenFamily (A : ℕᵒᵖ ⥤ C) (m : ℕ) : C :=
  parityTowerFamily A (Sum.inl m)

/-- The odd objects of a tower. -/
abbrev parityOddFamily (A : ℕᵒᵖ ⥤ C) (m : ℕ) : C :=
  parityTowerFamily A (Sum.inr m)

/-- The m-th even factor is the inverse-sequence object at 2m. -/
@[simp]
theorem parityEvenFamily_eq (A : ℕᵒᵖ ⥤ C) (m : ℕ) :
    parityEvenFamily A m = A.obj (op (2 * m)) := by
  simp [parityEvenFamily, parityTowerFamily]

/-- The m-th odd factor is the inverse-sequence object at 2m + 1. -/
@[simp]
theorem parityOddFamily_eq (A : ℕᵒᵖ ⥤ C) (m : ℕ) :
    parityOddFamily A m = A.obj (op (2 * m + 1)) := by
  simp [parityOddFamily, parityTowerFamily]

/-- The chosen product of the even objects of a tower. -/
abbrev parityEvenProduct (A : ℕᵒᵖ ⥤ C) [HasCountableProducts C] : C :=
  ∏ᶜ parityEvenFamily A

/-- The chosen product of the odd objects of a tower. -/
abbrev parityOddProduct (A : ℕᵒᵖ ⥤ C) [HasCountableProducts C] : C :=
  ∏ᶜ parityOddFamily A

/-- The biproduct of the chosen even and odd products. -/
abbrev parityProduct (A : ℕᵒᵖ ⥤ C) [Preadditive C]
    [HasCountableProducts C] [HasBinaryBiproducts C] : C :=
  parityEvenProduct A ⊞ parityOddProduct A

section Parity

variable [Preadditive C] [HasCountableProducts C] [HasBinaryBiproducts C]

/-- Reassemble the even and odd products into the sequential product. -/
noncomputable def parityProductIso (A : ℕᵒᵖ ⥤ C) :
    parityProduct A ≅ sequentialProduct A := by
  letI : Countable (ℕ ⊕ ℕ) := Countable.of_equiv ℕ parityIndexEquiv.symm
  let f : ℕ → C := fun n ↦ A.obj (op n)
  let pf : ℕ ⊕ ℕ → C := f ∘ parityIndexEquiv
  let toSum : parityProduct A ⟶ ∏ᶜ pf :=
    Pi.lift fun
      | Sum.inl m => biprod.fst ≫ Pi.π (parityEvenFamily A) m
      | Sum.inr m => biprod.snd ≫ Pi.π (parityOddFamily A) m
  let fromSum : (∏ᶜ pf) ⟶ parityProduct A :=
    biprod.lift
      (Pi.lift fun m ↦ Pi.π pf (Sum.inl m))
      (Pi.lift fun m ↦ Pi.π pf (Sum.inr m))
  let splitIso : parityProduct A ≅ ∏ᶜ pf :=
    { hom := toSum
      inv := fromSum
      hom_inv_id := by
        apply biprod.hom_ext
        · apply Pi.hom_ext
          intro m
          simp [toSum, fromSum]
        · apply Pi.hom_ext
          intro m
          simp [toSum, fromSum]
      inv_hom_id := by
        apply Pi.hom_ext
        rintro (m | m) <;> simp [toSum, fromSum] }
  exact splitIso ≪≫ Pi.reindex parityIndexEquiv f
/-- The unsigned parity comparison sends the even coordinate at 2m to the m-th even-factor
projection. -/
@[reassoc (attr := simp)]
theorem parityProductIso_hom_even_π (A : ℕᵒᵖ ⥤ C) (m : ℕ) :
    (parityProductIso A).hom ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m) =
      biprod.fst ≫ Pi.π (parityEvenFamily A) m := by
  let _ : Countable (ℕ ⊕ ℕ) := Countable.of_equiv ℕ parityIndexEquiv.symm
  change (parityProductIso A).hom ≫
      Pi.π (fun n : ℕ ↦ A.obj (op n)) (parityIndexEquiv (Sum.inl m)) =
    biprod.fst ≫ Pi.π (parityEvenFamily A) m
  dsimp [parityProductIso]
  rw [Category.assoc, Pi.reindex_hom_π]
  rw [Pi.lift_comp_π]

/-- The unsigned parity comparison sends the odd coordinate at 2m + 1 to the m-th odd-factor
projection. -/
@[reassoc (attr := simp)]
theorem parityProductIso_hom_odd_π (A : ℕᵒᵖ ⥤ C) (m : ℕ) :
    (parityProductIso A).hom ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m + 1) =
      biprod.snd ≫ Pi.π (parityOddFamily A) m := by
  let _ : Countable (ℕ ⊕ ℕ) := Countable.of_equiv ℕ parityIndexEquiv.symm
  change (parityProductIso A).hom ≫
      Pi.π (fun n : ℕ ↦ A.obj (op n)) (parityIndexEquiv (Sum.inr m)) =
    biprod.snd ≫ Pi.π (parityOddFamily A) m
  dsimp [parityProductIso]
  rw [Category.assoc, Pi.reindex_hom_π]
  rw [Pi.lift_comp_π]

/-- Reassemble parity coordinates while negating the odd target coordinates. -/
noncomputable def paritySignIso (A : ℕᵒᵖ ⥤ C) :
    parityProduct A ≅ sequentialProduct A :=
  biprod.mapIso (Iso.refl _) (-Iso.refl _) ≪≫ parityProductIso A

/-- The signed parity comparison preserves every even-factor projection. -/
@[reassoc (attr := simp)]
theorem paritySignIso_hom_even_π (A : ℕᵒᵖ ⥤ C) (m : ℕ) :
    (paritySignIso A).hom ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m) =
      biprod.fst ≫ Pi.π (parityEvenFamily A) m := by
  rw [paritySignIso, Iso.trans_hom, Category.assoc,
    parityProductIso_hom_even_π]
  rw [biprod.mapIso_hom]
  calc
    biprod.map (Iso.refl (parityEvenProduct A)).hom
          (-Iso.refl (parityOddProduct A)).hom ≫ biprod.fst ≫
        Pi.π (parityEvenFamily A) m =
      (biprod.map (Iso.refl (parityEvenProduct A)).hom
          (-Iso.refl (parityOddProduct A)).hom ≫ biprod.fst) ≫
        Pi.π (parityEvenFamily A) m := (Category.assoc _ _ _).symm
    _ = (biprod.fst ≫ (Iso.refl (parityEvenProduct A)).hom) ≫
        Pi.π (parityEvenFamily A) m := by rw [biprod.map_fst]
    _ = biprod.fst ≫ Pi.π (parityEvenFamily A) m := by simp

/-- The signed parity comparison negates every odd-factor projection. -/
@[reassoc (attr := simp)]
theorem paritySignIso_hom_odd_π (A : ℕᵒᵖ ⥤ C) (m : ℕ) :
    (paritySignIso A).hom ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m + 1) =
      -(biprod.snd ≫ Pi.π (parityOddFamily A) m) := by
  rw [paritySignIso, Iso.trans_hom, Category.assoc,
    parityProductIso_hom_odd_π]
  rw [biprod.mapIso_hom]
  calc
    biprod.map (Iso.refl (parityEvenProduct A)).hom
          (-Iso.refl (parityOddProduct A)).hom ≫ biprod.snd ≫
        Pi.π (parityOddFamily A) m =
      (biprod.map (Iso.refl (parityEvenProduct A)).hom
          (-Iso.refl (parityOddProduct A)).hom ≫ biprod.snd) ≫
        Pi.π (parityOddFamily A) m := (Category.assoc _ _ _).symm
    _ = (biprod.snd ≫ (-Iso.refl (parityOddProduct A)).hom) ≫
        Pi.π (parityOddFamily A) m := by rw [biprod.map_snd]
    _ = -(biprod.snd ≫ Pi.π (parityOddFamily A) m) := by simp

/-- The transition from odd coordinates to the preceding even coordinates. -/
noncomputable def parityOddToEvenMap (A : ℕᵒᵖ ⥤ C) :
    parityOddProduct A ⟶ parityEvenProduct A :=
  Pi.lift fun m ↦
    Pi.π (parityOddFamily A) m ≫
      A.map (homOfLE (by omega : 2 * m ≤ 2 * m + 1)).op

omit [Preadditive C] [HasBinaryBiproducts C] in
/-- The m-th odd-to-even product coordinate is the successor transition from stage 2m + 1 to stage
2m. -/
@[reassoc (attr := simp)]
theorem parityOddToEvenMap_π (A : ℕᵒᵖ ⥤ C) (m : ℕ) :
    parityOddToEvenMap A ≫ Pi.π (parityEvenFamily A) m =
      Pi.π (parityOddFamily A) m ≫
        A.map (homOfLE (by omega : 2 * m ≤ 2 * m + 1)).op := by
  simp [parityOddToEvenMap] ; rfl

/-- The transition from the next even coordinate to the odd coordinate. -/
noncomputable def parityNextEvenToOddMap (A : ℕᵒᵖ ⥤ C) :
    parityEvenProduct A ⟶ parityOddProduct A :=
  Pi.lift fun m ↦
    Pi.π (parityEvenFamily A) (m + 1) ≫
      A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op

omit [Preadditive C] [HasBinaryBiproducts C] in
/-- The m-th next-even-to-odd coordinate is the transition from stage 2(m + 1) to stage 2m + 1. -/
@[reassoc (attr := simp)]
theorem parityNextEvenToOddMap_π (A : ℕᵒᵖ ⥤ C) (m : ℕ) :
    parityNextEvenToOddMap A ≫ Pi.π (parityOddFamily A) m =
      Pi.π (parityEvenFamily A) (m + 1) ≫
        A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op := by
  simp [parityNextEvenToOddMap] ; rfl

/-- The sequential difference in even/odd block coordinates. -/
noncomputable def parityDifference (A : ℕᵒᵖ ⥤ C) :
    parityProduct A ⟶ parityProduct A :=
  biprod.lift
    (biprod.fst - biprod.snd ≫ parityOddToEvenMap A)
    (biprod.fst ≫ parityNextEvenToOddMap A - biprod.snd)

/-- The even coordinate of the parity difference is the even input minus the adjacent odd input
transported by the successor map. -/
@[reassoc (attr := simp)]
theorem parityDifference_even_π (A : ℕᵒᵖ ⥤ C) (m : ℕ) :
    parityDifference A ≫ biprod.fst ≫
        Pi.π (parityEvenFamily A) m =
      biprod.fst ≫ Pi.π (parityEvenFamily A) m -
        (biprod.snd ≫ Pi.π (parityOddFamily A) m ≫
          A.map (homOfLE (by omega : 2 * m ≤ 2 * m + 1)).op) := by
  simp [parityDifference, Category.assoc, Preadditive.sub_comp] ; rfl

/-- The odd coordinate of the parity difference is the next even input transported by the
successor map minus the odd input. -/
@[reassoc (attr := simp)]
theorem parityDifference_odd_π (A : ℕᵒᵖ ⥤ C) (m : ℕ) :
    parityDifference A ≫ biprod.snd ≫
        Pi.π (parityOddFamily A) m =
      (biprod.fst ≫ Pi.π (parityEvenFamily A) (m + 1) ≫
          A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op) -
        (biprod.snd ≫ Pi.π (parityOddFamily A) m) := by
  simp [parityDifference, Category.assoc, Preadditive.sub_comp] ; rfl

/-- The parity difference followed by the odd-sign comparison equals the unsigned parity
comparison followed by the standard sequential difference. -/
@[reassoc]
theorem parityDifference_comp_signIso (A : ℕᵒᵖ ⥤ C) :
    parityDifference A ≫ (paritySignIso A).hom =
      (parityProductIso A).hom ≫ sequentialDifference A := by
  let _ : Countable (ℕ ⊕ ℕ) := Countable.of_equiv ℕ parityIndexEquiv.symm
  let e := Pi.reindex parityIndexEquiv (fun n : ℕ ↦ A.obj (op n))
  apply (cancel_mono e.inv).1
  apply Pi.hom_ext
  rintro (m | m)
  · dsimp [e]
    simp only [Category.assoc, Pi.reindex_inv_π]
    change parityDifference A ≫ (paritySignIso A).hom ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m) =
      (parityProductIso A).hom ≫ sequentialDifference A ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m)
    rw [paritySignIso_hom_even_π]
    rw [sequentialDifference_π, Preadditive.comp_sub,
      parityProductIso_hom_even_π]
    have hOdd :
        (parityProductIso A).hom ≫
            Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m + 1) ≫
              A.map (homOfLE (by omega : 2 * m ≤ 2 * m + 1)).op =
          biprod.snd ≫ Pi.π (parityOddFamily A) m ≫
            A.map (homOfLE (by omega : 2 * m ≤ 2 * m + 1)).op := by
      calc
        (parityProductIso A).hom ≫
              Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m + 1) ≫
            A.map (homOfLE (by omega : 2 * m ≤ 2 * m + 1)).op =
          ((parityProductIso A).hom ≫
              Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m + 1)) ≫
            A.map (homOfLE (by omega : 2 * m ≤ 2 * m + 1)).op :=
              (Category.assoc _ _ _).symm
        _ = (biprod.snd ≫ Pi.π (parityOddFamily A) m) ≫
            A.map (homOfLE (by omega : 2 * m ≤ 2 * m + 1)).op :=
          congrArg
            (fun q ↦ q ≫
              A.map (homOfLE (by omega : 2 * m ≤ 2 * m + 1)).op)
            (parityProductIso_hom_odd_π A m)
        _ = biprod.snd ≫ Pi.π (parityOddFamily A) m ≫
            A.map (homOfLE (by omega : 2 * m ≤ 2 * m + 1)).op :=
              Category.assoc _ _ _
    exact (parityDifference_even_π A m).trans
      (congrArg
        (fun q ↦ biprod.fst ≫ Pi.π (parityEvenFamily A) m - q)
        hOdd.symm)
  · dsimp [e]
    simp only [Category.assoc, Pi.reindex_inv_π]
    change parityDifference A ≫ (paritySignIso A).hom ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m + 1) =
      (parityProductIso A).hom ≫ sequentialDifference A ≫
        Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m + 1)
    rw [paritySignIso_hom_odd_π]
    rw [sequentialDifference_π, Preadditive.comp_sub,
      parityProductIso_hom_odd_π]
    have hEven :
        (parityProductIso A).hom ≫
            Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * (m + 1)) ≫
              A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op =
          biprod.fst ≫ Pi.π (parityEvenFamily A) (m + 1) ≫
            A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op := by
      calc
        (parityProductIso A).hom ≫
              Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * (m + 1)) ≫
            A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op =
          ((parityProductIso A).hom ≫
              Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * (m + 1))) ≫
            A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op :=
              (Category.assoc _ _ _).symm
        _ = (biprod.fst ≫ Pi.π (parityEvenFamily A) (m + 1)) ≫
            A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op :=
          congrArg
            (fun q ↦ q ≫
              A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op)
            (parityProductIso_hom_even_π A (m + 1))
        _ = biprod.fst ≫ Pi.π (parityEvenFamily A) (m + 1) ≫
            A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op :=
              Category.assoc _ _ _
    have hEven' :
        (parityProductIso A).hom ≫
            Pi.π (fun n : ℕ ↦ A.obj (op n)) (2 * m + 1 + 1) ≫
              A.map (homOfLE (Nat.le_succ (2 * m + 1))).op =
          biprod.fst ≫ Pi.π (parityEvenFamily A) (m + 1) ≫
            A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op := by
      simpa only [Nat.mul_succ, ← Nat.add_assoc, Nat.reduceAdd] using hEven
    rw [hEven']
    let o : parityProduct A ⟶ parityOddFamily A m :=
      biprod.snd ≫ Pi.π (parityOddFamily A) m
    let eNext : parityProduct A ⟶ parityOddFamily A m :=
      biprod.fst ≫ Pi.π (parityEvenFamily A) (m + 1) ≫
        A.map (homOfLE (by omega : 2 * m + 1 ≤ 2 * (m + 1))).op
    have hDiff : parityDifference A ≫ o = eNext - o := by
      exact parityDifference_odd_π A m
    change parityDifference A ≫ (-o) = o - eNext
    calc
      parityDifference A ≫ (-o) = -(parityDifference A ≫ o) := by simp
      _ = -(eNext - o) := congrArg Neg.neg hDiff
      _ = o - eNext := by simp

end Parity

end CategoryTheory.Limits

end
