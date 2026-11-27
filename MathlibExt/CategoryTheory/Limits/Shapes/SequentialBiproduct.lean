/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.CategoryTheory.Limits.Shapes.BiproductKernels
public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialLimOne

/-!
# Biproducts of inverse sequences

A finite biproduct of inverse sequences commutes with the countable product
through its stage projections. Under this product comparison, the standard
one-minus-shift map is the biproduct of the standard difference maps of the
component sequences. The induced kernel and cokernel comparisons retain
these coordinate maps.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

noncomputable section

open Opposite

universe u v w

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {I : Type w} [HasBiproductsOfShape I C] [HasCountableProducts C]
  (A : I → ℕᵒᵖ ⥤ C)

/-- The inverse tower formed with the biproducts and given transition maps. -/
def sequentialBiproduct : ℕᵒᵖ ⥤ C where
  obj n := ⨁ (fun i => (A i).obj n)
  map f := biproduct.map (fun i => (A i).map f)
  map_id n := by
    apply biproduct.hom_ext
    intro i
    simp only [biproduct.map_π, Functor.map_id, Category.comp_id, Category.id_comp]
  map_comp f g := by
    apply biproduct.hom_ext
    intro i
    simp only [Category.assoc, biproduct.map_π, biproduct.map_π_assoc, Functor.map_comp]

/-- The product/biproduct interchange map uses every given projection. -/
def sequentialBiproductProductHom :
    (⨁ fun i => sequentialProduct (A i)) ⟶ sequentialProduct (sequentialBiproduct A) :=
  Pi.lift (f := fun n => (sequentialBiproduct A).obj (op n))
    (fun n => biproduct.map (fun i => Pi.π (fun n => (A i).obj (op n)) n))

/-- The inverse first projects in the given stage and then in the given summand. -/
def sequentialBiproductProductInv :
    sequentialProduct (sequentialBiproduct A) ⟶ ⨁ fun i => sequentialProduct (A i) :=
  biproduct.lift (f := fun i => sequentialProduct (A i)) (fun i =>
    Pi.lift (f := fun n => (A i).obj (op n)) (fun n =>
    Pi.π (fun n => (sequentialBiproduct A).obj (op n)) n ≫
      biproduct.π (fun i => (A i).obj (op n)) i))

set_option backward.isDefEq.respectTransparency false in
/-- The countable product and finite biproduct commute. -/
def sequentialBiproductProductIso :
    (⨁ fun i => sequentialProduct (A i)) ≅ sequentialProduct (sequentialBiproduct A) where
  hom := sequentialBiproductProductHom A
  inv := sequentialBiproductProductInv A
  hom_inv_id := by
    apply biproduct.hom_ext
    intro i
    apply Pi.hom_ext
    intro n
    simp only [sequentialBiproductProductHom, sequentialBiproductProductInv,
      Category.assoc, biproduct.lift_π, Pi.lift_comp_π, Pi.lift_comp_π_assoc, biproduct.map_π,
      Category.id_comp]
  inv_hom_id := by
    apply Pi.hom_ext
    intro n
    apply biproduct.hom_ext
    intro i
    simp only [sequentialBiproductProductHom, sequentialBiproductProductInv,
      Category.assoc, Pi.lift_comp_π, biproduct.map_π, biproduct.lift_π_assoc,
      Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Interchange preserves each stage and summand projection. -/
@[reassoc]
theorem sequentialBiproductProductIso_hom_π_π (n : ℕ) (i : I) :
    (sequentialBiproductProductIso A).hom ≫
      Pi.π (fun n => (sequentialBiproduct A).obj (op n)) n ≫
        biproduct.π (fun i => (A i).obj (op n)) i =
    biproduct.π (fun i => sequentialProduct (A i)) i ≫
      Pi.π (fun n => (A i).obj (op n)) n := by
  simp only [sequentialBiproductProductIso, sequentialBiproductProductHom,
    Pi.lift_comp_π_assoc, biproduct.map_π]

set_option backward.isDefEq.respectTransparency false in
/-- The given standard differences commute with the interchange map. -/
theorem sequentialBiproductDifference_comp_productIso :
    biproduct.map (fun i => sequentialDifference (A i)) ≫
        (sequentialBiproductProductIso A).hom =
      (sequentialBiproductProductIso A).hom ≫
        sequentialDifference (sequentialBiproduct A) := by
  apply Pi.hom_ext
  intro n
  apply biproduct.hom_ext
  intro i
  have hm : (sequentialBiproduct A).map (homOfLE (Nat.le_succ n)).op ≫
      biproduct.π (fun i => (A i).obj (op n)) i =
    biproduct.π (fun i => (A i).obj (op (n + 1))) i ≫
      (A i).map (homOfLE (Nat.le_succ n)).op :=
    biproduct.map_π (fun i => (A i).map (homOfLE (Nat.le_succ n)).op) i
  simp only [Category.assoc, sequentialBiproductProductIso_hom_π_π,
    biproduct.map_π_assoc, sequentialDifference_π,
    Preadditive.comp_sub, Preadditive.sub_comp]
  erw [hm, sequentialBiproductProductIso_hom_π_π_assoc]

section Kernels

variable [HasKernels C]

/-- The standard-difference kernel splits through the given component kernels. -/
def sequentialBiproductKernelIso :
    (⨁ fun i => kernel (sequentialDifference (A i))) ≅
      kernel (sequentialDifference (sequentialBiproduct A)) :=
  biproductKernelIso (fun i => sequentialDifference (A i)) ≪≫
    kernel.mapIso (biproduct.map (fun i => sequentialDifference (A i)))
      (sequentialDifference (sequentialBiproduct A))
      (sequentialBiproductProductIso A) (sequentialBiproductProductIso A)
      (sequentialBiproductDifference_comp_productIso A)

set_option backward.isDefEq.respectTransparency false in
/-- The split kernel comparison preserves every given inclusion. -/
theorem sequentialBiproductKernelIso_hom_comp_ι :
    (sequentialBiproductKernelIso A).hom ≫
      kernel.ι (sequentialDifference (sequentialBiproduct A)) =
    biproduct.map (fun i => kernel.ι (sequentialDifference (A i))) ≫
      (sequentialBiproductProductIso A).hom := by
  simp only [sequentialBiproductKernelIso, Iso.trans_hom, kernel.mapIso_hom,
    Category.assoc, kernel.map, kernel.lift_ι]
  rw [← Category.assoc, biproductKernelIso_hom_comp_ι]
  rfl

section Limits

variable [∀ i, HasLimit (A i)] [HasLimit (sequentialBiproduct A)]

/-- The chosen inverse limit of the given biproduct tower is the component limit biproduct. -/
def sequentialBiproductLimitIso :
    limit (sequentialBiproduct A) ≅ ⨁ fun i => limit (A i) :=
  sequentialLimitKernelIso (sequentialBiproduct A) ≪≫
    (sequentialBiproductKernelIso A).symm ≪≫
      biproduct.mapIso (fun i => (sequentialLimitKernelIso (A i)).symm)

end Limits

end Kernels

section Cokernels

variable [HasCokernels C]

/-- Concrete sequential lim-one of the given biproduct tower is the lim-one biproduct. -/
def sequentialBiproductLimOneIso :
    sequentialLimOne (sequentialBiproduct A) ≅ ⨁ fun i => sequentialLimOne (A i) :=
  (cokernel.mapIso (biproduct.map (fun i => sequentialDifference (A i)))
    (sequentialDifference (sequentialBiproduct A))
    (sequentialBiproductProductIso A) (sequentialBiproductProductIso A)
    (sequentialBiproductDifference_comp_productIso A)).symm ≪≫
    biproductCokernelIso (fun i => sequentialDifference (A i))

set_option backward.isDefEq.respectTransparency false in
/-- The lim-one comparison preserves the given quotient maps through the product interchange. -/
theorem sequentialLimOneπ_comp_biproductLimOneIso :
    sequentialLimOneπ (sequentialBiproduct A) ≫
      (sequentialBiproductLimOneIso A).hom =
    (sequentialBiproductProductIso A).inv ≫
      biproduct.map (fun i => sequentialLimOneπ (A i)) := by
  simp only [sequentialBiproductLimOneIso, sequentialLimOneπ,
    Iso.trans_hom, Iso.symm_hom, cokernel.mapIso_inv]
  simp only [Category.assoc, cokernel.map, cokernel.π_desc_assoc]
  rw [π_comp_biproductCokernelIso_hom]
  rfl

end Cokernels

end CategoryTheory.Limits
