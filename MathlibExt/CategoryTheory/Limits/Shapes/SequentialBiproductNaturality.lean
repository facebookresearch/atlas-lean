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

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialBiproduct

/-!
# Naturality of inverse-sequence biproduct comparisons

Maps of inverse sequences induce maps of their finite biproducts. The
comparison between the countable product of a biproduct and the biproduct of
countable products commutes with these maps on every stage projection. The
kernel and cokernel comparisons are natural for the same component maps.
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
  {A B : I → ℕᵒᵖ ⥤ C}

/-- The map of the given finite biproduct towers. -/
def sequentialBiproductMap (α : ∀ i, A i ⟶ B i) :
    sequentialBiproduct A ⟶ sequentialBiproduct B where
  app n := biproduct.map (fun i => (α i).app n)
  naturality {n m} f := by
    change biproduct.map (fun i => (A i).map f) ≫
      biproduct.map (fun i => (α i).app m) =
      biproduct.map (fun i => (α i).app n) ≫ biproduct.map (fun i => (B i).map f)
    apply biproduct.hom_ext
    intro i
    simp only [Category.assoc, biproduct.map_π, biproduct.map_π_assoc]
    simp only [(α i).naturality f]

set_option backward.isDefEq.respectTransparency false in
/-- Product interchange commutes with every given component tower map. -/
theorem sequentialBiproductProductIso_naturality (α : ∀ i, A i ⟶ B i) :
    biproduct.map (fun i => sequentialProductMap (α i)) ≫
        (sequentialBiproductProductIso B).hom =
      (sequentialBiproductProductIso A).hom ≫
        sequentialProductMap (sequentialBiproductMap α) := by
  apply Pi.hom_ext
  intro n
  apply biproduct.hom_ext
  intro i
  have hm : (sequentialBiproductMap α).app (op n) ≫
      biproduct.π (fun i => (B i).obj (op n)) i =
    biproduct.π (fun i => (A i).obj (op n)) i ≫ (α i).app (op n) :=
    biproduct.map_π (fun i => (α i).app (op n)) i
  simp only [Category.assoc, sequentialBiproductProductIso_hom_π_π,
    biproduct.map_π_assoc,
    sequentialProductMap_π]
  erw [hm, sequentialBiproductProductIso_hom_π_π_assoc]

section Limits

variable [HasKernels C] [∀ i, HasLimit (A i)] [HasLimit (sequentialBiproduct A)]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse chosen-limit comparison preserves the limit-to-product edge. -/
theorem sequentialBiproductLimitIso_inv_comp_toProduct :
    (sequentialBiproductLimitIso A).inv ≫ sequentialLimitToProduct (sequentialBiproduct A) =
      biproduct.map (fun i => sequentialLimitToProduct (A i)) ≫
        (sequentialBiproductProductIso A).hom := by
  simp only [sequentialBiproductLimitIso, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, sequentialLimitKernelIso_inv_comp_toProduct]
  rw [sequentialBiproductKernelIso_hom_comp_ι]
  rw [← Category.assoc]
  apply (cancel_mono (sequentialBiproductProductIso A).hom).mpr
  apply biproduct.hom_ext
  intro i
  simp only [Category.assoc, biproduct.mapIso, Iso.symm_inv,
    biproduct.map_π, biproduct.map_π_assoc, sequentialLimitKernelIso_hom_ι]

set_option backward.isDefEq.respectTransparency false in
/-- Every given stage projection is preserved by the inverse limit comparison. -/
@[reassoc]
theorem sequentialBiproductLimitIso_inv_comp_π (n : ℕ) :
    (sequentialBiproductLimitIso A).inv ≫ limit.π (sequentialBiproduct A) (op n) =
      biproduct.map (fun i => limit.π (A i) (op n)) := by
  apply biproduct.hom_ext
  intro i
  have h := congrArg (fun g => g ≫
      Pi.π (fun n => (sequentialBiproduct A).obj (op n)) n ≫
        biproduct.π (fun i => (A i).obj (op n)) i)
    (sequentialBiproductLimitIso_inv_comp_toProduct (A := A))
  simpa only [Category.assoc, sequentialLimitToProduct_π_assoc,
    sequentialBiproductProductIso_hom_π_π, biproduct.map_π_assoc,
    sequentialLimitToProduct_π, biproduct.map_π] using h

set_option backward.isDefEq.respectTransparency false in
/-- Every summand stage projection is preserved by the forward limit comparison. -/
@[reassoc]
theorem sequentialBiproductLimitIso_hom_π_π (n : ℕ) (i : I) :
    (sequentialBiproductLimitIso A).hom ≫ biproduct.π (fun i => limit (A i)) i ≫
        limit.π (A i) (op n) =
      limit.π (sequentialBiproduct A) (op n) ≫
        biproduct.π (fun i => (A i).obj (op n)) i := by
  apply (cancel_epi (sequentialBiproductLimitIso A).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, sequentialBiproductLimitIso_inv_comp_π, biproduct.map_π]

end Limits

section LimitNaturality

variable [HasKernels C] [∀ i, HasLimit (A i)] [HasLimit (sequentialBiproduct A)]
  [∀ i, HasLimit (B i)] [HasLimit (sequentialBiproduct B)]

set_option backward.isDefEq.respectTransparency false in
/-- The chosen-limit comparisons are natural in given component tower maps. -/
theorem sequentialBiproductLimitIso_naturality (α : ∀ i, A i ⟶ B i) :
    limMap (sequentialBiproductMap α) ≫ (sequentialBiproductLimitIso B).hom =
      (sequentialBiproductLimitIso A).hom ≫ biproduct.map (fun i => limMap (α i)) := by
  apply biproduct.hom_ext
  intro i
  apply limit.hom_ext
  intro n
  cases n using Opposite.rec
  rename_i n
  have hm : (sequentialBiproductMap α).app (op n) ≫
      biproduct.π (fun i => (B i).obj (op n)) i =
    biproduct.π (fun i => (A i).obj (op n)) i ≫ (α i).app (op n) :=
    biproduct.map_π (fun i => (α i).app (op n)) i
  simp only [Category.assoc, biproduct.map_π_assoc, limMap_π,
    limMap_π_assoc, sequentialBiproductLimitIso_hom_π_π,
    sequentialBiproductLimitIso_hom_π_π_assoc]
  erw [hm]

end LimitNaturality

set_option backward.isDefEq.respectTransparency false in
/-- Inverse product interchange is natural in the given tower maps. -/
theorem sequentialBiproductProductIso_inv_naturality (α : ∀ i, A i ⟶ B i) :
    sequentialProductMap (sequentialBiproductMap α) ≫ (sequentialBiproductProductIso B).inv =
      (sequentialBiproductProductIso A).inv ≫
        biproduct.map (fun i => sequentialProductMap (α i)) := by
  have h := congrArg (fun g => (sequentialBiproductProductIso A).inv ≫ g ≫
      (sequentialBiproductProductIso B).inv)
    (sequentialBiproductProductIso_naturality α)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using h.symm

section LimOneNaturality

variable [HasCokernels C]

set_option backward.isDefEq.respectTransparency false in
/-- Concrete lim-one comparisons are natural in given component tower maps. -/
theorem sequentialBiproductLimOneIso_naturality (α : ∀ i, A i ⟶ B i) :
    sequentialLimOneMap (sequentialBiproductMap α) ≫ (sequentialBiproductLimOneIso B).hom =
      (sequentialBiproductLimOneIso A).hom ≫
        biproduct.map (fun i => sequentialLimOneMap (α i)) := by
  apply (cancel_epi (sequentialLimOneπ (sequentialBiproduct A))).mp
  rw [← Category.assoc, sequentialLimOneπ_comp_map, Category.assoc,
    sequentialLimOneπ_comp_biproductLimOneIso]
  rw [← Category.assoc, sequentialBiproductProductIso_inv_naturality, Category.assoc]
  erw [← Category.assoc (sequentialLimOneπ (sequentialBiproduct A))
    (sequentialBiproductLimOneIso A).hom
    (biproduct.map (fun i => sequentialLimOneMap (α i))),
    sequentialLimOneπ_comp_biproductLimOneIso]
  simp only [Category.assoc]
  apply congrArg (fun g => (sequentialBiproductProductIso A).inv ≫ g)
  apply biproduct.hom_ext
  intro i
  simp only [Category.assoc, biproduct.map_π, biproduct.map_π_assoc,
    sequentialLimOneπ_comp_map]

end LimOneNaturality

end CategoryTheory.Limits
