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

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Actual dual evaluation of a finite additive frame

Contravariant additive functors send the finite projection/injection identities
to inverse evaluation maps. The construction uses those maps directly.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ u₂ v₁ v₂ w
namespace CategoryTheory.DualFiniteFrame

/-- The opposite of the actual finite frame's total identity is its dual total
identity, with no condition on the index universe. -/
theorem finiteFrame_op_total {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    (I : Type w) [Fintype I] {A : C} (f : I → C)
    (ι : ∀ i, f i ⟶ A) (π : ∀ i, A ⟶ f i)
    (htotal : (∑ i, π i ≫ ι i) = 𝟙 A) :
    (∑ i, (ι i).op ≫ (π i).op) = 𝟙 (op A) := by
  apply Quiver.Hom.unop_inj
  simpa only [unop_sum, unop_comp, Quiver.Hom.unop_op, unop_id] using htotal

/-- A genuine finite frame gives a dual evaluation isomorphism for an additive
contravariant functor. Its hom and inverse are the actual projection/injection
maps, and the empty frame is included. -/
def finiteFrameDualEvaluationIso {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : Cᵒᵖ ⥤ D) [F.Additive] (I : Type w) [Fintype I]
    {A : C} (f : I → C) (g : I → D) [HasBiproduct g]
    (ι : ∀ i, f i ⟶ A) (π : ∀ i, A ⟶ f i)
    (hsame : ∀ i, ι i ≫ π i = 𝟙 (f i))
    (hdifferent : ∀ i j, i ≠ j → ι i ≫ π j = 0)
    (htotal : (∑ i, π i ≫ ι i) = 𝟙 A)
    (e : ∀ i, F.obj (op (f i)) ≅ g i) : F.obj (op A) ≅ ⨁ g where
  hom := biproduct.lift (fun i => F.map (ι i).op ≫ (e i).hom)
  inv := biproduct.desc (fun i => (e i).inv ≫ F.map (π i).op)
  hom_inv_id := by
    classical
    rw [biproduct.lift_desc]
    calc
      (∑ i, (F.map (ι i).op ≫ (e i).hom) ≫ ((e i).inv ≫ F.map (π i).op)) =
          ∑ i, F.map ((ι i).op ≫ (π i).op) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Category.assoc, Iso.hom_inv_id_assoc, F.map_comp]
      _ = F.map (∑ i, (ι i).op ≫ (π i).op) := (F.map_sum _ _).symm
      _ = 𝟙 _ := by rw [finiteFrame_op_total I f ι π htotal, F.map_id]
  inv_hom_id := by
    classical
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    rw [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π]
    simp only [Category.assoc]
    rw [← Category.assoc (F.map (π i).op), ← F.map_comp, ← op_comp]
    by_cases h : j = i
    · subst j
      rw [hsame]
      simp
    · rw [hdifferent j i h]
      simp [Ne.symm h]

/-- The dual evaluation isomorphism has the original generator values. -/
theorem finiteFrameDualEvaluationIso_hom_projection {C : Type u₁} [Category.{v₁} C]
    [Preadditive C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : Cᵒᵖ ⥤ D) [F.Additive] (I : Type w) [Fintype I]
    {A : C} (f : I → C) (g : I → D) [HasBiproduct g]
    (ι : ∀ i, f i ⟶ A) (π : ∀ i, A ⟶ f i)
    (hsame : ∀ i, ι i ≫ π i = 𝟙 (f i))
    (hdifferent : ∀ i j, i ≠ j → ι i ≫ π j = 0)
    (htotal : (∑ i, π i ≫ ι i) = 𝟙 A)
    (e : ∀ i, F.obj (op (f i)) ≅ g i) (i : I) :
    (finiteFrameDualEvaluationIso F I f g ι π hsame hdifferent htotal e).hom ≫ biproduct.π g i =
      F.map (ι i).op ≫ (e i).hom := biproduct.lift_π _ _

/-- An actual finite-biproduct presentation transports its frame before genuine
dual evaluation. The hom still uses the transported original injections. -/
def transportedFiniteFrameDualEvaluationIso {C : Type u₁} [Category.{v₁} C]
    [Preadditive C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : Cᵒᵖ ⥤ D) [F.Additive] (I : Type w) [Fintype I]
    {A : C} (f : I → C) [HasBiproduct f] (g : I → D) [HasBiproduct g]
    (frame : (⨁ f) ≅ A) (duals : ∀ i, F.obj (op (f i)) ≅ g i) :
    F.obj (op A) ≅ ⨁ g := by
  classical
  refine finiteFrameDualEvaluationIso F I f g
    (fun i => biproduct.ι f i ≫ frame.hom)
    (fun i => frame.inv ≫ biproduct.π f i) ?_ ?_ ?_ duals
  · intro i
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    simp
  · intro i j h
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    simp [h]
  · simp_rw [Category.assoc,
      ← Category.assoc (biproduct.π f _) (biproduct.ι f _) frame.hom]
    rw [← Preadditive.comp_sum, ← Preadditive.sum_comp, biproduct.total]
    simp

/-- The transported-frame dual hom retains direct precomposition by each
original transported injection. -/
theorem transportedFiniteFrameDualEvaluationIso_hom_projection
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : Cᵒᵖ ⥤ D) [F.Additive] (I : Type w) [Fintype I]
    {A : C} (f : I → C) [HasBiproduct f] (g : I → D) [HasBiproduct g]
    (frame : (⨁ f) ≅ A) (duals : ∀ i, F.obj (op (f i)) ≅ g i) (i : I) :
    (transportedFiniteFrameDualEvaluationIso F I f g frame duals).hom ≫ biproduct.π g i =
      F.map (biproduct.ι f i ≫ frame.hom).op ≫ (duals i).hom :=
  biproduct.lift_π _ _

/-- The transported-frame inverse is direct precomposition by the actual
transported original projection. -/
theorem transportedFiniteFrameDualEvaluationIso_inv_injection
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : Cᵒᵖ ⥤ D) [F.Additive] (I : Type w) [Fintype I]
    {A : C} (f : I → C) [HasBiproduct f] (g : I → D) [HasBiproduct g]
    (frame : (⨁ f) ≅ A) (duals : ∀ i, F.obj (op (f i)) ≅ g i) (i : I) :
    biproduct.ι g i ≫ (transportedFiniteFrameDualEvaluationIso F I f g frame duals).inv =
      (duals i).inv ≫ F.map (frame.inv ≫ biproduct.π f i).op :=
  biproduct.ι_desc _ _

end CategoryTheory.DualFiniteFrame
