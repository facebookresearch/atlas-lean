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
# Contravariant evaluation of finite split frames

Let C,D be preadditive and F : Cᵒᵖ ⥤ D additive. A finite frame for A consists of objects f_i
and maps ι_i : f_i → A, π_i : A → f_i with ι_i ≫ π_i = id_{f_i}, ι_i ≫ π_j = 0 for i ≠ j and
Σ_i π_i ≫ ι_i = id_A. Given isomorphisms e_i : F(f_i) ≅ g_i and the biproduct of the g_i,
evaluation defines F(A) ≅ ⨁ᵢg_i.

The hom is the lift of F((ι_i).op) ≫ e_i.hom; its inverse is the descendant of e_i.inv ≫
F((π_i).op). Contravariance reverses the total frame identity and additivity preserves its
finite sum. A presentation ⨁ᵢf_i ≅ A transports the injections and projections before this
evaluation. Empty finite frames are included, and indexing, object and morphism universes
remain independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ u₂ v₁ v₂ w
namespace CategoryTheory.DualFiniteFrame

/-- Opposite total identity of a finite frame.

For a finite family f_i in a preadditive category and maps ι_i : f_i → A, π_i : A → f_i
satisfying Σ_i π_i ≫ ι_i = id_A, the opposite category satisfies Σ_i (ι_i).op ≫ (π_i).op =
id_{op A}. Taking opposites reverses each composition and preserves the finite additive sum. -/
theorem finiteFrame_op_total {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    (I : Type w) [Fintype I] {A : C} (f : I → C)
    (ι : ∀ i, f i ⟶ A) (π : ∀ i, A ⟶ f i)
    (htotal : (∑ i, π i ≫ ι i) = 𝟙 A) :
    (∑ i, (ι i).op ≫ (π i).op) = 𝟙 (op A) := by
  apply Quiver.Hom.unop_inj
  simpa only [unop_sum, unop_comp, Quiver.Hom.unop_op, unop_id] using htotal

/-- Evaluation isomorphism of a finite split frame.

Let F : Cᵒᵖ ⥤ D be additive between preadditive categories. Given a finite frame (ι_i,π_i) of
A with orthogonal splitting and total identity, component isomorphisms e_i : F(f_i) ≅ g_i and
the biproduct of g, form F(A) ≅ ⨁g. Its hom has components F((ι_i).op) ≫ e_i.hom and its
inverse has components e_i.inv ≫ F((π_i).op). The construction also covers an empty index
type. -/
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

/-- Projection equation for finite-frame evaluation.

For an additive contravariant functor F, a finite split frame of A and component
identifications e_i : F(f_i) ≅ g_i, the evaluation comparison E : F(A) ≅ ⨁g satisfies E.hom ≫
biproduct.π g i = F((ι_i).op) ≫ e_i.hom. -/
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

/-- Evaluation of a finite biproduct presentation.

Let frame : ⨁f ≅ A be a finite biproduct presentation in a preadditive category and F : Cᵒᵖ ⥤
D additive. With identifications F(f_i) ≅ g_i and the biproduct of g defined, transport the
frame by injections biproduct.ι f i ≫ frame.hom and projections frame.inv ≫ biproduct.π f i.
Their evaluation gives F(A) ≅ ⨁g. -/
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

/-- Projection formula for evaluation of a transported frame.

For a finite presentation frame : ⨁f ≅ A, additive contravariant F and component isomorphisms
e_i : F(f_i) ≅ g_i, the transported comparison E satisfies E.hom ≫ biproduct.π g i =
F((biproduct.ι f i ≫ frame.hom).op) ≫ e_i.hom. -/
theorem transportedFiniteFrameDualEvaluationIso_hom_projection
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : Cᵒᵖ ⥤ D) [F.Additive] (I : Type w) [Fintype I]
    {A : C} (f : I → C) [HasBiproduct f] (g : I → D) [HasBiproduct g]
    (frame : (⨁ f) ≅ A) (duals : ∀ i, F.obj (op (f i)) ≅ g i) (i : I) :
    (transportedFiniteFrameDualEvaluationIso F I f g frame duals).hom ≫ biproduct.π g i =
      F.map (biproduct.ι f i ≫ frame.hom).op ≫ (duals i).hom :=
  biproduct.lift_π _ _

/-- Injection formula for the inverse transported-frame evaluation.

For the evaluation E : F(A) ≅ ⨁g of a finite presentation frame : ⨁f ≅ A, biproduct.ι g i ≫
E.inv = e_i.inv ≫ F((frame.inv ≫ biproduct.π f i).op). Thus its inverse is defined by the
transported projection maps under the additive contravariant functor F. -/
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
