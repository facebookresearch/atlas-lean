/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Subfunctor.Finite
public import Mathlib.CategoryTheory.Elements
public import Mathlib.SetTheory.Cardinal.Regular

/-! # Total-point cardinality of generated subpresheaves

The actual native category-of-elements points retain their original site objects
and values. Constructive orbit and union surjections preserve both coordinates;
their cardinal bounds control arbitrary native generated subfunctors, infinite
size envelopes and strictly small unions at a regular cardinal.

Source: the elementary fixed-site presheaf support calculation used in the
Hirschhorn localization/cardinality route. This module uses the native
Subfunctor, Elements and cardinal arithmetic APIs and assumes no model,
replacement, local-presentability or cellularity data.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Opposite Cardinal

namespace CategoryTheory.Subfunctor

variable {C : Type} [SmallCategory C] {F : Cᵒᵖ ⥤ Type u}

/-- The actual orbit surjection retains both original object and original image. -/
theorem exists_ofSection_elements_surjection {X : Cᵒᵖ} (x : F.obj X) :
    ∃ φ : ULift.{u} (Σ U : Cᵒᵖ, X ⟶ U) → (ofSection x).toFunctor.Elements,
      Function.Surjective φ ∧
        ∀ a, (φ a).obj = a.down.1 ∧ HEq (φ a).val.val (F.map a.down.2 x) := by
  let φ : ULift.{u} (Σ U : Cᵒᵖ, X ⟶ U) →
      (ofSection x).toFunctor.Elements := fun a =>
    Functor.elementsMk (ofSection x).toFunctor a.down.1
      ⟨F.map a.down.2 x, ⟨a.down.2, rfl⟩⟩
  have hφ : Function.Surjective φ := by
    intro e
    obtain ⟨f, hf⟩ := e.val.property
    refine ⟨ULift.up ⟨e.obj, f⟩, ?_⟩
    apply Functor.Elements.ext (φ (ULift.up ⟨e.obj, f⟩)) e rfl
    have hv : (φ (ULift.up ⟨e.obj, f⟩)).val = e.val := Subtype.ext hf
    simpa only [eqToHom_refl, Functor.map_id, types_id_apply] using hv
  refine ⟨φ, hφ, ?_⟩
  intro a
  exact ⟨rfl, HEq.rfl⟩

/-- The actual union surjection retains each original piece's object and point. -/
theorem exists_iSup_elements_surjection {ι : Type u} (S : ι → Subfunctor F) :
    ∃ φ : (Σ i : ι, (S i).toFunctor.Elements) → (⨆ i, S i).toFunctor.Elements,
      Function.Surjective φ ∧
        ∀ a, (φ a).obj = a.2.obj ∧ HEq (φ a).val.val a.2.val.val := by
  let φ : (Σ i : ι, (S i).toFunctor.Elements) →
      (⨆ i, S i).toFunctor.Elements := fun a =>
    Functor.elementsMk (⨆ i, S i).toFunctor a.2.obj
      ⟨a.2.val.val, by
        rw [iSup_obj]
        exact Set.mem_iUnion.mpr ⟨a.1, a.2.val.property⟩⟩
  have hφ : Function.Surjective φ := by
    intro e
    let y : F.obj e.obj := e.val.val
    have hy : y ∈ (⨆ i, S i).obj e.obj := e.val.property
    rw [iSup_obj] at hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    let z : (S i).toFunctor.Elements :=
      Functor.elementsMk (S i).toFunctor e.obj ⟨y, hi⟩
    refine ⟨⟨i, z⟩, ?_⟩
    apply Functor.Elements.ext (φ ⟨i, z⟩) e rfl
    have hv : (φ ⟨i, z⟩).val = e.val := Subtype.ext rfl
    simpa only [eqToHom_refl, Functor.map_id, types_id_apply] using hv
  refine ⟨φ, hφ, ?_⟩
  intro a
  exact ⟨rfl, HEq.rfl⟩

/-- All original generated points come from the actual outgoing site operators. -/
theorem mk_elements_ofSection_le {X : Cᵒᵖ} (x : F.obj X) :
    Cardinal.mk (ofSection x).toFunctor.Elements ≤
      Cardinal.mk (ULift.{u} (Σ U : Cᵒᵖ, X ⟶ U)) := by
  obtain ⟨φ, hφ, _⟩ := exists_ofSection_elements_surjection x
  exact Cardinal.mk_le_of_surjective hφ

/-- Total points of an actual indexed union come from its original pieces. -/
theorem mk_elements_iSup_le {ι : Type u} (S : ι → Subfunctor F) :
    Cardinal.mk (⨆ i, S i).toFunctor.Elements ≤
      Cardinal.mk (Σ i : ι, (S i).toFunctor.Elements) := by
  obtain ⟨φ, hφ, _⟩ := exists_iSup_elements_surjection S
  exact Cardinal.mk_le_of_surjective hφ

/-- Native arbitrary-family generation has the original index-times-operators bound. -/
theorem IsGeneratedBy.mk_elements_le {ι : Type u} {X : ι → Cᵒᵖ}
    {x : ∀ i, F.obj (X i)} {G : Subfunctor F} (h : G.IsGeneratedBy x) :
    Cardinal.mk G.toFunctor.Elements ≤
      Cardinal.mk ι * Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) := by
  have hOrbit (i : ι) :
      Cardinal.mk (ofSection (x i)).toFunctor.Elements ≤
        Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) := by
    refine (mk_elements_ofSection_le (x i)).trans ?_
    let ψ : ULift.{u} (Σ U : Cᵒᵖ, X i ⟶ U) →
        ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B) := fun a => ULift.up ⟨X i, a.down⟩
    apply Cardinal.mk_le_of_injective (f := ψ)
    intro a b hab
    apply ULift.ext
    exact sigma_mk_injective (β := fun A : Cᵒᵖ => Σ B : Cᵒᵖ, A ⟶ B)
      (congrArg ULift.down hab)
  rw [← h.iSup_eq]
  refine (mk_elements_iSup_le (fun i => ofSection (x i))).trans ?_
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun i => Cardinal.mk (ofSection (x i)).toFunctor.Elements) ≤
        Cardinal.sum (fun _ : ι =>
          Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B))) :=
      Cardinal.sum_le_sum _ _ hOrbit
    _ = Cardinal.mk ι * Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) :=
      Cardinal.sum_const' _ _

/-- An explicitly bounded original union stays within the same infinite cardinal. -/
theorem mk_elements_iSup_le_of_le {ι : Type u} (S : ι → Subfunctor F)
    {γ : Cardinal.{u}} (hγ : ℵ₀ ≤ γ) (hι : Cardinal.mk ι ≤ γ)
    (hS : ∀ i, Cardinal.mk (S i).toFunctor.Elements ≤ γ) :
    Cardinal.mk (⨆ i, S i).toFunctor.Elements ≤ γ := by
  refine (mk_elements_iSup_le S).trans ?_
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun i => Cardinal.mk (S i).toFunctor.Elements) ≤
        Cardinal.sum (fun _ : ι => γ) := Cardinal.sum_le_sum _ _ hS
    _ = Cardinal.mk ι * γ := Cardinal.sum_const' _ _
    _ ≤ γ := Cardinal.mul_le_of_le hγ hι le_rfl

/-- The same native generated subfunctor is bounded at any stable infinite envelope. -/
theorem IsGeneratedBy.mk_elements_le_of_le {ι : Type u} {X : ι → Cᵒᵖ}
    {x : ∀ i, F.obj (X i)} {G : Subfunctor F} (h : G.IsGeneratedBy x)
    {γ : Cardinal.{u}} (hγ : ℵ₀ ≤ γ) (hι : Cardinal.mk ι ≤ γ)
    (hOp : Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) ≤ γ) :
    Cardinal.mk G.toFunctor.Elements ≤ γ :=
  h.mk_elements_le.trans (Cardinal.mul_le_of_le hγ hι hOp)

/-- Regularity controls precisely the stated small index and small pieces. -/
theorem mk_elements_iSup_lt_of_isRegular {ι : Type u} (S : ι → Subfunctor F)
    {μ : Cardinal.{u}} (hμ : μ.IsRegular) (hι : Cardinal.mk ι < μ)
    (hS : ∀ i, Cardinal.mk (S i).toFunctor.Elements < μ) :
    Cardinal.mk (⨆ i, S i).toFunctor.Elements < μ := by
  refine (mk_elements_iSup_le S).trans_lt ?_
  rw [Cardinal.mk_sigma]
  exact Cardinal.sum_lt_of_isRegular hμ hι hS

/-- The product bound only needs an infinite comparison cardinal. -/
theorem IsGeneratedBy.mk_elements_lt {ι : Type u} {X : ι → Cᵒᵖ}
    {x : ∀ i, F.obj (X i)} {G : Subfunctor F} (h : G.IsGeneratedBy x)
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hι : Cardinal.mk ι < μ)
    (hOp : Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) < μ) :
    Cardinal.mk G.toFunctor.Elements < μ :=
  h.mk_elements_le.trans_lt (Cardinal.mul_lt_of_lt hμ hι hOp)

/-- All operators are counted; strict countable-site support requires μ above ω. -/
theorem IsGeneratedBy.mk_elements_lt_of_countable_operators
    [Countable (Σ A B : Cᵒᵖ, A ⟶ B)] {ι : Type u} {X : ι → Cᵒᵖ}
    {x : ∀ i, F.obj (X i)} {G : Subfunctor F} (h : G.IsGeneratedBy x)
    {μ : Cardinal.{u}} (hω : ℵ₀ < μ) (hι : Cardinal.mk ι < μ) :
    Cardinal.mk G.toFunctor.Elements < μ := by
  have hOp : Cardinal.mk (ULift.{u} (Σ A B : Cᵒᵖ, A ⟶ B)) ≤ ℵ₀ :=
    Cardinal.mk_le_aleph0
  exact h.mk_elements_lt hω.le hι (hOp.trans_lt hω)


end CategoryTheory.Subfunctor
