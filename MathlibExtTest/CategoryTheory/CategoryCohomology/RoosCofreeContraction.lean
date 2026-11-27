/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import MathlibExt.CategoryTheory.CategoryCohomology.RoosCofreeContraction

/-!
# Cofree Roos contraction clients

The clients evaluate terminal insertion at the identity coefficient slot,
the degree-zero coefficient-product splitting and reconstruction on the
augmentation kernel. Positive-degree clients check cycle-to-boundary
factorization with the individual homology-existence hypothesis.
-/

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryCohomology

universe v₁ v₂ u₁ u₂

namespace RoosCofreeContractionTests

local instance (priority := 100) roosCofreeClientCoefficientProducts
    {J : Type u₁} [Category.{v₁} J]
    {B : Type u₂} [Category.{v₂} B] [HasProducts.{max u₁ v₁} B] :
    HasProductsOfShape J B :=
  (Limits.hasProducts_shrink.{u₁, v₁, v₂, u₂} (C := B)) J

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [HasProducts.{max u₁ v₁} A]
  (V : Discrete I ⥤ A)

local notation "RV" => Functor.obj (discreteCofreeFunctor (I := I) A) V

/-- A nonidentity outgoing arrow is inserted before the actual old chain. -/
example {i₁ i₀ j : I} (g : i₁ ⟶ i₀) (f : i₀ ⟶ j) :
    roosCofreeExtraCodegeneracy V 1 ≫ roosπ RV (ComposableArrows.mk₁ g.op) ≫
        discreteCofreeπ A V i₀ ⟨j, f⟩ =
      roosπ RV (ComposableArrows.mk₂ f.op g.op) ≫
        discreteCofreeπ A V j ⟨j, 𝟙 j⟩ :=
  roosCofreeExtraCodegeneracy_π V (ComposableArrows.mk₁ g.op) ⟨j, f⟩

/-- Repetition/evaluation permits cancellation of the actual degree-zero section. -/
example {Z : A} (u v : Z ⟶ ∏ᶜ fun j : I ↦ V.obj (Discrete.mk j))
    (h : u ≫ roosCofreeSection V = v ≫ roosCofreeSection V) : u = v := by
  let P : A := ∏ᶜ (fun j : I ↦ V.obj (Discrete.mk j))
  let X : A := (roosCosimplicial RV).obj (SimplexCategory.mk 0)
  let s : P ⟶ X := roosCofreeSection V
  let r : X ⟶ P := roosCofreeRetraction V
  have hs : u ≫ s = v ≫ s := h
  have hsr : s ≫ r = 𝟙 P := roosCofreeSection_retraction V
  calc
    u = u ≫ 𝟙 P := (Category.comp_id _).symm
    _ = u ≫ (s ≫ r) := congrArg (fun k => u ≫ k) hsr.symm
    _ = (u ≫ s) ≫ r := (Category.assoc _ _ _).symm
    _ = (v ≫ s) ≫ r := congrArg (fun k => k ≫ r) hs
    _ = v ≫ (s ≫ r) := Category.assoc _ _ _
    _ = v ≫ 𝟙 P := congrArg (fun k => v ≫ k) hsr
    _ = v := Category.comp_id _

section Preadditive

variable [Preadditive A]

/-- The actual differential reconstructs a zero-augmentation degree-zero morphism. -/
example {Z : A} (u : Z ⟶ (roosComplex RV).X 0)
    (hu : u ≫ roosCofreeRetraction V = 0) :
    u ≫ (roosComplex RV).d 0 1 ≫ roosCofreeExtraCodegeneracy V 0 = u := by
  let X₀ : A := (roosCosimplicial RV).obj (SimplexCategory.mk 0)
  let X₁ : A := (roosCosimplicial RV).obj (SimplexCategory.mk 1)
  let P : A := ∏ᶜ (fun j : I ↦ V.obj (Discrete.mk j))
  let u₀ : Z ⟶ X₀ := u
  let d : X₀ ⟶ X₁ := (roosComplex RV).d 0 1
  let e : X₁ ⟶ X₀ := roosCofreeExtraCodegeneracy V 0
  let r : X₀ ⟶ P := roosCofreeRetraction V
  let s : P ⟶ X₀ := roosCofreeSection V
  have hur : u₀ ≫ r = 0 := hu
  have hz : u₀ ≫ (r ≫ s) = 0 :=
    (Category.assoc u₀ r s).symm.trans
      ((congrArg (fun k : Z ⟶ P => k ≫ s) hur).trans zero_comp)
  have hd : d ≫ e = 𝟙 X₀ - r ≫ s := roosCofree_d_zero_extra V
  change u₀ ≫ d ≫ e = u₀
  calc
    u₀ ≫ d ≫ e = u₀ ≫ (𝟙 X₀ - r ≫ s) := congrArg (fun k => u₀ ≫ k) hd
    _ = u₀ ≫ 𝟙 X₀ - u₀ ≫ (r ≫ s) := by rw [Preadditive.comp_sub]
    _ = u₀ - 0 := by rw [Category.comp_id, hz]
    _ = u₀ := sub_zero _

/-- Every positive cocycle factors through the actual previous differential. -/
example {Z : A} (n : ℕ) (u : Z ⟶ (roosComplex RV).X (n + 1))
    (hu : u ≫ (roosComplex RV).d (n + 1) (n + 2) = 0) :
    u ≫ roosCofreeExtraCodegeneracy V n ≫ (roosComplex RV).d n (n + 1) = u := by
  let X₀ : A := (roosCosimplicial RV).obj (SimplexCategory.mk n)
  let X₁ : A := (roosCosimplicial RV).obj (SimplexCategory.mk (n + 1))
  let X₂ : A := (roosCosimplicial RV).obj (SimplexCategory.mk (n + 2))
  let u₁ : Z ⟶ X₁ := u
  let d₀ : X₀ ⟶ X₁ := (roosComplex RV).d n (n + 1)
  let d₁ : X₁ ⟶ X₂ := (roosComplex RV).d (n + 1) (n + 2)
  let e₀ : X₁ ⟶ X₀ := roosCofreeExtraCodegeneracy V n
  let e₁ : X₂ ⟶ X₁ := roosCofreeExtraCodegeneracy V (n + 1)
  have hud : u₁ ≫ d₁ = 0 := hu
  have hz : u₁ ≫ (d₁ ≫ e₁) = 0 :=
    (Category.assoc u₁ d₁ e₁).symm.trans
      ((congrArg (fun k : Z ⟶ X₂ => k ≫ e₁) hud).trans zero_comp)
  have hc : d₁ ≫ e₁ + e₀ ≫ d₀ = 𝟙 X₁ := roosCofree_d_succ_extra V n
  have h : u₁ ≫ (d₁ ≫ e₁ + e₀ ≫ d₀) = u₁ :=
    (congrArg (fun k => u₁ ≫ k) hc).trans (Category.comp_id _)
  change u₁ ≫ e₀ ≫ d₀ = u₁
  have h' : u₁ ≫ (d₁ ≫ e₁) + u₁ ≫ (e₀ ≫ d₀) = u₁ := by
    simpa only [Preadditive.comp_add] using h
  exact (zero_add (u₁ ≫ (e₀ ≫ d₀))).symm.trans
    ((congrArg (fun k => k + u₁ ≫ (e₀ ≫ d₀)) hz).symm.trans h')

/-- The same cycle factorization detects positive exactness using only local homology. -/
example (n : ℕ) [(roosComplex RV).HasHomology (n + 1)]
    {Z : A} (u : Z ⟶ (roosComplex RV).homology (n + 1)) : u = 0 :=
  (isZero_roosCofree_homology_succ V n).eq_zero_of_tgt u

end Preadditive

end RoosCofreeContractionTests

end
