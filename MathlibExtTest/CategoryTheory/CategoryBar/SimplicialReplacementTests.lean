/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.CategoryBar.SimplicialReplacement

/-!
# Simplicial replacement public contract

Compile-level pins for the terminal-coefficient replacement types,
degree-zero description, coefficient/index maps, and mixed naturality.
-/

open CategoryTheory Opposite

universe u v uL

namespace MathlibExtTest.CategoryBar.SimplicialReplacementTests

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {E : Type u} [Category.{v} E]
variable {L L' L'' : C ⥤ Type uL}
variable {T : D ⥤ Type uL}
variable {V : E ⥤ Type uL}
variable {L₁ L₂ : C ⥤ Type uL} {T₁ T₂ : D ⥤ Type uL}

example : Cᵒᵖ ⥤ Type 0 :=
  CategoryBar.replUnit C

example (n : ℕ) : Type (max u v uL) :=
  CategoryBar.replObj C L n

noncomputable example : SimplicialObject.Data (Type (max u v uL)) :=
  CategoryBar.simplicialReplacementData L

noncomputable example : SSet.{max u v uL} :=
  CategoryBar.simplicialReplacement L

example (F : ComposableArrows C 0) (l : L.obj F.left)
    (r : (CategoryBar.replUnit C).obj (op F.right)) :
    CategoryBar.replObjZeroEquiv L (⟨F, l, r⟩ : CategoryBar.replObj C L 0) =
      ⟨F.obj 0, l⟩ :=
  CategoryBar.replObjZeroEquiv_apply F l r

example (X : C) (l : L.obj X) :
    (CategoryBar.replObjZeroEquiv L).symm (⟨X, l⟩ : Σ X : C, L.obj X) =
      (⟨ComposableArrows.mk₀ X, l, PUnit.unit⟩ : CategoryBar.replObj C L 0) := by
  simpa using CategoryBar.replObjZeroEquiv_symm_apply X l

example (α : L ⟶ L') {n : ℕ} (F : ComposableArrows C n)
    (l : L.obj F.left) (r : (CategoryBar.replUnit C).obj (op F.right)) :
    CategoryBar.replCoeffMap α (⟨F, l, r⟩ : CategoryBar.replObj C L n) =
      (⟨F, α.app F.left l, r⟩ : CategoryBar.replObj C L' n) := by
  simpa using CategoryBar.replCoeffMap_mk α F l r

example (α : L ⟶ L') (β : L' ⟶ L'') :
    CategoryBar.replMap α ≫ CategoryBar.replMap β =
      CategoryBar.replMap (α ≫ β) :=
  CategoryBar.replMap_comp α β

example (Φ : C ⥤ D) (α : L ⟶ Φ ⋙ T) {n : ℕ}
    (x : CategoryBar.replObj C L n) :
    CategoryBar.barChain (CategoryBar.replIdxMap Φ α x) =
      (Φ.mapComposableArrows n).obj (CategoryBar.barChain x) :=
  CategoryBar.replIdxMap_chain Φ α x

example (Φ : C ⥤ D) (Ψ : D ⥤ E) (α : L ⟶ Φ ⋙ T) (β : T ⟶ Ψ ⋙ V) :
    CategoryBar.replIdxMapSSet Φ α ≫ CategoryBar.replIdxMapSSet Ψ β =
      CategoryBar.replIdxMapSSet (Φ ⋙ Ψ) (CategoryBar.compIdxL Φ Ψ α β) :=
  CategoryBar.replIdxMapSSet_comp Φ Ψ α β

example (Φ : C ⥤ D) (γ : L₁ ⟶ L₂) (δ : T₁ ⟶ T₂)
    (α : L₁ ⟶ Φ ⋙ T₁) (α' : L₂ ⟶ Φ ⋙ T₂)
    (h : γ ≫ α' = α ≫ Functor.whiskerLeft Φ δ) {n : ℕ}
    (x : CategoryBar.replObj C L₁ n) :
    CategoryBar.replCoeffMap δ (CategoryBar.replIdxMap Φ α x) =
      CategoryBar.replIdxMap Φ α' (CategoryBar.replCoeffMap γ x) := by
  simpa using CategoryBar.replCoeff_idx_mixed Φ γ δ α α' h x

end MathlibExtTest.CategoryBar.SimplicialReplacementTests
