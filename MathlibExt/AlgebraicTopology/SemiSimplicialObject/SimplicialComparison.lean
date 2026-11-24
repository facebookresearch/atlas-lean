/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Copyright (c) 2025 Fabian Odermatt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: @toskua

This source adapts the native simplicial homotopy arguments by Fabian
Odermatt while retaining the existing semisimplicial model and complexes.
-/
module

public import MathlibExt.AlgebraicTopology.SemiSimplicialObject.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.CategoryTheory.Whiskering

/-!
# Full-simplicial forgetful and alternating-complex comparisons

Precompose with the semi-simplex inclusion. The h_i data and native
chain component signs are retained. Identity degree maps compare the two
alternating complexes and are natural in full simplicial morphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial BigOperators

universe v u

namespace CategoryTheory.SemiSimplicialObject

variable {C : Type u} [Category.{v} C]

@[simp]
theorem whiskerLeft_δ (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    SemiSimplicialObject.δ (SemiSimplexCategory.toSimplexCategory.op ⋙ X) i = X.δ i := by
  change (X.map ((SemiSimplexCategory.toSimplexCategory.map
    (SemiSimplexCategory.δ i)).op.unop).op : X _⦋n + 1⦌ ⟶ X _⦋n⦌) =
      X.map (SimplexCategory.δ i).op
  have hd : (SemiSimplexCategory.toSimplexCategory.map (SemiSimplexCategory.δ i)).op.unop =
      SimplexCategory.δ i :=
    (Quiver.Hom.unop_op _).trans (SemiSimplexCategory.toSimplexCategory_map_δ i)
  exact congrArg (fun d : ⦋n⦌ ⟶ ⦋n + 1⦌ => X.map d.op) hd

end CategoryTheory.SemiSimplicialObject

namespace CategoryTheory.SimplicialObject.Homotopy

variable {C : Type u} [Category.{v} C]
  {X Y : SimplicialObject C} {f g : X ⟶ Y}

/-- Forget the two degeneracy conditions by the semi-simplex inclusion. -/
def toSemiSimplicial (H : Homotopy f g) :
    SemiSimplicialObject.Homotopy
      (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op f)
      (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op g) where
  h i := H.h i
  h_zero_comp_δ_zero n := by
    change H.h (n := n) 0 ≫ Y.δ (n := n) 0 = g.app (op ⦋n⦌)
    exact H.h_zero_comp_δ_zero n
  h_last_comp_δ_last n := by
    change H.h (Fin.last n) ≫ Y.δ (Fin.last (n + 1)) = f.app (op ⦋n⦌)
    exact H.h_last_comp_δ_last n
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    change H.h j.succ ≫ Y.δ i.castSucc = X.δ i ≫ H.h j
    exact H.h_succ_comp_δ_castSucc_of_lt i j hij
  h_succ_comp_δ_castSucc_succ j := by
    change H.h j.succ ≫ Y.δ j.castSucc.succ = H.h j.castSucc ≫ Y.δ j.castSucc.succ
    exact H.h_succ_comp_δ_castSucc_succ j
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    change H.h j.castSucc ≫ Y.δ i.succ = X.δ i ≫ H.h j
    exact H.h_castSucc_comp_δ_succ_of_lt i j hji

@[simp]
theorem toSemiSimplicial_h (H : Homotopy f g) {n : ℕ} (i : Fin (n + 1)) :
    H.toSemiSimplicial.h i = H.h i := rfl

variable [Preadditive C]

/-- Forgetting preserves the native negative adjacent chain-homotopy component. -/
theorem toSemiSimplicial_toChainHomotopy_hom (H : Homotopy f g) (n : ℕ) :
    H.toSemiSimplicial.toChainHomotopy.hom n (n + 1) =
      H.toChainHomotopy.hom n (n + 1) := by
  rw [SemiSimplicialObject.Homotopy.toChainHomotopy_hom]
  simp only [toSemiSimplicial_h]
  exact (ToChainHomotopy.hom_eq H n).symm

end CategoryTheory.SimplicialObject.Homotopy

namespace AlgebraicTopology.SemiSimplicialAlternatingFaceMapComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The two alternating complexes compare by identity degree maps. -/
def ofSimplicialIso (X : SimplicialObject C) :
    (semiSimplicialAlternatingFaceMapComplex C).obj
        (SemiSimplexCategory.toSimplexCategory.op ⋙ X) ≅
      (alternatingFaceMapComplex C).obj X :=
  HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl (X _⦋n⦌)) (by
    intro i j hij
    change j + 1 = i at hij
    subst i
    change 𝟙 (X _⦋j + 1⦌) ≫
        ((alternatingFaceMapComplex C).obj X).d (j + 1) j =
      ((semiSimplicialAlternatingFaceMapComplex C).obj
        (SemiSimplexCategory.toSimplexCategory.op ⋙ X)).d (j + 1) j ≫ 𝟙 (X _⦋j⦌)
    simp only [semiSimplicialAlternatingFaceMapComplex_obj_d,
      alternatingFaceMapComplex_obj_d, objD, AlternatingFaceMapComplex.objD,
      SemiSimplicialObject.whiskerLeft_δ, Category.id_comp]
    exact (Category.comp_id _).symm)

@[simp]
theorem ofSimplicialIso_hom_f (X : SimplicialObject C) (n : ℕ) :
    (ofSimplicialIso X).hom.f n = 𝟙 (X _⦋n⦌) := by
  change (HomologicalComplex.Hom.isoOfComponents
    (C₁ := (semiSimplicialAlternatingFaceMapComplex C).obj
      (SemiSimplexCategory.toSimplexCategory.op ⋙ X))
    (C₂ := (alternatingFaceMapComplex C).obj X)
    (fun n => Iso.refl (X _⦋n⦌)) _).hom.f n = _
  rfl

@[simp]
theorem ofSimplicialIso_inv_f (X : SimplicialObject C) (n : ℕ) :
    (ofSimplicialIso X).inv.f n = 𝟙 (X _⦋n⦌) := by
  change (HomologicalComplex.Hom.isoOfComponents
    (C₁ := (semiSimplicialAlternatingFaceMapComplex C).obj
      (SemiSimplexCategory.toSimplexCategory.op ⋙ X))
    (C₂ := (alternatingFaceMapComplex C).obj X)
    (fun n => Iso.refl (X _⦋n⦌)) _).inv.f n = _
  rfl

/-- The chosen comparison commutes with every full simplicial map. -/
theorem ofSimplicialIso_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (semiSimplicialAlternatingFaceMapComplex C).map
        (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op f) ≫
        (ofSimplicialIso Y).hom =
      (ofSimplicialIso X).hom ≫ (alternatingFaceMapComplex C).map f := by
  apply HomologicalComplex.hom_ext
  intro n
  change f.app (op ⦋n⦌) ≫ 𝟙 (Y _⦋n⦌) = 𝟙 (X _⦋n⦌) ≫ f.app (op ⦋n⦌)
  simp only [Category.comp_id, Category.id_comp]

end AlgebraicTopology.SemiSimplicialAlternatingFaceMapComplex
