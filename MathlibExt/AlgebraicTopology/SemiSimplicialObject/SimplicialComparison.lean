/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Portions of this file are adapted from:

`Mathlib/AlgebraicTopology/SimplicialObject/Homotopy.lean` (Mathlib):
Copyright (c) 2025 Fabian Odermatt. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Authors: Fabian Odermatt
Homotopy endpoint and face interfaces used by the semisimplicial restriction.

`Mathlib/AlgebraicTopology/SimplicialObject/ChainHomotopy.lean` (Mathlib):
Copyright (c) 2025 Fabian Odermatt. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Authors: Fabian Odermatt
Alternating prism formulas used in the chain-homotopy comparison.
-/
-- Adapter: @toskua
module

public import MathlibExt.AlgebraicTopology.SemiSimplicialObject.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.CategoryTheory.Whiskering

/-!
# Restricting simplicial homotopies to semisimplicial objects

Precomposition with the inclusion of order-preserving injections into the simplex category
restricts a simplicial object to a semisimplicial object and preserves all its faces. A
simplicial homotopy therefore restricts to the same degree-raising maps and endpoint and face
equations.

In a preadditive category, the alternating-face complex of the restriction is isomorphic to
the simplicial alternating-face complex by identity maps in every degree. These comparisons
are natural in simplicial morphisms. The restricted and simplicial homotopies have the same
adjacent chain-homotopy components, namely the negative alternating sums of their h_i.
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

/-- Let H be a simplicial homotopy between f, g : X ⟶ Y in a category C. Precomposing X, Y, f and
g with SemiSimplexCategory.toSimplexCategory.op gives semisimplicial objects and maps. The
same maps H.h i : X_n ⟶ Y_(n+1) satisfy the semisimplicial endpoint and face conditions,
defining a homotopy between the restricted f and g. -/
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

/-- Let H be a simplicial homotopy between f, g : X ⟶ Y in a preadditive category C. For every n :
ℕ, the component (n, n + 1) of the chain homotopy induced by its semisimplicial restriction
equals H.toChainHomotopy.hom n (n + 1). Both are the morphism −∑ i : Fin (n + 1), (−1)^i • H.h
i : X_n ⟶ Y_(n+1). -/
theorem toSemiSimplicial_toChainHomotopy_hom (H : Homotopy f g) (n : ℕ) :
    H.toSemiSimplicial.toChainHomotopy.hom n (n + 1) =
      H.toChainHomotopy.hom n (n + 1) := by
  rw [SemiSimplicialObject.Homotopy.toChainHomotopy_hom]
  simp only [toSemiSimplicial_h]
  exact (ToChainHomotopy.hom_eq H n).symm

end CategoryTheory.SimplicialObject.Homotopy

namespace AlgebraicTopology.SemiSimplicialAlternatingFaceMapComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- For a simplicial object X in a preadditive category C, the alternating-face complex of
SemiSimplexCategory.toSimplexCategory.op ⋙ X is isomorphic to the simplicial alternating-face
complex of X. Both complexes are indexed by down ℕ; the forward and inverse isomorphism
components in degree n are 𝟙 X_n, since their faces and alternating differentials agree. -/
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

/-- For a simplicial map f : X ⟶ Y in a preadditive category C, let e_X and e_Y be the
identity-component comparisons from the alternating-face complexes of the semisimplicial
restrictions to the simplicial complexes. Then map(restrict f) ≫ e_Y.hom = e_X.hom ≫ map f,
where the left map is semisimplicial alternating faces and the right map is simplicial
alternating faces. -/
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
