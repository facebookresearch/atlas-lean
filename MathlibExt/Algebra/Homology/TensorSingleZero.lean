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

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Monoidal
public import MathlibExt.Algebra.Homology.TensorHomFunctoriality
public import MathlibExt.Algebra.Homology.TensorUnitor

/-!
# Tensoring with a degree-zero single complex

For a preadditive monoidal category with a zero object, finite coproducts and additive tensor
variables, K ⊗ A[0] is canonically the complex with degree-n object K_n ⊗ A and differential
d_K ⊗ id_A.

The comparison is natural in both K and A and preserves the degree-(n,0) antidiagonal summand
through the canonical single-object chart.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [HasZeroObject C]
  [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]
  [HasFiniteCoproducts C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The tensor comparison with a degree-zero single complex.

Identify K ⊗ A[0] with the degreewise right-tensor functor applied to K. -/
noncomputable def tensorObjSingleZeroIso
    (K : ChainComplex C ℕ) (A : C) :
    tensorObj K ((ChainComplex.single₀ C).obj A) ≅
      (((tensoringRight C).obj A).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K := by
  let L := (ChainComplex.single₀ C).obj A
  let B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) :=
    (((curriedTensor C).mapBifunctorHomologicalComplex
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj K).obj L
  let T := (((tensoringRight C).obj A).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K
  let sourceIso (i j : ℕ) : (B.X i).X j ≅ K.X i ⊗ L.X j :=
    Iso.refl _
  let targetIso (n : ℕ) : T.X n ≅ K.X n ⊗ A :=
    Iso.refl _
  let homComponent : ∀ (n i j : ℕ) (_ : i + j = n),
      ((B.X i).X j ⟶ T.X n) := fun n i j h ↦ by
    if hj : j = 0 then
      subst j
      subst n
      exact (sourceIso i 0).hom ≫
        (𝟙 (K.X i) ⊗ₘ
          (singleObjXSelf (ComplexShape.down ℕ) 0 A).hom) ≫
        (targetIso i).inv
    else
      exact 0
  let homX : ∀ n : ℕ, (B.total (ComplexShape.down ℕ)).X n ⟶ T.X n := fun n ↦
    B.totalDesc (fun i j h ↦ homComponent n i j h)
  let invComponent : ∀ n : ℕ, T.X n ⟶ (B.X n).X 0 := fun n ↦ by
    exact (targetIso n).hom ≫
      (𝟙 (K.X n) ⊗ₘ
        (singleObjXSelf (ComplexShape.down ℕ) 0 A).inv) ≫
      (sourceIso n 0).inv
  let invX : ∀ n : ℕ, T.X n ⟶
      (B.total (ComplexShape.down ℕ)).X n := fun n ↦
    invComponent n ≫
      B.ιTotal (ComplexShape.down ℕ) n 0 n rfl
  let e : ∀ n : ℕ, (B.total (ComplexShape.down ℕ)).X n ≅ T.X n := fun n ↦
    { hom := homX n
      inv := invX n
      hom_inv_id := by
        apply HomologicalComplex₂.total.hom_ext
        intro i j h
        cases j with
        | zero =>
            have hi : i = n := h
            subst i
            have hh : h = rfl := Subsingleton.elim _ _
            cases hh
            dsimp only [homX, invX, invComponent]
            rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
            dsimp only [homComponent]
            rw [dite_eq_left rfl]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
            slice_lhs 2 3 =>
              rw [MonoidalCategory.tensorHom_comp_tensorHom,
                Category.comp_id, Iso.hom_inv_id,
                MonoidalCategory.id_tensorHom_id]
            slice_lhs 1 2 => rw [Category.comp_id]
            rw [Iso.hom_inv_id, Category.id_comp, Category.comp_id]
        | succ j =>
            exact ((tensorLeft (K.X i)).map_isZero
              (isZero_single_obj_X
                (ComplexShape.down ℕ) 0 A (j + 1)
                  (Nat.succ_ne_zero j))).eq_of_src _ _
      inv_hom_id := by
        dsimp only [homX, invX, invComponent]
        rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
        dsimp only [homComponent]
        rw [dite_eq_left rfl]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        slice_lhs 2 3 =>
          rw [MonoidalCategory.tensorHom_comp_tensorHom,
            Category.comp_id, Iso.inv_hom_id,
            MonoidalCategory.id_tensorHom_id]
        slice_lhs 1 2 => rw [Category.comp_id]
        rw [Iso.hom_inv_id] }
  exact Hom.isoOfComponents e (fun n n' hnn' ↦ by
    apply HomologicalComplex₂.total.hom_ext
    intro i j h
    cases j with
    | zero =>
        have hi : i = n := h
        subst i
        have hh : h = rfl := Subsingleton.elim _ _
        cases hh
        dsimp only [e, homX]
        rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
        conv_rhs => rw [← Category.assoc]
        rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
          HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
          Preadditive.add_comp]
        rw [B.d₂_eq_zero (ComplexShape.down ℕ) n 0 n' (by simp)]
        simp only [zero_comp, add_zero]
        rw [B.d₁_eq (ComplexShape.down ℕ) hnn' 0 n' rfl]
        have heps : ComplexShape.ε₁ (ComplexShape.down ℕ)
            (ComplexShape.down ℕ) (ComplexShape.down ℕ) (n, 0) = 1 := rfl
        rw [heps, one_smul, Category.assoc,
          HomologicalComplex₂.ι_totalDesc]
        dsimp only [homComponent]
        rw [dite_eq_left rfl, dite_eq_left rfl]
        have hSource :
            (B.d n n').f 0 ≫ (sourceIso n' 0).hom =
              (sourceIso n 0).hom ≫
                ((curriedTensor C).map (K.d n n')).app (L.X 0) := by
          dsimp only [sourceIso, B]
          simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
            Functor.mapBifunctorHomologicalComplex_obj_obj_d_f]
        have hTarget :
            (targetIso n).inv ≫ T.d n n' =
              ((tensoringRight C).obj A).map (K.d n n') ≫
                (targetIso n').inv := by
          dsimp only [targetIso, T]
          simp only [Iso.refl_inv, Functor.mapHomologicalComplex_obj_d]
          exact (Category.id_comp _).trans (Category.comp_id _).symm
        have hTensor :
            (𝟙 (K.X n) ⊗ₘ
                (singleObjXSelf (ComplexShape.down ℕ) 0 A).hom) ≫
                ((tensoringRight C).obj A).map (K.d n n') =
              ((curriedTensor C).map (K.d n n')).app (L.X 0) ≫
                (𝟙 (K.X n') ⊗ₘ
                  (singleObjXSelf (ComplexShape.down ℕ) 0 A).hom) := by
          simp only [Functor.flip_obj_map, curriedTensor_map_app,
            ← MonoidalCategory.tensorHom_id]
          rw [MonoidalCategory.tensorHom_comp_tensorHom,
            MonoidalCategory.tensorHom_comp_tensorHom]
          simp only [Category.id_comp, Category.comp_id]
        slice_lhs 3 4 => rw [hTarget]
        slice_lhs 2 3 => rw [hTensor]
        slice_rhs 1 2 => rw [hSource]
        simp only [Category.assoc]
    | succ j =>
        exact ((tensorLeft (K.X i)).map_isZero
          (isZero_single_obj_X
            (ComplexShape.down ℕ) 0 A (j + 1)
              (Nat.succ_ne_zero j))).eq_of_src _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-zero tensor comparison on its surviving summand.

The (n,0) coprojection followed by the comparison is id_{K_n} tensored with the single-complex
chart to A. -/
@[reassoc]
theorem ιTensorObj_comp_tensorObjSingleZeroIso_hom
    (K : ChainComplex C ℕ) (A : C) (n : ℕ) :
    ιTensorObj K ((ChainComplex.single₀ C).obj A) n 0 n rfl ≫
        (tensorObjSingleZeroIso K A).hom.f n =
      𝟙 (K.X n) ⊗ₘ
        (singleObjXSelf (ComplexShape.down ℕ) 0 A).hom := by
  unfold tensorObjSingleZeroIso
  dsimp only [Hom.isoOfComponents_hom_f]
  rw [HomologicalComplex₂.ι_totalDesc]
  dsimp
  cat_disch

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of the single-zero comparison in the chain complex.

A chain map f commutes with the tensor-single comparison and degreewise right tensoring by A. -/
@[reassoc]
theorem tensorObjSingleZeroIso_hom_naturality₁
    {K K' : ChainComplex C ℕ} (f : K ⟶ K') (A : C) :
    tensorHom f (𝟙 ((ChainComplex.single₀ C).obj A)) ≫
        (tensorObjSingleZeroIso K' A).hom =
      (tensorObjSingleZeroIso K A).hom ≫
        (((tensoringRight C).obj A).mapHomologicalComplex
          (ComplexShape.down ℕ)).map f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro i j h
  cases j with
  | zero =>
      have hi : i = n := h
      subst i
      have hh : h = rfl := Subsingleton.elim _ _
      cases hh
      simp only [comp_f]
      rw [ιTensorObj_tensorHom_assoc,
        ιTensorObj_comp_tensorObjSingleZeroIso_hom]
      rw [ιTensorObj_comp_tensorObjSingleZeroIso_hom_assoc]
      simp only [id_f, ChainComplex.single₀ObjXSelf, Iso.refl_hom,
        MonoidalCategory.id_tensorHom_id,
        Functor.mapHomologicalComplex_map_f]
      simp only [Category.id_comp, Category.comp_id,
        ChainComplex.single₀_obj_zero, Functor.flip_obj_map,
        curriedTensor_map_app, ← MonoidalCategory.tensorHom_id]
  | succ j =>
      exact ((tensorLeft (K.X i)).map_isZero
        (isZero_single_obj_X (ComplexShape.down ℕ) 0 A (j + 1)
          (Nat.succ_ne_zero j))).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of the single-zero comparison in the coefficient.

A morphism a : A → A′ commutes with the comparison and the corresponding degreewise tensor
transformation. -/
@[reassoc]
theorem tensorObjSingleZeroIso_hom_naturality₂
    (K : ChainComplex C ℕ) {A A' : C} (a : A ⟶ A') :
    tensorHom (𝟙 K) ((ChainComplex.single₀ C).map a) ≫
        (tensorObjSingleZeroIso K A').hom =
      (tensorObjSingleZeroIso K A).hom ≫
        (NatTrans.mapHomologicalComplex
          ((tensoringRight C).map a) (ComplexShape.down ℕ)).app K := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro i j h
  cases j with
  | zero =>
      have hi : i = n := h
      subst i
      have hh : h = rfl := Subsingleton.elim _ _
      cases hh
      simp only [comp_f]
      rw [ιTensorObj_tensorHom_assoc,
        ιTensorObj_comp_tensorObjSingleZeroIso_hom]
      rw [ιTensorObj_comp_tensorObjSingleZeroIso_hom_assoc]
      simp only [id_f, ChainComplex.single₀_map_f_zero,
        ChainComplex.single₀ObjXSelf, Iso.refl_hom,
        MonoidalCategory.id_tensorHom_id]
      simp only [Category.id_comp, Category.comp_id,
        NatTrans.mapHomologicalComplex_app_f, Functor.flip_map_app,
        curriedTensor_obj_map, ← MonoidalCategory.id_tensorHom]
  | succ j =>
      exact ((tensorLeft (K.X i)).map_isZero
        (isZero_single_obj_X (ComplexShape.down ℕ) 0 A (j + 1)
          (Nat.succ_ne_zero j))).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Joint naturality of the single-zero tensor comparison.

The tensor map of f and a[0] commutes with the comparison and the degreewise maps in both
variables. -/
@[reassoc]
theorem tensorObjSingleZeroIso_hom_naturality
    {K K' : ChainComplex C ℕ} (f : K ⟶ K')
    {A A' : C} (a : A ⟶ A') :
    tensorHom f ((ChainComplex.single₀ C).map a) ≫
        (tensorObjSingleZeroIso K' A').hom =
      (tensorObjSingleZeroIso K A).hom ≫
        (((tensoringRight C).obj A).mapHomologicalComplex
          (ComplexShape.down ℕ)).map f ≫
        (NatTrans.mapHomologicalComplex
          ((tensoringRight C).map a) (ComplexShape.down ℕ)).app K' := by
  have hsplit :
      tensorHom f ((ChainComplex.single₀ C).map a) =
        tensorHom f (𝟙 ((ChainComplex.single₀ C).obj A)) ≫
          tensorHom (𝟙 K') ((ChainComplex.single₀ C).map a) := by
    simpa only [Category.comp_id, Category.id_comp] using
      (HomologicalComplex.tensorHom_comp_tensorHom f (𝟙 K')
        (𝟙 ((ChainComplex.single₀ C).obj A))
        ((ChainComplex.single₀ C).map a)).symm
  rw [hsplit]
  slice_lhs 2 3 =>
    rw [tensorObjSingleZeroIso_hom_naturality₂]
  slice_lhs 1 2 =>
    rw [tensorObjSingleZeroIso_hom_naturality₁]
  simp only [Category.assoc]

end HomologicalComplex

end
