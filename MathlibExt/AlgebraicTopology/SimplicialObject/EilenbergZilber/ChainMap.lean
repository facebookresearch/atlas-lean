/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.TensorDifferentialDownNat
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleAlternating
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleDifferential

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Simplicial

namespace AlgebraicTopology.EilenbergZilber

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  (X Y : SimplicialObject C)
  [HomologicalComplex.HasTensor
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]

theorem shuffleComponent_comm (n : ℕ) :
    shuffleComponent X Y (n + 1) ≫
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj (X ⊗ Y)).d (n + 1) n =
      (HomologicalComplex.tensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)).d (n + 1) n ≫
        shuffleComponent X Y n := by
  ext p q h
  change p + q = n + 1 at h
  rw [ιTensorObj_comp_shuffleComponent_assoc]
  change _ =
    HomologicalComplex.ιTensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y) p q (n + 1) h ≫
      (HomologicalComplex.tensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)).d (n + 1) n ≫
      shuffleComponent X Y n
  conv_rhs => rw [← Category.assoc]
  rw [HomologicalComplex.ιTensorObj_comp_d_down_nat
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y) p q n h]
  simp only [Preadditive.add_comp]
  rcases p with _ | p
  · rcases q with _ | q
    · omega
    · have hn : n = 0 + q := by omega
      subst n
      have hh : h = rfl := Subsingleton.elim _ _
      cases hh
      simp only [dite_eq_left True.intro, dite_eq_right (Nat.succ_ne_zero q), Limits.zero_comp,
        zero_add, Nat.succ_sub_one, pow_zero, one_smul, Category.assoc,
        ιTensorObj_comp_shuffleComponent,
        AlgebraicTopology.alternatingFaceMapComplex_obj_d,
        AlgebraicTopology.alternatingFaceMapComplex_obj_X, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      exact shuffleBidegree_comp_objD_eq_tensor_differential_left_zero X Y q
  · rcases q with _ | q
    · have hn : n = p := by omega
      subst n
      have hh : h = rfl := Subsingleton.elim _ _
      cases hh
      simp only [dite_eq_right (Nat.succ_ne_zero p), dite_eq_left True.intro, Limits.zero_comp,
        add_zero, Nat.succ_sub_one, Category.assoc, ιTensorObj_comp_shuffleComponent,
        AlgebraicTopology.alternatingFaceMapComplex_obj_d,
        AlgebraicTopology.alternatingFaceMapComplex_obj_X, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      exact shuffleBidegree_comp_objD_eq_tensor_differential_right_zero X Y p
    · have hn : n = (p + 1) + q := by omega
      subst n
      have hh : h = rfl := Subsingleton.elim _ _
      cases hh
      simp only [dite_eq_right (Nat.succ_ne_zero p), dite_eq_right (Nat.succ_ne_zero q),
        Nat.succ_sub_one, Category.assoc, ιTensorObj_comp_shuffleComponent,
        Preadditive.zsmul_comp, AlgebraicTopology.alternatingFaceMapComplex_obj_d,
        AlgebraicTopology.alternatingFaceMapComplex_obj_X, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      exact shuffleBidegree_comp_objD_eq_tensor_differential_positive X Y p q

/-- The shuffle map on alternating-face complexes. -/
noncomputable def alternatingMap :
    HomologicalComplex.tensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y) ⟶
      (AlgebraicTopology.alternatingFaceMapComplex C).obj (X ⊗ Y) where
  f := shuffleComponent X Y
  comm' := fun {i j} hij ↦ by
    subst hij
    exact shuffleComponent_comm X Y j

@[simp]
theorem alternatingMap_f (n : ℕ) :
    (alternatingMap X Y).f n = shuffleComponent X Y n := rfl

@[reassoc]
theorem alternatingMap_naturality {X X₂ Y Y₂ : SimplicialObject C}
    (f : X ⟶ X₂) (g : Y ⟶ Y₂)
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X₂)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y₂)] :
    HomologicalComplex.tensorHom
        ((AlgebraicTopology.alternatingFaceMapComplex C).map f)
        ((AlgebraicTopology.alternatingFaceMapComplex C).map g) ≫
      alternatingMap X₂ Y₂ =
    alternatingMap X Y ≫
      (AlgebraicTopology.alternatingFaceMapComplex C).map (f ⊗ₘ g) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact shuffleComponent_naturality f g n

end AlgebraicTopology.EilenbergZilber
