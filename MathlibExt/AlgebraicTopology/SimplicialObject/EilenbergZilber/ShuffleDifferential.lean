/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleDifferential.Maps
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryLeft.Signs
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryRight.Signs

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber

open CategoryTheory Simplicial SimplexCategory

open scoped BigOperators MonoidalCategory

set_option backward.isDefEq.respectTransparency false

private lemma sum_tensor_id {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [(MonoidalCategory.curriedTensor C).Additive] {A B D : C} {J : Type*} [Fintype J]
    (f : J → (A ⟶ B)) :
    ((∑ j, f j) ⊗ₘ 𝟙 D) = ∑ j, f j ⊗ₘ 𝟙 D := by
  simp_rw [MonoidalCategory.tensorHom_id]
  have h := Functor.map_sum (MonoidalCategory.curriedTensor C) f Finset.univ
  have h' := congrArg (fun α ↦ α.app D) h
  simpa only [MonoidalCategory.curriedTensor_map_app, NatTrans.app_sum] using h'

private lemma id_tensor_sum {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [∀ Z : C, ((MonoidalCategory.curriedTensor C).obj Z).Additive]
    {A B D : C} {J : Type*} [Fintype J] (g : J → (B ⟶ D)) :
    (𝟙 A ⊗ₘ (∑ j, g j)) = ∑ j, 𝟙 A ⊗ₘ g j := by
  simp_rw [MonoidalCategory.id_tensorHom]
  exact Functor.map_sum ((MonoidalCategory.curriedTensor C).obj A) g Finset.univ

private lemma zsmul_tensor_id {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [(MonoidalCategory.curriedTensor C).Additive] {A B D : C} (r : ℤ) (f : A ⟶ B) :
    (r • f) ⊗ₘ 𝟙 D = r • (f ⊗ₘ 𝟙 D) := by
  simp_rw [MonoidalCategory.tensorHom_id]
  have h := Functor.map_zsmul (MonoidalCategory.curriedTensor C) (f := f) (r := r)
  have h' := congrArg (fun α ↦ α.app D) h
  simpa only [MonoidalCategory.curriedTensor_map_app, NatTrans.app_zsmul] using h'

private lemma id_tensor_zsmul {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [∀ Z : C, ((MonoidalCategory.curriedTensor C).obj Z).Additive]
    {A B D : C} (r : ℤ) (g : B ⟶ D) :
    𝟙 A ⊗ₘ (r • g) = r • (𝟙 A ⊗ₘ g) := by
  simp_rw [MonoidalCategory.id_tensorHom]
  exact Functor.map_zsmul ((MonoidalCategory.curriedTensor C).obj A) (f := g) (r := r)

private noncomputable def shuffleBoundaryTermPositive {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] (X Y : SimplicialObject C) (p q : ℕ)
    (s : Shuffle (p + 1) (q + 1)) (i : Fin ((p + 1) + (q + 1) + 1)) :
    X.obj (Opposite.op ⦋p + 1⦌) ⊗ Y.obj (Opposite.op ⦋q + 1⦌) ⟶
      (X ⊗ Y).obj (Opposite.op ⦋(p + 1) + q⦌) :=
  ((-1 : ℤ) ^ i.val) • (MonoidalCategory.tensorHom (X.map s.leftHom.op) (Y.map s.rightHom.op) ≫
    eqToHom (by rfl) ≫ (X ⊗ Y).δ (Fin.cast (by omega) i))

private theorem shuffleBoundaryTermPositive_partner {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] (X Y : SimplicialObject C) (p q : ℕ)
    (x : Shuffle.MixedFace (p + 1) (q + 1)) :
    shuffleBoundaryTermPositive X Y p q x.partner.shuffle x.partner.faceIndex =
      shuffleBoundaryTermPositive X Y p q x.shuffle x.faceIndex := by
  simp only [shuffleBoundaryTermPositive, Shuffle.MixedFace.partner_faceIndex, eqToHom_refl,
    Category.id_comp]
  congr 1
  have hδ : (X ⊗ Y).δ (n := (p + 1) + q) (Fin.cast (by omega) x.faceIndex) =
      MonoidalCategory.tensorHom (X.δ (n := (p + 1) + q) (Fin.cast (by omega) x.faceIndex))
        (Y.δ (n := (p + 1) + q) (Fin.cast (by omega) x.faceIndex)) := rfl
  rw [hδ]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom]
  exact mixedFace_tensor_map_eq X Y x

private theorem shuffleBidegree_comp_objD_eq_boundary_sum_positive {C : Type*} [Category C]
    [Preadditive C] [MonoidalCategory C] (X Y : SimplicialObject C) (p q : ℕ) :
    shuffleBidegree X Y (p + 1) (q + 1) ≫
      AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) ((p + 1) + q) =
    ∑ z : Shuffle (p + 1) (q + 1) × Fin ((p + 1) + (q + 1) + 1),
      ((-1 : ℤ) ^ z.2.val) •
        (shuffleSummand X Y z.1 ≫
          (X ⊗ Y).δ (n := (p + 1) + q) (Fin.cast (by omega) z.2)) := by
  unfold shuffleBidegree AlgebraicTopology.AlternatingFaceMapComplex.objD
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.comp_zsmul, Finset.smul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro z _
  rfl

private theorem shuffleBidegree_comp_objD_eq_signed_boundary_sum_positive {C : Type*} [Category C]
    [Preadditive C] [MonoidalCategory C] (X Y : SimplicialObject C) (p q : ℕ) :
    shuffleBidegree X Y (p + 1) (q + 1) ≫
      AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) ((p + 1) + q) =
    ∑ z : Shuffle (p + 1) (q + 1) × Fin ((p + 1) + (q + 1) + 1),
      shuffleSignZ z.1 • shuffleBoundaryTermPositive X Y p q z.1 z.2 := by
  rw [shuffleBidegree_comp_objD_eq_boundary_sum_positive]
  apply Finset.sum_congr rfl
  intro z _
  simp only [shuffleBoundaryTermPositive, shuffleSummand, Preadditive.zsmul_comp, smul_smul,
    eqToHom_refl, Category.id_comp]
  congr 1
  ring

private theorem shuffleBidegree_comp_objD_eq_nonmixed_sum_positive {C : Type*} [Category C]
    [Preadditive C] [MonoidalCategory C] (X Y : SimplicialObject C) (p q : ℕ) :
    shuffleBidegree X Y (p + 1) (q + 1) ≫
      AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) ((p + 1) + q) =
    ∑ z ∈ Shuffle.nonmixedBoundaryFaces (p + 1) (q + 1),
      shuffleSignZ z.1 • shuffleBoundaryTermPositive X Y p q z.1 z.2 := by
  rw [shuffleBidegree_comp_objD_eq_signed_boundary_sum_positive]
  exact Shuffle.sum_boundary_eq_sum_nonmixedBoundaryFaces
    (shuffleBoundaryTermPositive X Y p q) (shuffleBoundaryTermPositive_partner X Y p q)

private theorem shuffleBidegree_comp_objD_eq_boundary_sums_positive {C : Type*} [Category C]
    [Preadditive C] [MonoidalCategory C] (X Y : SimplicialObject C) (p q : ℕ) :
    shuffleBidegree X Y (p + 1) (q + 1) ≫
      AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) ((p + 1) + q) =
    (∑ x : Fin (p + 2) × Shuffle p (q + 1),
      shuffleSignZ (Shuffle.leftBoundaryPair x).1 •
        shuffleBoundaryTermPositive X Y p q (Shuffle.leftBoundaryPair x).1
          (Shuffle.leftBoundaryPair x).2) +
    (∑ x : Fin (q + 2) × Shuffle (p + 1) q,
      shuffleSignZ (Shuffle.rightBoundaryPair x).1 •
        shuffleBoundaryTermPositive X Y p q (Shuffle.rightBoundaryPair x).1
          (Shuffle.rightBoundaryPair x).2) := by
  rw [shuffleBidegree_comp_objD_eq_nonmixed_sum_positive]
  exact Shuffle.sum_nonmixedBoundaryFaces_positive
    (fun s i => shuffleSignZ s • shuffleBoundaryTermPositive X Y p q s i)

private theorem simplicialDelta_transport {C : Type*} [Category C]
    (X : SimplicialObject C) (n m : ℕ) (h : n = m) (i : Fin (n + 2)) :
    eqToHom (by rw [h]) ≫ X.δ (n := m) (Fin.cast (by omega) i) ≫
        eqToHom (by rw [h]) =
      X.δ (n := n) i := by
  subst m
  simp

private theorem leftBoundaryShuffle_left_map_transport {C : Type*} [Category C]
    (X : SimplicialObject C) (p q : ℕ) (t : Shuffle p (q + 1)) (a : Fin (p + 2)) :
    X.map (Shuffle.leftBoundaryShuffle t a).leftHom.op ≫
        X.δ (n := (p + 1) + q)
          (Fin.cast (by omega) (Shuffle.leftBoundaryIndex t a)) =
      (X.δ a ≫ X.map t.leftHom.op) ≫
        eqToHom (by rw [show p + (q + 1) = (p + 1) + q by omega]) := by
  let i : Fin (((p + 1) + q) + 2) :=
    Fin.cast (by omega) (Shuffle.leftBoundaryIndex t a)
  have ht := simplicialDelta_transport X ((p + 1) + q) (p + (q + 1)) (by omega) i
  rw [← ht]
  simp only [Category.assoc]
  simpa only [i, Fin.cast_cast, Category.assoc] using
    congrArg (fun f => f ≫
      eqToHom (by rw [show p + (q + 1) = (p + 1) + q by omega]))
      (leftBoundaryShuffle_left_map X t a)

private theorem leftBoundaryShuffle_right_map_transport {C : Type*} [Category C]
    (X : SimplicialObject C) (p q : ℕ) (t : Shuffle p (q + 1)) (a : Fin (p + 2)) :
    X.map (Shuffle.leftBoundaryShuffle t a).rightHom.op ≫
        X.δ (n := (p + 1) + q)
          (Fin.cast (by omega) (Shuffle.leftBoundaryIndex t a)) =
      X.map t.rightHom.op ≫
        eqToHom (by rw [show p + (q + 1) = (p + 1) + q by omega]) := by
  let i : Fin (((p + 1) + q) + 2) :=
    Fin.cast (by omega) (Shuffle.leftBoundaryIndex t a)
  have ht := simplicialDelta_transport X ((p + 1) + q) (p + (q + 1)) (by omega) i
  rw [← ht]
  simpa only [i, Fin.cast_cast, Category.assoc] using
    congrArg (fun f => f ≫
      eqToHom (by rw [show p + (q + 1) = (p + 1) + q by omega]))
      (leftBoundaryShuffle_right_map X t a)

private theorem shuffleBoundaryTermPositive_rightBoundary {C : Type*} [Category C]
    [Preadditive C] [MonoidalCategory C] (X Y : SimplicialObject C) (p q : ℕ)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) :
    shuffleSignZ (Shuffle.rightBoundaryShuffle t b) •
        shuffleBoundaryTermPositive X Y p q (Shuffle.rightBoundaryShuffle t b)
          (Shuffle.rightBoundaryIndex t b) =
      (((-1 : ℤ) ^ (p + 1 + b.val)) * shuffleSignZ t) •
        (MonoidalCategory.tensorHom (X.map t.leftHom.op)
            (Y.δ b ≫ Y.map t.rightHom.op) ≫ eqToHom (by rfl)) := by
  simp only [shuffleBoundaryTermPositive, smul_smul, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  rw [mul_comm]
  rw [Shuffle.shuffleSignZ_rightBoundaryShuffle t b]
  congr 1
  have hδ : (X ⊗ Y).δ (n := (p + 1) + q)
        (Fin.cast (by omega) (Shuffle.rightBoundaryIndex t b)) =
      MonoidalCategory.tensorHom
        (X.δ (n := (p + 1) + q) (Fin.cast (by omega) (Shuffle.rightBoundaryIndex t b)))
        (Y.δ (n := (p + 1) + q) (Fin.cast (by omega) (Shuffle.rightBoundaryIndex t b))) := rfl
  rw [hδ]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom]
  exact congrArg₂ MonoidalCategory.tensorHom (rightBoundaryShuffle_left_map X t b)
    (rightBoundaryShuffle_right_map Y t b)

private theorem shuffleBoundaryTermPositive_leftBoundary {C : Type*} [Category C]
    [Preadditive C] [MonoidalCategory C] (X Y : SimplicialObject C) (p q : ℕ)
    (t : Shuffle p (q + 1)) (a : Fin (p + 2)) :
    shuffleSignZ (Shuffle.leftBoundaryShuffle t a) •
        shuffleBoundaryTermPositive X Y p q (Shuffle.leftBoundaryShuffle t a)
          (Shuffle.leftBoundaryIndex t a) =
      (((-1 : ℤ) ^ a.val) * shuffleSignZ t) •
        (MonoidalCategory.tensorHom (X.δ a ≫ X.map t.leftHom.op)
            (Y.map t.rightHom.op) ≫
          eqToHom (by
            rw [show p + (q + 1) = (p + 1) + q by omega]
            exact (CategoryTheory.Monoidal.FunctorCategory.tensorObj_obj
              (F := X) (G := Y) (X := Opposite.op ⦋(p + 1) + q⦌)).symm)) := by
  simp only [shuffleBoundaryTermPositive, smul_smul, eqToHom_refl, Category.id_comp]
  rw [mul_comm]
  rw [Shuffle.shuffleSignZ_leftBoundaryShuffle]
  congr 1
  have hδ : (X ⊗ Y).δ (n := (p + 1) + q)
        (Fin.cast (by omega) (Shuffle.leftBoundaryIndex t a)) =
      MonoidalCategory.tensorHom
        (X.δ (n := (p + 1) + q) (Fin.cast (by omega) (Shuffle.leftBoundaryIndex t a)))
        (Y.δ (n := (p + 1) + q) (Fin.cast (by omega) (Shuffle.leftBoundaryIndex t a))) := rfl
  rw [hδ]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom]
  rw [leftBoundaryShuffle_left_map_transport X p q t a,
    leftBoundaryShuffle_right_map_transport Y p q t a]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  congr 1
  simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_eqToHom,
    MonoidalCategory.eqToHom_whiskerRight, eqToHom_trans]

public theorem shuffleBidegree_comp_objD_eq_tensor_differential_positive
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [(MonoidalCategory.curriedTensor C).Additive]
    [∀ Z : C, ((MonoidalCategory.curriedTensor C).obj Z).Additive]
    (X Y : SimplicialObject C) (p q : ℕ) :
    shuffleBidegree X Y (p + 1) (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) ((p + 1) + q) =
      ((AlgebraicTopology.AlternatingFaceMapComplex.objD X p ⊗ₘ
            𝟙 (Y.obj (Opposite.op ⦋q + 1⦌))) ≫
          shuffleBidegree X Y p (q + 1) ≫
          eqToHom (by rw [show p + (q + 1) = (p + 1) + q by omega])) +
        ((-1 : ℤ) ^ (p + 1)) •
          ((𝟙 (X.obj (Opposite.op ⦋p + 1⦌)) ⊗ₘ
              AlgebraicTopology.AlternatingFaceMapComplex.objD Y q) ≫
            shuffleBidegree X Y (p + 1) q) := by
  rw [shuffleBidegree_comp_objD_eq_boundary_sums_positive]
  congr 1
  · rw [Fintype.sum_prod_type]
    simp_rw [Shuffle.leftBoundaryPair, shuffleBoundaryTermPositive_leftBoundary]
    unfold AlgebraicTopology.AlternatingFaceMapComplex.objD shuffleBidegree shuffleSummand
    rw [sum_tensor_id]
    simp_rw [zsmul_tensor_id]
    simp only [Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, smul_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    · rw [mul_comm]
    · rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
      simp
  · rw [Fintype.sum_prod_type]
    simp_rw [Shuffle.rightBoundaryPair, shuffleBoundaryTermPositive_rightBoundary]
    unfold AlgebraicTopology.AlternatingFaceMapComplex.objD shuffleBidegree shuffleSummand
    rw [id_tensor_sum]
    simp_rw [id_tensor_zsmul]
    simp only [Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id, eqToHom_refl, smul_smul, Finset.smul_sum]
    simp_rw [pow_add]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    ring

private noncomputable def shuffleBoundaryTermRightZero {C : Type*} [Category C]
    [Preadditive C] [MonoidalCategory C] (X Y : SimplicialObject C) (p : ℕ)
    (s : Shuffle (p + 1) 0) (i : Fin ((p + 1) + 0 + 1)) :
    X.obj (Opposite.op ⦋p + 1⦌) ⊗ Y.obj (Opposite.op ⦋0⦌) ⟶
      (X ⊗ Y).obj (Opposite.op ⦋p⦌) :=
  ((-1 : ℤ) ^ i.val) •
    (MonoidalCategory.tensorHom (X.map s.leftHom.op) (Y.map s.rightHom.op) ≫
      eqToHom (by rfl) ≫ (X ⊗ Y).δ (n := p) (Fin.cast (by omega) i))

private theorem shuffleBidegree_comp_objD_eq_boundary_sum_right_zero
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    (X Y : SimplicialObject C) (p : ℕ) :
    shuffleBidegree X Y (p + 1) 0 ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) p =
      ∑ z : Shuffle (p + 1) 0 × Fin ((p + 1) + 0 + 1),
        ((-1 : ℤ) ^ z.2.val) •
          (shuffleSummand X Y z.1 ≫
            (X ⊗ Y).δ (n := p) (Fin.cast (by omega) z.2)) := by
  unfold shuffleBidegree AlgebraicTopology.AlternatingFaceMapComplex.objD
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.comp_zsmul, Finset.smul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro z _
  rfl

private theorem shuffleBidegree_comp_objD_eq_signed_boundary_sum_right_zero
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    (X Y : SimplicialObject C) (p : ℕ) :
    shuffleBidegree X Y (p + 1) 0 ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) p =
      ∑ z : Shuffle (p + 1) 0 × Fin ((p + 1) + 0 + 1),
        shuffleSignZ z.1 • shuffleBoundaryTermRightZero X Y p z.1 z.2 := by
  rw [shuffleBidegree_comp_objD_eq_boundary_sum_right_zero]
  apply Finset.sum_congr rfl
  intro z _
  simp only [shuffleBoundaryTermRightZero, shuffleSummand, Preadditive.zsmul_comp,
    smul_smul, eqToHom_refl, Category.id_comp]
  congr 1
  ring

private theorem shuffleBidegree_comp_objD_eq_left_boundary_sum_right_zero
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    (X Y : SimplicialObject C) (p : ℕ) :
    shuffleBidegree X Y (p + 1) 0 ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) p =
      ∑ x : Fin (p + 2) × Shuffle p 0,
        shuffleSignZ (Shuffle.leftBoundaryPair x).1 •
          shuffleBoundaryTermRightZero X Y p (Shuffle.leftBoundaryPair x).1
            (Shuffle.leftBoundaryPair x).2 := by
  rw [shuffleBidegree_comp_objD_eq_signed_boundary_sum_right_zero]
  have hnonmixed : Shuffle.nonmixedBoundaryFaces (p + 1) 0 = Finset.univ := by
    ext z
    simp only [Shuffle.nonmixedBoundaryFaces, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    exact Shuffle.isLeftBoundary_not_isMixedBoundary
      (Shuffle.isLeftBoundary_of_right_zero z.1 z.2)
  have h := Shuffle.sum_nonmixedBoundaryFaces_right_zero
    (fun s i => shuffleSignZ s • shuffleBoundaryTermRightZero X Y p s i)
  simpa only [hnonmixed, Finset.sum_filter, Finset.sum_const_zero, add_zero] using h

private theorem shuffleBoundaryTermRightZero_leftBoundary {C : Type*} [Category C]
    [Preadditive C] [MonoidalCategory C] (X Y : SimplicialObject C) (p : ℕ)
    (t : Shuffle p 0) (a : Fin (p + 2)) :
    shuffleSignZ (Shuffle.leftBoundaryShuffle t a) •
        shuffleBoundaryTermRightZero X Y p (Shuffle.leftBoundaryShuffle t a)
          (Shuffle.leftBoundaryIndex t a) =
      ((-1 : ℤ) ^ a.val) •
        ((X.δ a ⊗ₘ 𝟙 (Y.obj (Opposite.op ⦋0⦌))) ≫ shuffleSummand X Y t) := by
  simp only [shuffleBoundaryTermRightZero, shuffleSummand, Preadditive.comp_zsmul,
    smul_smul, eqToHom_refl, Category.id_comp]
  rw [mul_comm]
  rw [Shuffle.shuffleSignZ_leftBoundaryShuffle]
  congr 1
  have hδ : (X ⊗ Y).δ (n := p)
        (Fin.cast (by omega) (Shuffle.leftBoundaryIndex t a)) =
      MonoidalCategory.tensorHom
        (X.δ (n := p) (Fin.cast (by omega) (Shuffle.leftBoundaryIndex t a)))
        (Y.δ (n := p) (Fin.cast (by omega) (Shuffle.leftBoundaryIndex t a))) := rfl
  rw [hδ]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom]
  exact congrArg₂ MonoidalCategory.tensorHom
    (by simpa using leftBoundaryShuffle_left_map X t a)
    (by simpa using leftBoundaryShuffle_right_map Y t a)

public theorem shuffleBidegree_comp_objD_eq_tensor_differential_right_zero
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [(MonoidalCategory.curriedTensor C).Additive]
    (X Y : SimplicialObject C) (p : ℕ) :
    shuffleBidegree X Y (p + 1) 0 ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) p =
      (AlgebraicTopology.AlternatingFaceMapComplex.objD X p ⊗ₘ
          𝟙 (Y.obj (Opposite.op ⦋0⦌))) ≫ shuffleBidegree X Y p 0 := by
  rw [shuffleBidegree_comp_objD_eq_left_boundary_sum_right_zero]
  rw [Fintype.sum_prod_type]
  simp_rw [Shuffle.leftBoundaryPair, shuffleBoundaryTermRightZero_leftBoundary]
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD shuffleBidegree
  rw [sum_tensor_id]
  simp_rw [zsmul_tensor_id]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp]
  rw [Finset.sum_comm]

private noncomputable def shuffleBoundaryTermLeftZero {C : Type*} [Category C]
    [Preadditive C] [MonoidalCategory C] (X Y : SimplicialObject C) (q : ℕ)
    (s : Shuffle 0 (q + 1)) (i : Fin (0 + (q + 1) + 1)) :
    X.obj (Opposite.op ⦋0⦌) ⊗ Y.obj (Opposite.op ⦋q + 1⦌) ⟶
      (X ⊗ Y).obj (Opposite.op ⦋0 + q⦌) :=
  ((-1 : ℤ) ^ i.val) •
    (MonoidalCategory.tensorHom (X.map s.leftHom.op) (Y.map s.rightHom.op) ≫
      (X ⊗ Y).δ (n := 0 + q) (Fin.cast (by omega) i))

private theorem shuffleBidegree_comp_objD_eq_boundary_sum_left_zero
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    (X Y : SimplicialObject C) (q : ℕ) :
    shuffleBidegree X Y 0 (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) (0 + q) =
      ∑ z : Shuffle 0 (q + 1) × Fin (0 + (q + 1) + 1),
        ((-1 : ℤ) ^ z.2.val) •
          (shuffleSummand X Y z.1 ≫
            (X ⊗ Y).δ (n := 0 + q) (Fin.cast (by omega) z.2)) := by
  unfold shuffleBidegree AlgebraicTopology.AlternatingFaceMapComplex.objD
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.comp_zsmul, Finset.smul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro z _
  rfl

private theorem shuffleBidegree_comp_objD_eq_signed_boundary_sum_left_zero
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    (X Y : SimplicialObject C) (q : ℕ) :
    shuffleBidegree X Y 0 (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) (0 + q) =
      ∑ z : Shuffle 0 (q + 1) × Fin (0 + (q + 1) + 1),
        shuffleSignZ z.1 • shuffleBoundaryTermLeftZero X Y q z.1 z.2 := by
  rw [shuffleBidegree_comp_objD_eq_boundary_sum_left_zero]
  apply Finset.sum_congr rfl
  intro z _
  simp only [shuffleBoundaryTermLeftZero, shuffleSummand, Preadditive.zsmul_comp,
    smul_smul]
  congr 1
  ring

private theorem shuffleBidegree_comp_objD_eq_right_boundary_sum_left_zero
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    (X Y : SimplicialObject C) (q : ℕ) :
    shuffleBidegree X Y 0 (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) (0 + q) =
      ∑ x : Fin (q + 2) × Shuffle 0 q,
        shuffleSignZ (Shuffle.rightBoundaryPair x).1 •
          shuffleBoundaryTermLeftZero X Y q (Shuffle.rightBoundaryPair x).1
            (Shuffle.rightBoundaryPair x).2 := by
  rw [shuffleBidegree_comp_objD_eq_signed_boundary_sum_left_zero]
  have hnonmixed : Shuffle.nonmixedBoundaryFaces 0 (q + 1) = Finset.univ := by
    ext z
    simp only [Shuffle.nonmixedBoundaryFaces, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    exact Shuffle.isRightBoundary_not_isMixedBoundary
      (Shuffle.isRightBoundary_of_left_zero z.1 z.2)
  have h := Shuffle.sum_nonmixedBoundaryFaces_left_zero
    (fun s i => shuffleSignZ s • shuffleBoundaryTermLeftZero X Y q s i)
  simpa only [hnonmixed, Finset.sum_filter, Finset.sum_const_zero, add_zero] using h

private theorem shuffleBoundaryTermLeftZero_rightBoundary {C : Type*} [Category C]
    [Preadditive C] [MonoidalCategory C] (X Y : SimplicialObject C) (q : ℕ)
    (t : Shuffle 0 q) (b : Fin (q + 2)) :
    shuffleSignZ (Shuffle.rightBoundaryShuffle t b) •
        shuffleBoundaryTermLeftZero X Y q (Shuffle.rightBoundaryShuffle t b)
          (Shuffle.rightBoundaryIndex t b) =
      ((-1 : ℤ) ^ b.val) •
        ((𝟙 (X.obj (Opposite.op ⦋0⦌)) ⊗ₘ Y.δ b) ≫ shuffleSummand X Y t) := by
  simp only [shuffleBoundaryTermLeftZero, shuffleSummand, Preadditive.comp_zsmul,
    smul_smul]
  rw [mul_comm]
  rw [Shuffle.shuffleSignZ_rightBoundaryShuffle]
  simp only [zero_add]
  congr 1
  have hδ : (X ⊗ Y).δ (n := 0 + q)
        (Fin.cast (by omega) (Shuffle.rightBoundaryIndex t b)) =
      MonoidalCategory.tensorHom
        (X.δ (n := 0 + q) (Fin.cast (by omega) (Shuffle.rightBoundaryIndex t b)))
        (Y.δ (n := 0 + q) (Fin.cast (by omega) (Shuffle.rightBoundaryIndex t b))) := rfl
  rw [hδ]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom]
  exact congrArg₂ MonoidalCategory.tensorHom
    (by simpa using rightBoundaryShuffle_left_map X t b)
    (by simpa using rightBoundaryShuffle_right_map Y t b)

public theorem shuffleBidegree_comp_objD_eq_tensor_differential_left_zero
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [∀ Z : C, ((MonoidalCategory.curriedTensor C).obj Z).Additive]
    (X Y : SimplicialObject C) (q : ℕ) :
    shuffleBidegree X Y 0 (q + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) (0 + q) =
      (𝟙 (X.obj (Opposite.op ⦋0⦌)) ⊗ₘ
          AlgebraicTopology.AlternatingFaceMapComplex.objD Y q) ≫
        shuffleBidegree X Y 0 q := by
  rw [shuffleBidegree_comp_objD_eq_right_boundary_sum_left_zero]
  rw [Fintype.sum_prod_type]
  simp_rw [Shuffle.rightBoundaryPair, shuffleBoundaryTermLeftZero_rightBoundary]
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD shuffleBidegree
  rw [id_tensor_sum]
  simp_rw [id_tensor_zsmul]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp]
  rw [Finset.sum_comm]

end AlgebraicTopology.EilenbergZilber
