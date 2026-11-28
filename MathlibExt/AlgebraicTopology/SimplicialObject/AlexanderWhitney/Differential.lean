/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.TensorDifferentialDownNat
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.Alternating
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.Crossover
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.FaceComposition

@[expose] public section

universe v u w

open CategoryTheory Limits MonoidalCategory Simplicial SimplexCategory

namespace AlgebraicTopology.AlexanderWhitney

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  (X Y : SimplicialObject C)
  [HomologicalComplex.HasTensor
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]

omit [∀ Z : C, ((curriedTensor C).obj Z).Additive] in
private lemma sum_tensor_id {A B D : C} {J : Type w} [Fintype J]
    (f : J → (A ⟶ B)) :
    ((∑ j, f j) ⊗ₘ 𝟙 D) = ∑ j, f j ⊗ₘ 𝟙 D := by
  simp_rw [tensorHom_id]
  have h := Functor.map_sum (curriedTensor C) f Finset.univ
  have h' := congrArg (fun α ↦ α.app D) h
  simpa only [curriedTensor_map_app, NatTrans.app_sum] using h'

omit [(curriedTensor C).Additive] in
private lemma id_tensor_sum {A B D : C} {J : Type w} [Fintype J]
    (g : J → (B ⟶ D)) :
    (𝟙 A ⊗ₘ (∑ j, g j)) = ∑ j, 𝟙 A ⊗ₘ g j := by
  simp_rw [id_tensorHom]
  exact Functor.map_sum ((curriedTensor C).obj A) g Finset.univ

omit [∀ Z : C, ((curriedTensor C).obj Z).Additive] in
private lemma zsmul_tensor_id {A B D : C} (r : ℤ) (f : A ⟶ B) :
    (r • f) ⊗ₘ 𝟙 D = r • (f ⊗ₘ 𝟙 D) := by
  simp_rw [tensorHom_id]
  have h := Functor.map_zsmul (curriedTensor C) (f := f) (r := r)
  have h' := congrArg (fun α ↦ α.app D) h
  simpa only [curriedTensor_map_app, NatTrans.app_zsmul] using h'

omit [(curriedTensor C).Additive] in
private lemma id_tensor_zsmul {A B D : C} (r : ℤ) (g : B ⟶ D) :
    𝟙 A ⊗ₘ (r • g) = r • (𝟙 A ⊗ₘ g) := by
  simp_rw [id_tensorHom]
  exact Functor.map_zsmul ((curriedTensor C).obj A) (f := g) (r := r)

private lemma zsmul_sum {A : Type w} [AddCommGroup A] {J : Type*} [Fintype J]
    (r : ℤ) (f : J → A) : r • (∑ j, f j) = ∑ j, r • f j :=
  map_sum (DistribSMul.toAddMonoidHom A r) f Finset.univ

private lemma alternatingComponent_comp_d_eq_bidegree_sum (n : ℕ) :
    alternatingComponent X Y (n + 1) ≫
        (HomologicalComplex.tensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)).d
            (n + 1) n =
      ∑ p : Fin (n + 2),
        (let KX := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
         let KY := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
         let q := n + 1 - p.val
         have h : p.val + q = n + 1 := by omega
         (frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
           ((if hp : p.val = 0 then
               (0 : KX.X p.val ⊗ KY.X q ⟶
                 (HomologicalComplex.tensorObj KX KY).X n)
             else
               (KX.d p.val (p.val - 1) ⊗ₘ 𝟙 (KY.X q)) ≫
                 HomologicalComplex.ιTensorObj KX KY
                   (p.val - 1) q n (by omega)) +
            (if hq : q = 0 then
               (0 : KX.X p.val ⊗ KY.X q ⟶
                 (HomologicalComplex.tensorObj KX KY).X n)
             else
               ((-1 : ℤ) ^ p.val) •
                 ((𝟙 (KX.X p.val) ⊗ₘ KY.d q (q - 1)) ≫
                   HomologicalComplex.ιTensorObj KX KY
                     p.val (q - 1) n (by omega))))) := by
  let KX := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
  let KY := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
  change (∑ p : Fin (n + 2),
      let q := n + 1 - p.val
      have h : p.val + q = n + 1 := by omega
      (frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
        HomologicalComplex.ιTensorObj KX KY p.val q (n + 1) h) ≫
        (HomologicalComplex.tensorObj KX KY).d (n + 1) n = _
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  dsimp only
  rw [Category.assoc, HomologicalComplex.ιTensorObj_comp_d_down_nat]

private lemma d_comp_alternatingComponent_eq_tensor_double_sum (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj (X ⊗ Y)).d
          (n + 1) n ≫ alternatingComponent X Y n =
      ∑ i : Fin (n + 2),
        ∑ p : Fin (n + 1),
          (let q := n - p.val
           have h : p.val + q = n := by omega
           ((-1 : ℤ) ^ i.val) •
             ((X.δ i ⊗ₘ Y.δ i) ≫
               ((frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
                 HomologicalComplex.ιTensorObj
                   ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                   ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                   p.val q n h))) := by
  let KX := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
  let KY := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  change (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • (X ⊗ Y).δ i) ≫
      (∑ p : Fin (n + 1),
        let q := n - p.val
        have h : p.val + q = n := by omega
        (frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
          HomologicalComplex.ιTensorObj KX KY p.val q n h) = _
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Preadditive.zsmul_comp]
  rfl

private lemma horizontal_term_congr (n p q q' : ℕ) (hqq : q = q')
    (h : (p + 1) + q = n + 1) (h' : (p + 1) + q' = n + 1)
    (hLow : p + q = n) (hLow' : p + q' = n) :
    (frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
        ((((AlgebraicTopology.alternatingFaceMapComplex C).obj X).d (p + 1) p ⊗ₘ
          𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).X q)) ≫
          HomologicalComplex.ιTensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            p q n hLow) =
      (frontFace (C := C) X h' ⊗ₘ backFace (C := C) Y h') ≫
        ((((AlgebraicTopology.alternatingFaceMapComplex C).obj X).d (p + 1) p ⊗ₘ
          𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).X q')) ≫
          HomologicalComplex.ιTensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            p q' n hLow') := by
  subst q'
  rfl

private lemma vertical_term_congr (n p qh ql qh' ql' : ℕ)
    (hh : qh = qh') (hl : ql = ql')
    (h : p + qh = n + 1) (h' : p + qh' = n + 1)
    (hLow : p + ql = n) (hLow' : p + ql' = n) :
    ((-1 : ℤ) ^ p) •
        ((frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
          ((𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p) ⊗ₘ
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).d qh ql) ≫
            HomologicalComplex.ιTensorObj
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
              p ql n hLow)) =
      ((-1 : ℤ) ^ p) •
        ((frontFace (C := C) X h' ⊗ₘ backFace (C := C) Y h') ≫
          ((𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p) ⊗ₘ
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).d qh' ql') ≫
            HomologicalComplex.ιTensorObj
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
              p ql' n hLow')) := by
  subst qh'
  subst ql'
  rfl

private lemma horizontal_outer_normalize (n : ℕ) :
    let KX := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
    let KY := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
    (∑ p : Fin (n + 2),
      let q := n + 1 - p.val
      have h : p.val + q = n + 1 := by omega
      (frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
        (if hp : p.val = 0 then
          (0 : KX.X p.val ⊗ KY.X q ⟶
            (HomologicalComplex.tensorObj KX KY).X n)
        else
          (KX.d p.val (p.val - 1) ⊗ₘ 𝟙 (KY.X q)) ≫
            HomologicalComplex.ιTensorObj KX KY
              (p.val - 1) q n (by omega))) =
    ∑ p : Fin (n + 1),
      let q := n - p.val
      have h : (p.val + 1) + q = n + 1 := by omega
      have hLow : p.val + q = n := by omega
      (frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
        ((KX.d (p.val + 1) p.val ⊗ₘ 𝟙 (KY.X q)) ≫
          HomologicalComplex.ιTensorObj KX KY p.val q n hLow) := by
  let KX := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
  let KY := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
  let f := fun p : Fin (n + 2) =>
    let q := n + 1 - p.val
    have h : p.val + q = n + 1 := by omega
    (frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
      (if hp : p.val = 0 then
        (0 : KX.X p.val ⊗ KY.X q ⟶
          (HomologicalComplex.tensorObj KX KY).X n)
      else
        (KX.d p.val (p.val - 1) ⊗ₘ 𝟙 (KY.X q)) ≫
          HomologicalComplex.ιTensorObj KX KY
            (p.val - 1) q n (by omega))
  change (∑ p, f p) = _
  rw [Fin.sum_univ_succ]
  have hf0 : f 0 = 0 := by
    dsimp [f]
    simp only [CategoryTheory.Limits.comp_zero]
  rw [hf0, zero_add]
  apply Finset.sum_congr rfl
  intro p _
  have hp : (Fin.succ p).val ≠ 0 := by simp
  dsimp [f]
  apply horizontal_term_congr (C := C) X Y n p.val
      (n + 1 - (p.val + 1)) (n - p.val)
  omega

private lemma vertical_outer_normalize (n : ℕ) :
    let KX := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
    let KY := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
    (∑ p : Fin (n + 2),
      let q := n + 1 - p.val
      have h : p.val + q = n + 1 := by omega
      (frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
        (if hq : q = 0 then
          (0 : KX.X p.val ⊗ KY.X q ⟶
            (HomologicalComplex.tensorObj KX KY).X n)
        else
          ((-1 : ℤ) ^ p.val) •
            ((𝟙 (KX.X p.val) ⊗ₘ KY.d q (q - 1)) ≫
              HomologicalComplex.ιTensorObj KX KY
                p.val (q - 1) n (by omega)))) =
    ∑ p : Fin (n + 1),
      let q := n - p.val
      have h : p.val + (q + 1) = n + 1 := by omega
      have hLow : p.val + q = n := by omega
      ((-1 : ℤ) ^ p.val) •
        ((frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
          ((𝟙 (KX.X p.val) ⊗ₘ KY.d (q + 1) q) ≫
            HomologicalComplex.ιTensorObj KX KY p.val q n hLow)) := by
  let KX := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
  let KY := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
  let g := fun p : Fin (n + 2) =>
    let q := n + 1 - p.val
    have h : p.val + q = n + 1 := by omega
    (frontFace (C := C) X h ⊗ₘ backFace (C := C) Y h) ≫
      (if hq : q = 0 then
        (0 : KX.X p.val ⊗ KY.X q ⟶
          (HomologicalComplex.tensorObj KX KY).X n)
      else
        ((-1 : ℤ) ^ p.val) •
          ((𝟙 (KX.X p.val) ⊗ₘ KY.d q (q - 1)) ≫
            HomologicalComplex.ιTensorObj KX KY
              p.val (q - 1) n (by omega)))
  change (∑ p, g p) = _
  rw [Fin.sum_univ_castSucc]
  have hglast : g (Fin.last (n + 1)) = 0 := by
    dsimp [g]
    simp only [Nat.sub_self, dite_eq_left, CategoryTheory.Limits.comp_zero]
  rw [hglast, add_zero]
  apply Finset.sum_congr rfl
  intro p _
  have hq : n + 1 - p.val ≠ 0 := by omega
  dsimp [g]
  rw [dite_eq_right hq, Preadditive.comp_zsmul]
  apply vertical_term_congr (C := C) X Y n p.val
      (n + 1 - p.val) (n + 1 - p.val - 1)
      (n - p.val + 1) (n - p.val)
  all_goals omega

private lemma horizontal_face_split (p q n : ℕ) (hLow : p + q = n) :
    (frontFace (C := C) X (show (p + 1) + q = n + 1 by omega) ⊗ₘ
        backFace (C := C) Y (show (p + 1) + q = n + 1 by omega)) ≫
      ((((AlgebraicTopology.alternatingFaceMapComplex C).obj X).d (p + 1) p ⊗ₘ
          𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).X q)) ≫
        HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y) p q n hLow) =
      (∑ j : Fin (p + 1),
        ((-1 : ℤ) ^ j.val) •
          ((frontFace (C := C) X (show (p + 1) + q = n + 1 by omega) ⊗ₘ
              backFace (C := C) Y (show (p + 1) + q = n + 1 by omega)) ≫
            ((X.δ (Fin.castSucc j) ⊗ₘ
                𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).X q)) ≫
              HomologicalComplex.ιTensorObj
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                p q n hLow))) +
      ((-1 : ℤ) ^ (p + 1)) •
        ((frontFace (C := C) X (show (p + 1) + q = n + 1 by omega) ⊗ₘ
            backFace (C := C) Y (show (p + 1) + q = n + 1 by omega)) ≫
          ((X.δ (⟨p + 1, by omega⟩ : Fin (p + 2)) ⊗ₘ
              𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).X q)) ≫
            HomologicalComplex.ιTensorObj
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y) p q n hLow)) := by
  have hD :
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X).d (p + 1) p =
        ∑ j : Fin (p + 2), ((-1 : ℤ) ^ j.val) • X.δ j := by
    simp [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
      AlgebraicTopology.AlternatingFaceMapComplex.objD]
  rw [hD]
  have hTensor := sum_tensor_id (C := C)
    (D := ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).X q)
    (fun j : Fin (p + 2) ↦ ((-1 : ℤ) ^ j.val) • X.δ j)
  rw [hTensor]
  simp_rw [zsmul_tensor_id, Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  rw [Fin.sum_univ_castSucc]
  rfl

private lemma vertical_face_split (p q n : ℕ) (hLow : p + q = n) :
    ((-1 : ℤ) ^ p) •
      ((frontFace (C := C) X (show p + (q + 1) = n + 1 by omega) ⊗ₘ
          backFace (C := C) Y (show p + (q + 1) = n + 1 by omega)) ≫
        ((𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p) ⊗ₘ
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).d (q + 1) q) ≫
          HomologicalComplex.ιTensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y) p q n hLow)) =
      ((-1 : ℤ) ^ p) •
        ((frontFace (C := C) X (show p + (q + 1) = n + 1 by omega) ⊗ₘ
            backFace (C := C) Y (show p + (q + 1) = n + 1 by omega)) ≫
          ((𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p) ⊗ₘ
              Y.δ (⟨0, by omega⟩ : Fin (q + 2))) ≫
            HomologicalComplex.ιTensorObj
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y) p q n hLow)) +
      ∑ k : Fin (q + 1),
        ((-1 : ℤ) ^ (p + 1 + k.val)) •
          ((frontFace (C := C) X (show p + (q + 1) = n + 1 by omega) ⊗ₘ
              backFace (C := C) Y (show p + (q + 1) = n + 1 by omega)) ≫
            ((𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p) ⊗ₘ
                Y.δ (Fin.succ k)) ≫
              HomologicalComplex.ιTensorObj
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y) p q n hLow)) := by
  have hD :
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).d (q + 1) q =
        ∑ k : Fin (q + 2), ((-1 : ℤ) ^ k.val) • Y.δ k := by
    simp [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
      AlgebraicTopology.AlternatingFaceMapComplex.objD]
  rw [hD]
  have hTensor := id_tensor_sum (C := C)
    (A := ((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p)
    (fun k : Fin (q + 2) ↦ ((-1 : ℤ) ^ k.val) • Y.δ k)
  rw [hTensor]
  simp_rw [id_tensor_zsmul, Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  rw [Fin.sum_univ_succ, smul_add]
  simp only [Fin.val_zero, pow_zero, one_smul]
  congr 1
  rw [zsmul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_smul, ← pow_add]
  congr 1
  simp [Fin.val_succ, add_left_comm, add_comm]

private lemma crossover_component_eq (p q n : ℕ) (h : p + q = n) :
    (frontFace (C := C) X (show (p + 1) + q = n + 1 by omega) ⊗ₘ
        backFace (C := C) Y (show (p + 1) + q = n + 1 by omega)) ≫
      ((X.δ (⟨p + 1, by omega⟩ : Fin (p + 2)) ⊗ₘ
          𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).X q)) ≫
        HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          p q n h) =
    (frontFace (C := C) X (show p + (q + 1) = n + 1 by omega) ⊗ₘ
        backFace (C := C) Y (show p + (q + 1) = n + 1 by omega)) ≫
      ((𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p) ⊗ₘ
          Y.δ (⟨0, by omega⟩ : Fin (q + 2))) ≫
        HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          p q n h) := by
  subst n
  let KX := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
  let KY := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
  have hf :
      frontFace (C := C) X (show (p + 1) + q = p + q + 1 by omega) ≫
          X.δ (⟨p + 1, by omega⟩ : Fin (p + 2)) =
        frontFace (C := C) X (show p + (q + 1) = p + q + 1 by omega) := by
    simpa only [SimplicialObject.δ] using
      frontFace_last_crossover (C := C) X p q
  have hb :
      backFace (C := C) Y (show (p + 1) + q = p + q + 1 by omega) =
        backFace (C := C) Y (show p + (q + 1) = p + q + 1 by omega) ≫
          Y.δ (⟨0, by omega⟩ : Fin (q + 2)) :=
    Y.δ₀Iter_succ' p
  calc
    _ = ((frontFace (C := C) X (show (p + 1) + q = p + q + 1 by omega) ≫
            X.δ (⟨p + 1, by omega⟩ : Fin (p + 2))) ⊗ₘ
          backFace (C := C) Y (show (p + 1) + q = p + q + 1 by omega)) ≫
        HomologicalComplex.ιTensorObj KX KY p q (p + q) rfl := by
      rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
      simp
      dsimp only [KX, KY]
    _ = (frontFace (C := C) X (show p + (q + 1) = p + q + 1 by omega) ⊗ₘ
          (backFace (C := C) Y (show p + (q + 1) = p + q + 1 by omega) ≫
            Y.δ (⟨0, by omega⟩ : Fin (q + 2)))) ≫
        HomologicalComplex.ιTensorObj KX KY p q (p + q) rfl := by
      rw [hf, hb]
    _ = _ := by
      rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
      simp
      dsimp only [KX, KY]

private lemma horizontal_ordinary_component_eq
    (p q n : ℕ) (hLow : p + q = n) (j : Fin (p + 1)) :
    (frontFace (C := C) X (show (p + 1) + q = n + 1 by omega) ⊗ₘ
        backFace (C := C) Y (show (p + 1) + q = n + 1 by omega)) ≫
      ((X.δ (Fin.castSucc j) ⊗ₘ
          𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).X q)) ≫
        HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          p q n hLow) =
    (X.δ (⟨j.val, by omega⟩ : Fin (n + 2)) ⊗ₘ
        Y.δ (⟨j.val, by omega⟩ : Fin (n + 2))) ≫
      ((frontFace (C := C) X hLow ⊗ₘ backFace (C := C) Y hLow) ≫
        HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          p q n hLow) := by
  subst n
  let KX := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
  let KY := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
  have hf :
      frontFace (C := C) X (show (p + 1) + q = p + q + 1 by omega) ≫
          X.δ (Fin.castSucc j) =
        X.δ (⟨j.val, by omega⟩ : Fin (p + q + 2)) ≫
          frontFace (C := C) X (show p + q = p + q by rfl) := by
    simpa only [SimplicialObject.δ, Fin.val_castSucc] using
      frontFace_comp_delta (C := C) X p q (Fin.castSucc j)
  have hb :
      Y.δ (⟨j.val, by omega⟩ : Fin (p + q + 2)) ≫
          backFace (C := C) Y (show p + q = p + q by rfl) =
        backFace (C := C) Y (show (p + 1) + q = p + q + 1 by omega) :=
    Y.δ_δ₀Iter p ⟨j.val, by omega⟩
  calc
    _ = ((frontFace (C := C) X (show (p + 1) + q = p + q + 1 by omega) ≫
            X.δ (Fin.castSucc j)) ⊗ₘ
          backFace (C := C) Y (show (p + 1) + q = p + q + 1 by omega)) ≫
        HomologicalComplex.ιTensorObj KX KY p q (p + q) rfl := by
      rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
      simp
      dsimp only [KX, KY]
    _ = ((X.δ (⟨j.val, by omega⟩ : Fin (p + q + 2)) ≫
            frontFace (C := C) X (show p + q = p + q by rfl)) ⊗ₘ
          (Y.δ (⟨j.val, by omega⟩ : Fin (p + q + 2)) ≫
            backFace (C := C) Y (show p + q = p + q by rfl))) ≫
        HomologicalComplex.ιTensorObj KX KY p q (p + q) rfl := by
      rw [hf, hb]
    _ = _ := by
      rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]

private lemma vertical_ordinary_component_eq
    (p q n : ℕ) (hLow : p + q = n) (k : Fin (q + 1)) :
    (frontFace (C := C) X (show p + (q + 1) = n + 1 by omega) ⊗ₘ
        backFace (C := C) Y (show p + (q + 1) = n + 1 by omega)) ≫
      ((𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p) ⊗ₘ
          Y.δ (Fin.succ k)) ≫
        HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          p q n hLow) =
    (X.δ (⟨p + 1 + k.val, by omega⟩ : Fin (n + 2)) ⊗ₘ
        Y.δ (⟨p + 1 + k.val, by omega⟩ : Fin (n + 2))) ≫
      ((frontFace (C := C) X hLow ⊗ₘ backFace (C := C) Y hLow) ≫
        HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          p q n hLow) := by
  subst n
  let KX := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
  let KY := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
  have hf :
      X.δ (⟨p + 1 + k.val, by omega⟩ : Fin (p + q + 2)) ≫
          frontFace (C := C) X (show p + q = p + q by rfl) =
        frontFace (C := C) X (show p + (q + 1) = p + q + 1 by omega) := by
    simpa only [SimplicialObject.δ] using
      delta_comp_frontFace (C := C) X p q k
  have hb :
      backFace (C := C) Y (show p + (q + 1) = p + q + 1 by omega) ≫
          Y.δ (Fin.succ k) =
        Y.δ (⟨p + 1 + k.val, by omega⟩ : Fin (p + q + 2)) ≫
          backFace (C := C) Y (show p + q = p + q by rfl) :=
    (Y.δ_δ₀Iter' (n := q) (m := p + q) (Fin.succ k) p ⟨p + 1 + k.val, by omega⟩ (by omega)
      (by simp; omega)).symm
  calc
    _ = (frontFace (C := C) X (show p + (q + 1) = p + q + 1 by omega) ⊗ₘ
          (backFace (C := C) Y (show p + (q + 1) = p + q + 1 by omega) ≫
            Y.δ (Fin.succ k))) ≫
        HomologicalComplex.ιTensorObj KX KY p q (p + q) rfl := by
      rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
      simp
      dsimp only [KX, KY]
    _ = ((X.δ (⟨p + 1 + k.val, by omega⟩ : Fin (p + q + 2)) ≫
            frontFace (C := C) X (show p + q = p + q by rfl)) ⊗ₘ
          (Y.δ (⟨p + 1 + k.val, by omega⟩ : Fin (p + q + 2)) ≫
            backFace (C := C) Y (show p + q = p + q by rfl))) ≫
        HomologicalComplex.ιTensorObj KX KY p q (p + q) rfl := by
      rw [hf, hb]
    _ = _ := by
      rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]

private def faceSplitEquiv (n : ℕ) (p : Fin (n + 1)) :
    Fin (p.val + 1) ⊕ Fin (n - p.val + 1) ≃ Fin (n + 2) :=
  finSumFinEquiv.trans (finCongr (by omega))

private lemma ordinary_terms_eq_double_sum (n : ℕ) :
    let KX := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
    let KY := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
    (∑ p : Fin (n + 1),
      let q := n - p.val
      have hLow : p.val + q = n := by omega
      ∑ j : Fin (p.val + 1),
        ((-1 : ℤ) ^ j.val) •
          ((frontFace (C := C) X
                (show (p.val + 1) + q = n + 1 by omega) ⊗ₘ
              backFace (C := C) Y
                (show (p.val + 1) + q = n + 1 by omega)) ≫
            ((X.δ (Fin.castSucc j) ⊗ₘ 𝟙 (KY.X q)) ≫
              HomologicalComplex.ιTensorObj KX KY p.val q n hLow))) +
      (∑ p : Fin (n + 1),
        let q := n - p.val
        have hLow : p.val + q = n := by omega
        ∑ k : Fin (q + 1),
          ((-1 : ℤ) ^ (p.val + 1 + k.val)) •
            ((frontFace (C := C) X
                  (show p.val + (q + 1) = n + 1 by omega) ⊗ₘ
                backFace (C := C) Y
                  (show p.val + (q + 1) = n + 1 by omega)) ≫
              ((𝟙 (KX.X p.val) ⊗ₘ Y.δ (Fin.succ k)) ≫
                HomologicalComplex.ιTensorObj KX KY p.val q n hLow))) =
      ∑ i : Fin (n + 2),
        ∑ p : Fin (n + 1),
          let q := n - p.val
          have hLow : p.val + q = n := by omega
          ((-1 : ℤ) ^ i.val) •
            ((X.δ i ⊗ₘ Y.δ i) ≫
              ((frontFace (C := C) X hLow ⊗ₘ backFace (C := C) Y hLow) ≫
                HomologicalComplex.ιTensorObj KX KY p.val q n hLow)) := by
  let KX := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
  let KY := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
  let H := fun (p : Fin (n + 1)) (j : Fin (p.val + 1)) =>
    let q := n - p.val
    have hLow : p.val + q = n := by omega
    ((-1 : ℤ) ^ j.val) •
      ((frontFace (C := C) X
            (show (p.val + 1) + q = n + 1 by omega) ⊗ₘ
          backFace (C := C) Y
            (show (p.val + 1) + q = n + 1 by omega)) ≫
        ((X.δ (Fin.castSucc j) ⊗ₘ 𝟙 (KY.X q)) ≫
          HomologicalComplex.ιTensorObj KX KY p.val q n hLow))
  let V := fun (p : Fin (n + 1)) (k : Fin (n - p.val + 1)) =>
    let q := n - p.val
    have hLow : p.val + q = n := by omega
    ((-1 : ℤ) ^ (p.val + 1 + k.val)) •
      ((frontFace (C := C) X
            (show p.val + (q + 1) = n + 1 by omega) ⊗ₘ
          backFace (C := C) Y
            (show p.val + (q + 1) = n + 1 by omega)) ≫
        ((𝟙 (KX.X p.val) ⊗ₘ Y.δ (Fin.succ k)) ≫
          HomologicalComplex.ιTensorObj KX KY p.val q n hLow))
  let R := fun (p : Fin (n + 1)) (i : Fin (n + 2)) =>
    let q := n - p.val
    have hLow : p.val + q = n := by omega
    ((-1 : ℤ) ^ i.val) •
      ((X.δ i ⊗ₘ Y.δ i) ≫
        ((frontFace (C := C) X hLow ⊗ₘ backFace (C := C) Y hLow) ≫
          HomologicalComplex.ιTensorObj KX KY p.val q n hLow))
  change (∑ p, ∑ j, H p j) + (∑ p, ∑ k, V p k) =
    ∑ i, ∑ p, R p i
  rw [← Finset.sum_add_distrib, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  let e := faceSplitEquiv n p
  rw [← Fintype.sum_equiv e (fun x ↦ R p (e x)) (R p) (fun _ ↦ rfl),
    Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    dsimp only [H, R]
    rw [horizontal_ordinary_component_eq (C := C) X Y]
    rfl
  · apply Finset.sum_congr rfl
    intro k _
    dsimp only [V, R]
    rw [vertical_ordinary_component_eq (C := C) X Y]
    rfl

theorem alternatingComponent_comm (n : ℕ) :
    alternatingComponent X Y (n + 1) ≫
        (HomologicalComplex.tensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)).d
            (n + 1) n =
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj (X ⊗ Y)).d
          (n + 1) n ≫ alternatingComponent X Y n := by
  rw [alternatingComponent_comp_d_eq_bidegree_sum,
    d_comp_alternatingComponent_eq_tensor_double_sum]
  simp_rw [Preadditive.comp_add]
  rw [Finset.sum_add_distrib]
  rw [horizontal_outer_normalize (C := C) X Y,
    vertical_outer_normalize (C := C) X Y]
  simp_rw [horizontal_face_split (C := C) X Y,
    vertical_face_split (C := C) X Y]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  let KX := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
  let KY := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
  let H := fun (p : Fin (n + 1)) (j : Fin (p.val + 1)) =>
    let q := n - p.val
    have hLow : p.val + q = n := by omega
    ((-1 : ℤ) ^ j.val) •
      ((frontFace (C := C) X
            (show (p.val + 1) + q = n + 1 by omega) ⊗ₘ
          backFace (C := C) Y
            (show (p.val + 1) + q = n + 1 by omega)) ≫
        ((X.δ (Fin.castSucc j) ⊗ₘ 𝟙 (KY.X q)) ≫
          HomologicalComplex.ιTensorObj KX KY p.val q n hLow))
  let HC := fun p : Fin (n + 1) =>
    let q := n - p.val
    have hLow : p.val + q = n := by omega
    ((-1 : ℤ) ^ (p.val + 1)) •
      ((frontFace (C := C) X
            (show (p.val + 1) + q = n + 1 by omega) ⊗ₘ
          backFace (C := C) Y
            (show (p.val + 1) + q = n + 1 by omega)) ≫
        ((X.δ (⟨p.val + 1, by omega⟩ : Fin (p.val + 2)) ⊗ₘ
            𝟙 (KY.X q)) ≫
          HomologicalComplex.ιTensorObj KX KY p.val q n hLow))
  let VC := fun p : Fin (n + 1) =>
    let q := n - p.val
    have hLow : p.val + q = n := by omega
    ((-1 : ℤ) ^ p.val) •
      ((frontFace (C := C) X
            (show p.val + (q + 1) = n + 1 by omega) ⊗ₘ
          backFace (C := C) Y
            (show p.val + (q + 1) = n + 1 by omega)) ≫
        ((𝟙 (KX.X p.val) ⊗ₘ Y.δ (⟨0, by omega⟩ : Fin (q + 2))) ≫
          HomologicalComplex.ιTensorObj KX KY p.val q n hLow))
  let V := fun (p : Fin (n + 1)) (k : Fin (n - p.val + 1)) =>
    let q := n - p.val
    have hLow : p.val + q = n := by omega
    ((-1 : ℤ) ^ (p.val + 1 + k.val)) •
      ((frontFace (C := C) X
            (show p.val + (q + 1) = n + 1 by omega) ⊗ₘ
          backFace (C := C) Y
            (show p.val + (q + 1) = n + 1 by omega)) ≫
        ((𝟙 (KX.X p.val) ⊗ₘ Y.δ (Fin.succ k)) ≫
          HomologicalComplex.ιTensorObj KX KY p.val q n hLow))
  let R := fun (p : Fin (n + 1)) (i : Fin (n + 2)) =>
    let q := n - p.val
    have hLow : p.val + q = n := by omega
    ((-1 : ℤ) ^ i.val) •
      ((X.δ i ⊗ₘ Y.δ i) ≫
        ((frontFace (C := C) X hLow ⊗ₘ backFace (C := C) Y hLow) ≫
          HomologicalComplex.ιTensorObj KX KY p.val q n hLow))
  change ((∑ p, ∑ j, H p j) + ∑ p, HC p) +
      ((∑ p, VC p) + ∑ p, ∑ k, V p k) = ∑ i, ∑ p, R p i
  have hOrd : (∑ p, ∑ j, H p j) + (∑ p, ∑ k, V p k) =
      ∑ i, ∑ p, R p i := by
    dsimp only [H, V, R]
    exact ordinary_terms_eq_double_sum (C := C) X Y n
  have hCross : (∑ p, HC p) + (∑ p, VC p) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro p _
    dsimp only [HC, VC]
    have hcross := crossover_component_eq (C := C) X Y
      p.val (n - p.val) n (by omega)
    dsimp only [KX, KY] at hcross ⊢
    simp only [AlgebraicTopology.alternatingFaceMapComplex_obj_X] at hcross ⊢
    rw [hcross, pow_succ]
    simp
  calc
    _ = ((∑ p, ∑ j, H p j) + (∑ p, ∑ k, V p k)) +
        ((∑ p, HC p) + (∑ p, VC p)) := by
      ac_rfl
    _ = (∑ i, ∑ p, R p i) + 0 := by rw [hOrd, hCross]
    _ = _ := add_zero _

end AlgebraicTopology.AlexanderWhitney
