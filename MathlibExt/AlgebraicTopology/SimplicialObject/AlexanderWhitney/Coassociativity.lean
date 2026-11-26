/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.ChainMap
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.Coherence

/-!
# Alexander–Whitney associativity on alternating-face complexes

Let C be preadditive and monoidal with a zero object and finite coproducts. Suppose both tensor
variables are additive and preserve finite coproducts. The alternating-face functor A sends X to
the chain complex with term X_n and boundary ∑_i(-1)^i d_i. The Alexander–Whitney map
AW_{X,Y}:A(X⊗Y)→A(X)⊗A(Y) splits degree n over p+q=n by the front-p and back-q face maps.

For simplicial X,Y,Z, applying AW twice along the two parenthesizations gives equal maps after
the simplicial and chain tensor associators. This is an equality of the specified chain maps,
with arbitrary object and morphism universes.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Simplicial

namespace AlgebraicTopology.AlexanderWhitney

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSectionVars false

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  [(curriedTensor C).Additive]
  [∀ T : C, ((curriedTensor C).obj T).Additive]
  [∀ T : C, PreservesFiniteCoproducts ((curriedTensor C).obj T)]
  [∀ T : C, PreservesFiniteCoproducts ((curriedTensor C).flip.obj T)]

noncomputable local instance : MonoidalCategory (ChainComplex C ℕ) :=
  HomologicalComplex.monoidalCategory C (ComplexShape.down ℕ)

private lemma sum_tensor_id {A B D : C} {J : Type*} [Fintype J]
    (f : J → (A ⟶ B)) :
    ((∑ j, f j) ⊗ₘ 𝟙 D) = ∑ j, f j ⊗ₘ 𝟙 D := by
  simp_rw [tensorHom_id]
  have h := Functor.map_sum (curriedTensor C) f Finset.univ
  have h' := congrArg (fun a => a.app D) h
  simpa only [curriedTensor_map_app, NatTrans.app_sum] using h'

private lemma id_tensor_sum {A B D : C} {J : Type*} [Fintype J]
    (g : J → (B ⟶ D)) :
    (𝟙 A ⊗ₘ (∑ j, g j)) = ∑ j, 𝟙 A ⊗ₘ g j := by
  simp_rw [id_tensorHom]
  exact Functor.map_sum ((curriedTensor C).obj A) g Finset.univ

private lemma sum_tensor_morphism {A B D E : C} {J : Type*} [Fintype J]
    (g : J → (A ⟶ B)) (f : D ⟶ E) :
    ((∑ j, g j) ⊗ₘ f) = ∑ j, g j ⊗ₘ f := by
  rw [MonoidalCategory.tensorHom_def]
  have h := Functor.map_sum (curriedTensor C) g Finset.univ
  have h' := congrArg (fun a => a.app D) h
  rw [show (∑ j, g j) ▷ D = ∑ j, g j ▷ D by
    simpa only [curriedTensor_map_app, NatTrans.app_sum] using h']
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [MonoidalCategory.tensorHom_def]

private lemma tensor_morphism_sum {A B D E : C} {J : Type*} [Fintype J]
    (f : A ⟶ B) (g : J → (D ⟶ E)) :
    (f ⊗ₘ (∑ j, g j)) = ∑ j, f ⊗ₘ g j := by
  rw [MonoidalCategory.tensorHom_def]
  have h := Functor.map_sum ((curriedTensor C).obj B) g Finset.univ
  rw [show B ◁ (∑ j, g j) = ∑ j, B ◁ g j by exact h]
  rw [Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [MonoidalCategory.tensorHom_def]

private lemma frontFace_tensor (X Y : SimplicialObject C) {p q n : ℕ}
    (h : p + q = n) :
    frontFace (X ⊗ Y) h = frontFace X h ⊗ₘ frontFace Y h := rfl

private lemma backFace_tensor (X Y : SimplicialObject C) {p q n : ℕ}
    (h : p + q = n) :
    backFace (X ⊗ Y) h = backFace X h ⊗ₘ backFace Y h := rfl

private def assocIndexEquiv (n : ℕ) :
    (Σ k : Fin (n + 1), Fin (k.val + 1)) ≃
      (Σ p : Fin (n + 1), Fin (n - p.val + 1)) where
  toFun x :=
    ⟨⟨x.2.val, by
        have hk := x.1.isLt
        have hp := x.2.isLt
        omega⟩,
      ⟨x.1.val - x.2.val, by
        have hk : x.1.val ≤ n := Nat.lt_succ_iff.mp x.1.isLt
        exact Nat.lt_succ_of_le (Nat.sub_le_sub_right hk x.2.val)⟩⟩
  invFun x :=
    ⟨⟨x.1.val + x.2.val, by
        have hp := x.1.isLt
        have hq := x.2.isLt
        omega⟩,
      ⟨x.1.val, by
        exact Nat.lt_succ_of_le (Nat.le_add_right x.1.val x.2.val)⟩⟩
  left_inv x := by
    rcases x with ⟨k, p⟩
    have hk : (⟨p.val + (k.val - p.val), by
        have hkn := k.isLt
        have hpk := p.isLt
        omega⟩ : Fin (n + 1)) = k := by
      apply Fin.ext
      simp
      omega
    apply Sigma.ext hk
    apply (Fin.heq_ext_iff (congrArg (fun i : Fin (n + 1) => i.val + 1) hk)).2
    rfl
  right_inv x := by
    rcases x with ⟨p, q⟩
    have hp : (⟨p.val, by
        have hpn := p.isLt
        omega⟩ : Fin (n + 1)) = p := by
      apply Fin.ext
      rfl
    apply Sigma.ext hp
    apply (Fin.heq_ext_iff
      (congrArg (fun i : Fin (n + 1) => n - i.val + 1) hp)).2
    simp

private noncomputable def leftAssocTerm (X Y Z : SimplicialObject C) (n : ℕ)
    (a : Σ k : Fin (n + 1), Fin (k.val + 1)) :
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj ((X ⊗ Y) ⊗ Z)).X n ⟶
      (HomologicalComplex.tensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (HomologicalComplex.tensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z))).X n :=
  let k := a.1.val
  let p := a.2.val
  let q := k - p
  let r := n - k
  have hpq : p + q = k := by
    dsimp [p, q, k]
    have hp := a.2.isLt
    omega
  have hkr : k + r = n := by
    dsimp [k, r]
    have hk := a.1.isLt
    omega
  (((frontFace (X ⊗ Y) hkr ≫
        ((frontFace X hpq ⊗ₘ backFace Y hpq) ≫
          HomologicalComplex.ιTensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            p q k hpq)) ⊗ₘ
      (backFace Z hkr ≫
        𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj Z).X r))) ≫
    HomologicalComplex.ιTensorObj
      (HomologicalComplex.tensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y))
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)
      k r n hkr ≫
    (HomologicalComplex.associator
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)).hom.f n)

private noncomputable def rightAssocTerm (X Y Z : SimplicialObject C) (n : ℕ)
    (a : Σ p : Fin (n + 1), Fin (n - p.val + 1)) :
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj ((X ⊗ Y) ⊗ Z)).X n ⟶
      (HomologicalComplex.tensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (HomologicalComplex.tensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z))).X n :=
  let p := a.1.val
  let q := a.2.val
  let s := n - p
  let r := s - q
  have hps : p + s = n := by
    dsimp [p, s]
    have hp := a.1.isLt
    omega
  have hqr : q + r = s := by
    dsimp [q, r, s]
    have hq := a.2.isLt
    omega
  ((AlgebraicTopology.alternatingFaceMapComplex C).map (α_ X Y Z).hom).f n ≫
    (((frontFace X hps ≫
        𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p)) ⊗ₘ
      (backFace (Y ⊗ Z) hps ≫
        ((frontFace Y hqr ⊗ₘ backFace Z hqr) ≫
          HomologicalComplex.ιTensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)
            q r s hqr))) ≫
    HomologicalComplex.ιTensorObj
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      (HomologicalComplex.tensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z))
      p s n hps)

@[reassoc]
private lemma triple_faces_assoc (X Y Z : SimplicialObject C)
    (p q r m s n : ℕ) (hpq : p + q = m) (hmr : m + r = n)
    (hqr : q + r = s) (hps : p + s = n) :
    ((((frontFace X hmr ≫ frontFace X hpq) ⊗ₘ
          (frontFace Y hmr ≫ backFace Y hpq)) ⊗ₘ
        backFace Z hmr) ≫
      (α_ (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p)
        (((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).X q)
        (((AlgebraicTopology.alternatingFaceMapComplex C).obj Z).X r)).hom) =
      ((α_ X Y Z).hom.app (Opposite.op (SimplexCategory.mk n)) ≫
        (frontFace X hps ⊗ₘ
          ((backFace Y hps ≫ frontFace Y hqr) ⊗ₘ
            (backFace Z hps ≫ backFace Z hqr)))) := by
  subst m
  subst s
  rw [frontFace_assoc X p q r n hmr]
  rw [middleFace_assoc Y p q r n hmr]
  rw [← backFace_assoc Z p q r n hmr]
  exact MonoidalCategory.associator_naturality _ _ _

private lemma triple_inclusion_assoc
    (KX KY KZ : ChainComplex C ℕ) (p q r m s n : ℕ)
    (hpq : p + q = m) (hmr : m + r = n)
    (hqr : q + r = s) (hps : p + s = n) :
    ((HomologicalComplex.ιTensorObj KX KY p q m hpq ⊗ₘ 𝟙 (KZ.X r)) ≫
        HomologicalComplex.ιTensorObj
          (HomologicalComplex.tensorObj KX KY) KZ m r n hmr ≫
        (HomologicalComplex.associator KX KY KZ).hom.f n) =
      ((α_ (KX.X p) (KY.X q) (KZ.X r)).hom ≫
        (𝟙 (KX.X p) ⊗ₘ
          HomologicalComplex.ιTensorObj KY KZ q r s hqr) ≫
        HomologicalComplex.ιTensorObj KX
          (HomologicalComplex.tensorObj KY KZ) p s n hps) := by
  have h : p + q + r = n := by omega
  have h' := HomologicalComplex.ι_mapBifunctorAssociatorX_hom
    (MonoidalCategory.curriedAssociatorNatIso C)
    KX KY KZ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) p q r n h
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq
      (curriedTensor C) (curriedTensor C) KX KY KZ
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      p q r m n hpq hmr,
    HomologicalComplex.mapBifunctor₂₃.ι_eq
      (curriedTensor C) (curriedTensor C) KX KY KZ
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      p q r s n hqr hps] at h'
  simpa only [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorObj,
    HomologicalComplex.associator,
    HomologicalComplex.mapBifunctorAssociator,
    MonoidalCategory.curriedTensor_map_app,
    MonoidalCategory.curriedTensor_obj_map,
    MonoidalCategory.curriedAssociatorNatIso_hom_app_app_app,
    HomologicalComplex.Hom.isoOfComponents_hom_f,
    tensorHom_id, id_tensorHom, Category.assoc] using h'

private lemma right_face_inclusion_congr (X Y Z : SimplicialObject C)
    (p q r r' s n : ℕ) (hqr : q + r = s) (hqr' : q + r' = s)
    (hps : p + s = n) (hr : r = r') :
    ((frontFace X hps ⊗ₘ
          ((backFace Y hps ≫ frontFace Y hqr) ⊗ₘ
            (backFace Z hps ≫ backFace Z hqr))) ≫
        (𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p) ⊗ₘ
          HomologicalComplex.ιTensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)
            q r s hqr) ≫
        HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          (HomologicalComplex.tensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z))
          p s n hps) =
      ((frontFace X hps ⊗ₘ
          ((backFace Y hps ≫ frontFace Y hqr') ⊗ₘ
            (backFace Z hps ≫ backFace Z hqr'))) ≫
        (𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p) ⊗ₘ
          HomologicalComplex.ιTensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)
            q r' s hqr') ≫
        HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          (HomologicalComplex.tensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z))
          p s n hps) := by
  subst r'
  rfl

private lemma alternatingComponent_tensor_id (X Y : SimplicialObject C)
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]
    (D : C) (n : ℕ) :
    alternatingComponent X Y n ⊗ₘ 𝟙 D =
      ∑ p : Fin (n + 1),
        (((frontFace X (show p.val + (n - p.val) = n by omega) ⊗ₘ
              backFace Y (show p.val + (n - p.val) = n by omega)) ≫
            HomologicalComplex.ιTensorObj
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
              p.val (n - p.val) n (by omega)) ⊗ₘ 𝟙 D) := by
  rw [alternatingComponent, sum_tensor_id]

private lemma id_tensor_alternatingComponent (X Y : SimplicialObject C)
    [HomologicalComplex.HasTensor
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]
    (D : C) (n : ℕ) :
    𝟙 D ⊗ₘ alternatingComponent X Y n =
      ∑ p : Fin (n + 1),
        (𝟙 D ⊗ₘ
          ((frontFace X (show p.val + (n - p.val) = n by omega) ⊗ₘ
              backFace Y (show p.val + (n - p.val) = n by omega)) ≫
            HomologicalComplex.ιTensorObj
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
              p.val (n - p.val) n (by omega))) := by
  rw [alternatingComponent, id_tensor_sum]

private lemma left_tail (X Y Z : SimplicialObject C)
    (k r n : ℕ) (h : k + r = n) :
    HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj (X ⊗ Y))
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z) k r n h ≫
        (HomologicalComplex.tensorHom (alternatingMap X Y) (𝟙 _)).f n ≫
        (HomologicalComplex.associator
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)).hom.f n =
      (alternatingComponent X Y k ⊗ₘ
          𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj Z).X r)) ≫
        HomologicalComplex.ιTensorObj
          (HomologicalComplex.tensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y))
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)
          k r n h ≫
        (HomologicalComplex.associator
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)).hom.f n := by
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f]
  rw [← Category.assoc]
  change ((((alternatingMap X Y).f k ▷ _) ≫ (_ ◁ 𝟙 _)) ≫ _ ≫ _) = _
  rw [← MonoidalCategory.tensorHom_def]
  rw [alternatingMap_f]

private lemma right_tail (X Y Z : SimplicialObject C)
    (p s n : ℕ) (h : p + s = n) :
    HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj (Y ⊗ Z)) p s n h ≫
        (HomologicalComplex.tensorHom (𝟙 _) (alternatingMap Y Z)).f n =
      (𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p) ⊗ₘ
          alternatingComponent Y Z s) ≫
        HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          (HomologicalComplex.tensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z))
          p s n h := by
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f]
  rw [← Category.assoc]
  change (𝟙 _ ▷ _ ≫ _ ◁ (alternatingMap Y Z).f s) ≫ _ = _
  rw [← MonoidalCategory.tensorHom_def, alternatingMap_f]

private lemma left_outer_expand (X Y Z : SimplicialObject C)
    (k r n : ℕ) (h : k + r = n) :
    (frontFace (X ⊗ Y) h ⊗ₘ backFace Z h) ≫
        (alternatingComponent X Y k ⊗ₘ
          𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj Z).X r)) ≫
        HomologicalComplex.ιTensorObj
          (HomologicalComplex.tensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y))
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)
          k r n h ≫
        (HomologicalComplex.associator
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)).hom.f n =
      ∑ p : Fin (k + 1),
        (((frontFace (X ⊗ Y) h ≫
              ((frontFace X (show p.val + (k - p.val) = k by omega) ⊗ₘ
                backFace Y (show p.val + (k - p.val) = k by omega)) ≫
              HomologicalComplex.ιTensorObj
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                p.val (k - p.val) k (by omega))) ⊗ₘ
            (backFace Z h ≫
              𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj Z).X r))) ≫
          HomologicalComplex.ιTensorObj
            (HomologicalComplex.tensorObj
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y))
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)
            k r n h ≫
          (HomologicalComplex.associator
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)).hom.f n) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [alternatingComponent, Preadditive.comp_sum]
  rw [sum_tensor_morphism]
  simp only [Preadditive.sum_comp]

private lemma right_outer_expand (X Y Z : SimplicialObject C)
    (p s n : ℕ) (h : p + s = n) :
    ((AlgebraicTopology.alternatingFaceMapComplex C).map (α_ X Y Z).hom).f n ≫
        (frontFace X h ⊗ₘ backFace (Y ⊗ Z) h) ≫
        (𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p) ⊗ₘ
          alternatingComponent Y Z s) ≫
        HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          (HomologicalComplex.tensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z))
          p s n h =
      ∑ q : Fin (s + 1),
        (((AlgebraicTopology.alternatingFaceMapComplex C).map
              (α_ X Y Z).hom).f n ≫
            ((frontFace X h ≫
                𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p)) ⊗ₘ
              (backFace (Y ⊗ Z) h ≫
                ((frontFace Y (show q.val + (s - q.val) = s by omega) ⊗ₘ
                    backFace Z (show q.val + (s - q.val) = s by omega)) ≫
                  HomologicalComplex.ιTensorObj
                    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
                    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)
                    q.val (s - q.val) s (by omega)))) ≫
          HomologicalComplex.ιTensorObj
            ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
            (HomologicalComplex.tensorObj
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
              ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z))
            p s n h) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [alternatingComponent, Preadditive.comp_sum]
  rw [tensor_morphism_sum]
  rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Category.assoc]

private theorem assocTerm_eq (X Y Z : SimplicialObject C) (n : ℕ)
    (a : Σ k : Fin (n + 1), Fin (k.val + 1)) :
    leftAssocTerm X Y Z n a =
      rightAssocTerm X Y Z n (assocIndexEquiv n a) := by
  rcases a with ⟨k, p⟩
  dsimp only [leftAssocTerm, rightAssocTerm, assocIndexEquiv]
  simp only [Equiv.coe_fn_mk]
  simp only [AlgebraicTopology.alternatingFaceMapComplex_map_f]
  simp_rw [frontFace_tensor, backFace_tensor]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  have hpk : p.val ≤ k.val := Nat.lt_succ_iff.mp p.isLt
  have hkn : k.val ≤ n := Nat.lt_succ_iff.mp k.isLt
  have hsum : p.val + (k.val - p.val) + (n - k.val) = n := by omega
  have hr : n - p.val - (k.val - p.val) = n - k.val := by omega
  simp only [hr]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [triple_inclusion_assoc
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)
    p.val (k.val - p.val) (n - k.val) k.val (n - p.val) n
    (by omega) (by omega) (by omega) (by omega)]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [triple_faces_assoc_assoc X Y Z
    p.val (k.val - p.val) (n - k.val) k.val (n - p.val) n
    (by omega) (by omega) (by omega) (by omega)]
  congr 1
  exact right_face_inclusion_congr X Y Z p.val (k.val - p.val)
    (n - k.val) (n - p.val - (k.val - p.val)) (n - p.val) n
    (by omega) (by omega) (by omega) hr.symm

/-- Let C be a preadditive monoidal category with independent object and morphism universes, a zero
object and finite coproducts. Assume tensoring in each variable is additive and preserves finite
coproducts. Write A for the alternating-face functor from simplicial objects to nonnegative
chain complexes. For simplicial objects X,Y,Z, the equality is
AW_{X⊗Y,Z}≫(AW_{X,Y}⊗id_{A(Z)})≫α_{A(X),A(Y),A(Z)}=A(α_{X,Y,Z})≫AW_{X,Y⊗Z}≫(id_{A(X)}⊗AW_{Y,Z}).
Both sides map A((X⊗Y)⊗Z) to A(X)⊗(A(Y)⊗A(Z)) using the canonical associators. -/
theorem alternatingMap_assoc (X Y Z : SimplicialObject C) :
    alternatingMap (X ⊗ Y) Z ≫
        HomologicalComplex.tensorHom (alternatingMap X Y) (𝟙 _) ≫
        (HomologicalComplex.associator
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj Z)).hom =
      (AlgebraicTopology.alternatingFaceMapComplex C).map (α_ X Y Z).hom ≫
        alternatingMap X (Y ⊗ Z) ≫
        HomologicalComplex.tensorHom (𝟙 _) (alternatingMap Y Z) := by
  ext n
  simp only [HomologicalComplex.comp_f, alternatingMap_f]
  rw [alternatingComponent, alternatingComponent]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  simp_rw [left_tail, right_tail]
  simp_rw [left_outer_expand, right_outer_expand]
  change (∑ k : Fin (n + 1), ∑ p : Fin (k.val + 1),
      leftAssocTerm X Y Z n ⟨k, p⟩) =
    ∑ p : Fin (n + 1), ∑ q : Fin (n - p.val + 1),
      rightAssocTerm X Y Z n ⟨p, q⟩
  rw [← Fintype.sum_sigma, ← Fintype.sum_sigma]
  apply Fintype.sum_equiv (assocIndexEquiv n)
  intro a
  exact assocTerm_eq X Y Z n a

end AlgebraicTopology.AlexanderWhitney
