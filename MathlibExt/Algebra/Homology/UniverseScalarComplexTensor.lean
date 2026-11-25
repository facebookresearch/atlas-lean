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

public import MathlibExt.Algebra.Homology.UniverseScalarGradedTensor
public import MathlibExt.Algebra.Homology.UniverseScalarHomology
public import MathlibExt.Algebra.Category.ModuleCat.UniverseTensorExactness
public import MathlibExt.Algebra.Homology.TensorDifferentialDownNat
public import MathlibExt.Algebra.Homology.GradedTensorTower
import Lean.Elab.Tactic.Omega

/-!
# Actual tensor-complex comparison under original-ring scalar restriction

The component comparison is the actual finite-antidiagonal graded tensor
isomorphism. Its chain equation follows from the native tensor differential,
the two native module tensor naturality equations, and additive scalar
restriction. The actual integer Koszul sign is retained. No chain-map or
tensor-complex comparison certificate is supplied.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ModuleCat.UniverseScalarRestriction

variable (R : Type u) [CommRing R]


@[reassoc]
private theorem tensorComponent_ι (K L : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) (p q n : ℕ)
  (h : p + q = n) :
    HomologicalComplex.ιTensorObj ((complexFunctor.{u,v} R).obj K) ((complexFunctor.{u,v} R).obj L) p q n h ≫
      (gradedTensorIsoComponent.{u,v} R K.X L.X n).hom =
    (tensorIso.{u,v} R (K.X p) (L.X q)).hom ≫
      (toOriginal.{u,v} R).map (HomologicalComplex.ιTensorObj K L p q n h) :=
  ι_gradedTensorIso_hom.{u,v} R K.X L.X p q n h

private theorem tensorComponent_factors (K L : ChainComplex
    (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ) (p q p' q' n : ℕ)
    (h : p' + q' = n) (a : K.X p ⟶ K.X p') (b : L.X q ⟶ L.X q') :
    (tensorIso.{u,v} R (K.X p) (L.X q)).hom ≫
        (toOriginal.{u,v} R).map ((a ⊗ₘ b) ≫ HomologicalComplex.ιTensorObj K L p' q' n h) =
      (((toOriginal.{u,v} R).map a ⊗ₘ (toOriginal.{u,v} R).map b) ≫
        HomologicalComplex.ιTensorObj ((complexFunctor.{u,v} R).obj K)
          ((complexFunctor.{u,v} R).obj L) p' q' n h) ≫
        (gradedTensorIsoComponent.{u,v} R K.X L.X n).hom := by
  have hn := tensorIso_naturality.{u,v} R a b
  have hi := tensorComponent_ι.{u,v} R K L p' q' n h
  calc
    _ = (tensorIso.{u,v} R (K.X p) (L.X q)).hom ≫
        ((toOriginal.{u,v} R).map (a ⊗ₘ b) ≫
          (toOriginal.{u,v} R).map (HomologicalComplex.ιTensorObj K L p' q' n h)) :=
      congrArg (fun z => (tensorIso.{u,v} R (K.X p) (L.X q)).hom ≫ z)
        ((toOriginal.{u,v} R).map_comp _ _)
    _ = (((toOriginal.{u,v} R).map a ⊗ₘ (toOriginal.{u,v} R).map b) ≫
        (tensorIso.{u,v} R (K.X p') (L.X q')).hom) ≫
          (toOriginal.{u,v} R).map (HomologicalComplex.ιTensorObj K L p' q' n h) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ (toOriginal.{u,v} R).map
          (HomologicalComplex.ιTensorObj K L p' q' n h)) hn.symm)
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun z =>
        ((toOriginal.{u,v} R).map a ⊗ₘ (toOriginal.{u,v} R).map b) ≫ z) hi.symm).trans
          (Category.assoc _ _ _).symm)

private theorem linearCombination_comp {C : Type*} [Category C] [Preadditive C]
    {A B D : C} (r : ℤ) (a b : A ⟶ B) (c : B ⟶ D) :
    (a + r • b) ≫ c = a ≫ c + r • (b ≫ c) := by
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp]

private theorem tensorComponent_comm (K L : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) (n : ℕ) :
    (gradedTensorIsoComponent.{u,v} R K.X L.X (n + 1)).hom ≫
      (toOriginal.{u,v} R).map ((K ⊗ L).d (n + 1) n) =
    (((complexFunctor.{u,v} R).obj K) ⊗ ((complexFunctor.{u,v} R).obj L)).d (n + 1) n ≫
      (gradedTensorIsoComponent.{u,v} R K.X L.X n).hom := by
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := (complexFunctor.{u,v} R).obj K) (K₂ := (complexFunctor.{u,v} R).obj L)
    (F := curriedTensor (Modules.{u,v} R)) (c := ComplexShape.down ℕ)
  intro p q h
  change p + q = n + 1 at h
  have hc := tensorComponent_ι.{u,v} R K L p q (n + 1) h
  refine ((Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ (toOriginal.{u,v} R).map ((K ⊗ L).d (n + 1) n)) hc)).trans ?_
  rw [Category.assoc, ← Functor.map_comp]
  have dh := HomologicalComplex.ιTensorObj_comp_d_down_nat K L p q n h
  have dl := HomologicalComplex.ιTensorObj_comp_d_down_nat
    ((complexFunctor.{u,v} R).obj K) ((complexFunctor.{u,v} R).obj L) p q n h
  have hlow := (Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ (gradedTensorIsoComponent.{u,v} R K.X L.X n).hom) dl)
  refine (congrArg (fun z => (tensorIso.{u,v} R (K.X p) (L.X q)).hom ≫
    (toOriginal.{u,v} R).map z) dh).trans (Eq.trans ?_ hlow.symm)
  by_cases hp : p = 0
  · by_cases hq : q = 0
    · subst p; subst q; omega
    · subst p
      have hh : 0 + (q - 1) = n := by omega
      have ht := tensorComponent_factors.{u,v} R K L 0 q 0 (q - 1) n hh
        (𝟙 (K.X 0)) (L.d q (q - 1))
      simp only [Functor.map_id, Category.assoc] at ht
      simp only [dif_pos rfl, dif_neg hq, dite_true, Functor.map_add, Functor.map_zero,
        Functor.map_zsmul, Preadditive.zsmul_comp, zero_comp, zero_add,
        pow_zero, one_smul, Category.assoc]
      exact ht
  · by_cases hq : q = 0
    · subst q
      have hh : (p - 1) + 0 = n := by omega
      have ht := tensorComponent_factors.{u,v} R K L p 0 (p - 1) 0 n hh
        (K.d p (p - 1)) (𝟙 (L.X 0))
      simp only [Functor.map_id, Category.assoc] at ht
      simp only [dif_neg hp, dif_pos rfl, dite_true, Functor.map_add, Functor.map_zero,
        zero_comp, comp_zero, add_zero, Category.assoc]
      exact ht
    · have h₁ : (p - 1) + q = n := by omega
      have h₂ : p + (q - 1) = n := by omega
      have ht₁ := tensorComponent_factors.{u,v} R K L p q (p - 1) q n h₁
        (K.d p (p - 1)) (𝟙 (L.X q))
      have ht₂ := tensorComponent_factors.{u,v} R K L p q p (q - 1) n h₂
        (𝟙 (K.X p)) (L.d q (q - 1))
      simp only [Functor.map_id, Category.assoc] at ht₁ ht₂
      simp only [dif_neg hp, dif_neg hq, Functor.map_add, Functor.map_zsmul,
        Preadditive.zsmul_comp, Preadditive.comp_add, Preadditive.comp_zsmul,
        Preadditive.add_comp, Category.assoc]
      let a := ((toOriginal.{u,v} R).map (K.d p (p - 1)) ⊗ₘ
        (toOriginal.{u,v} R).map (𝟙 (L.X q))) ≫
          HomologicalComplex.ιTensorObj ((complexFunctor.{u,v} R).obj K)
            ((complexFunctor.{u,v} R).obj L) (p - 1) q n h₁
      let b := ((toOriginal.{u,v} R).map (𝟙 (K.X p)) ⊗ₘ
        (toOriginal.{u,v} R).map (L.d q (q - 1))) ≫
          HomologicalComplex.ιTensorObj ((complexFunctor.{u,v} R).obj K)
            ((complexFunctor.{u,v} R).obj L) p (q - 1) n h₂
      exact (congrArg₂ (fun x y => x + ((-1 : ℤ) ^ p) • y) ht₁ ht₂).trans
        (linearCombination_comp ((-1 : ℤ) ^ p) a b
          (gradedTensorIsoComponent.{u,v} R K.X L.X n).hom).symm


/-- The actual component comparisons form the native tensor-complex chain map. -/
def complexTensorMap (K L : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) :
  (complexFunctor.{u,v} R).obj K ⊗ (complexFunctor.{u,v} R).obj L ⟶ (complexFunctor.{u,v} R).obj (K ⊗ L) where
  f n := (gradedTensorIsoComponent.{u,v} R K.X L.X n).hom
  comm' i j h := by
    change j + 1 = i at h
    subst i
    exact tensorComponent_comm.{u,v} R K L j

/-- The actual chain tensor comparison is an isomorphism in every degree,
hence an actual native chain-complex isomorphism. -/
def complexTensorIso (K L : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) :
  (complexFunctor.{u,v} R).obj K ⊗ (complexFunctor.{u,v} R).obj L ≅ (complexFunctor.{u,v} R).obj (K ⊗ L) :=
  HomologicalComplex.Hom.isoOfComponents
    (gradedTensorIsoComponent.{u,v} R K.X L.X)
    (fun i j h => (complexTensorMap.{u,v} R K L).comm i j)

@[reassoc (attr := simp)]
theorem ι_complexTensorIso_hom (K L : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) (p q n : ℕ)
  (h : p + q = n) :
    HomologicalComplex.ιTensorObj ((complexFunctor.{u,v} R).obj K) ((complexFunctor.{u,v} R).obj L) p q n h ≫
      (complexTensorIso.{u,v} R K L).hom.f n =
    (tensorIso.{u,v} R (K.X p) (L.X q)).hom ≫
      (toOriginal.{u,v} R).map (HomologicalComplex.ιTensorObj K L p q n h) :=
  tensorComponent_ι.{u,v} R K L p q n h

/-- The actual tensor-complex comparison is natural in both original chain maps. -/
@[reassoc]
theorem complexTensorIso_naturality {K L K' L' : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)}
  (f : K ⟶ K') (g : L ⟶ L') :
    ((complexFunctor.{u,v} R).map f ⊗ₘ (complexFunctor.{u,v} R).map g) ≫ (complexTensorIso.{u,v} R K' L').hom =
      (complexTensorIso.{u,v} R K L).hom ≫ (complexFunctor.{u,v} R).map (f ⊗ₘ g) := by
  apply HomologicalComplex.hom_ext
  intro n
  change (GradedObject.Monoidal.tensorHom (fun i => (toOriginal.{u,v} R).map (f.f i))
      (fun i => (toOriginal.{u,v} R).map (g.f i))) n ≫ (gradedTensorIsoComponent.{u,v} R K'.X L'.X n).hom =
    (gradedTensorIsoComponent.{u,v} R K.X L.X n).hom ≫
      (toOriginal.{u,v} R).map ((HomologicalComplex.tensorHom f g).f n)
  rw [HomologicalComplex.tensorHom_f_eq_graded]
  exact congrFun (gradedTensorIso_naturality.{u,v} R f.f g.f) n

/-- The actual original tensor complex is reached from the actual lifted-ring
representations and the earned complex tensor isomorphism. -/
def originalTensorComplexIso (K L : ChainComplex (Modules.{u,v} R) ℕ) :
    (complexFunctor.{u,v} R).obj (((toLiftedComplex.{u,v} R).obj K) ⊗ ((toLiftedComplex.{u,v} R).obj L)) ≅ K ⊗ L :=
  (complexTensorIso.{u,v} R ((toLiftedComplex.{u,v} R).obj K)
      ((toLiftedComplex.{u,v} R).obj L)).symm ≪≫
    (originalComplexIso.{u,v} R K ⊗ᵢ originalComplexIso.{u,v} R L)

end ModuleCat.UniverseScalarRestriction
