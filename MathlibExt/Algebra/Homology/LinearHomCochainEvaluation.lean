/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import MathlibExt.Algebra.Homology.CochainChainGradedPairingHomology
public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairing
import MathlibExt.Algebra.Homology.TensorUnitor

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace HomologicalComplex

variable (R : Type u) [CommRing R]

noncomputable local instance linearHomEvaluationChainMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- Evaluation of linear Hom-cochains on chains, with values concentrated in degree zero. -/
public noncomputable def linearHomCochainEvaluationGradedPairing
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (M : ModuleCat.{u} R) :
    CochainChainGradedPairing
      ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj (op K)) K
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M) :=
  linearHomCochainChainGradedPairing R (rightUnitor K).inv
    (rightUnitor ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M)).hom

/-- The pairing on cohomology and homology induced by cochain evaluation. -/
public noncomputable def linearHomCochainEvaluationHomology
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (M : ModuleCat.{u} R) (p : ℕ) :
    ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
        (op K)).homology p ⊗ K.homology p ⟶ M :=
  (linearHomCochainEvaluationGradedPairing R K M).pairHomology p 0 ≫
    (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 M).hom

/-- Evaluation on homology is represented by evaluation on cycles. -/
@[reassoc]
public theorem tensor_homologyπ_comp_linearHomCochainEvaluationHomology
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (M : ModuleCat.{u} R) (p : ℕ) :
    ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
        (op K)).homologyπ p) ⊗ₘ K.homologyπ p) ≫
      linearHomCochainEvaluationHomology R K M p =
    (linearHomCochainEvaluationGradedPairing R K M).pairCycles p 0 ≫
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M).homologyπ 0 ≫
      (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 M).hom := by
  unfold linearHomCochainEvaluationHomology
  simpa only [Nat.add_zero, Category.assoc] using congrArg
    (fun f => f ≫ (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 M).hom)
    (CochainChainGradedPairing.tensor_homologyπ_comp_pairHomology
      (linearHomCochainEvaluationGradedPairing R K M) p 0)

/-- Evaluation on homology, computed on representatives: the evaluation of
the class of a cochain cycle on the class of a chain cycle is the value of
the underlying cochain on the underlying chain. -/
public theorem linearHomCochainEvaluationHomology_π_apply
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (M : ModuleCat.{u} R) (p : ℕ)
    (phi : ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
      (op K)).cycles p)
    (x : K.cycles p) :
    (linearHomCochainEvaluationHomology R K M p).hom
        ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
          (op K)).homologyπ p).hom phi ⊗ₜ[R] (K.homologyπ p).hom x) =
      ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
        (op K)).iCycles p).hom phi).hom ((K.iCycles p).hom x) := by
  let C := (linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
    (op K)
  let E := linearHomCochainEvaluationGradedPairing R K M
  have h := ConcreteCategory.congr_hom
    (tensor_homologyπ_comp_linearHomCochainEvaluationHomology R K M p)
    (phi ⊗ₜ[R] x)
  change (linearHomCochainEvaluationHomology R K M p).hom
      ((C.homologyπ p).hom phi ⊗ₜ[R] (K.homologyπ p).hom x) = _ at h
  rw [ModuleCat.comp_apply] at h
  rw [h]
  change ((singleObjHomologySelfIso
    (ComplexShape.down ℕ) 0 M).hom).hom
      ((((ChainComplex.single₀ (ModuleCat.{u} R)).obj M).homologyπ 0).hom
        ((E.pairCycles p 0).hom (phi ⊗ₜ[R] x))) = _
  rw [← ModuleCat.comp_apply,
    homologyπ_singleObjHomologySelfIso_hom,
    singleObjCyclesSelfIso_hom,
    ModuleCat.comp_apply]
  have hCycles := ConcreteCategory.congr_hom
    (E.pairCycles_i p 0) (phi ⊗ₜ[R] x)
  change
    (((ChainComplex.single₀ (ModuleCat.{u} R)).obj M).iCycles 0).hom
        ((E.pairCycles p 0).hom (phi ⊗ₜ[R] x)) =
      (E.pair p 0).hom
        ((C.iCycles p).hom phi ⊗ₜ[R] (K.iCycles p).hom x) at hCycles
  rw [hCycles]
  unfold E linearHomCochainEvaluationGradedPairing
  rw [linearHomCochainChainGradedPairing_pair]
  let I := tensorUnit (ModuleCat.{u} R) (ComplexShape.down ℕ)
  let SM := (ChainComplex.single₀ (ModuleCat.{u} R)).obj M
  let U := singleObjXSelf (ComplexShape.down ℕ) 0
    (𝟙_ (ModuleCat.{u} R))
  let S := singleObjXSelf (ComplexShape.down ℕ) 0 M
  let B : ChainGradedPairing SM I SM := (rightUnitor SM).hom
  let rho := chainGradedPairingDegreeZeroAction R B
  let f := (C.iCycles p).hom phi
  change (K.X p ⟶ M) at f
  let z := (K.iCycles p).hom x
  change S.hom.hom
      ((linearHomCochainChainPair R (rightUnitor K).inv rho p 0).hom
        (f ⊗ₜ[R] z)) = f.hom z
  rw [linearHomCochainChainPair_tmul]
  change S.hom.hom
      (((rightUnitor K).inv.f p ≫
        linearHomCochainChainPairDesc R rho p 0 f).hom z) = f.hom z
  have hKInv :
      (rightUnitor K).inv.f p =
        (ρ_ (K.X p)).inv ≫ (K.X p ◁ U.inv) ≫
          ιTensorObj K I p 0 p (Nat.add_zero p) := by
    change (rightUnitor' K).inv p = _
    exact rightUnitor'_inv K p
  have hDesc := ιTensorObj_comp_linearHomCochainChainPairDesc
    R rho p 0 p 0 (Nat.add_zero p) f
  simp only [dite_eq_left] at hDesc
  have hDescP :
      ιTensorObj K I p 0 p (Nat.add_zero p) ≫
          linearHomCochainChainPairDesc R rho p 0 f =
        (f ⊗ₘ 𝟙 (I.X 0)) ≫ rho 0 := by
    simpa only [Nat.add_zero] using hDesc
  have hRho :
      rho 0 =
        (S.inv ▷ I.X 0) ≫
          (SM.X 0 ◁ U.hom) ≫ (ρ_ (SM.X 0)).hom := by
    dsimp only [rho, B, chainGradedPairingDegreeZeroAction]
    rw [ιTensorObj_rightUnitor_hom]
  have hRaw :
      (rightUnitor K).inv.f p ≫
          linearHomCochainChainPairDesc R rho p 0 f ≫ S.hom = f := by
    rw [hKInv]
    simp only [Category.assoc]
    rw [reassoc_of% hDescP, hRho]
    change
      (ρ_ (K.X p)).inv ≫
        (𝟙 (K.X p) ⊗ₘ U.inv) ≫
        (f ⊗ₘ 𝟙 (I.X 0)) ≫
        (S.inv ⊗ₘ 𝟙 (I.X 0)) ≫
        (((𝟙 (SM.X 0) ⊗ₘ U.hom) ≫ (ρ_ (SM.X 0)).hom) ≫ S.hom) = f
    simp only [Category.assoc]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    have hTensor :
        ((((𝟙 (K.X p) ≫ f) ≫ S.inv) ≫ 𝟙 (SM.X 0)) ⊗ₘ
          (((U.inv ≫ 𝟙 (I.X 0)) ≫ 𝟙 (I.X 0)) ≫ U.hom)) =
        (f ≫ S.inv) ⊗ₘ (U.inv ≫ U.hom) := by
      have hFirst :
          (((𝟙 (K.X p) ≫ f) ≫ S.inv) ≫ 𝟙 (SM.X 0)) =
            f ≫ S.inv := by
        exact (congrArg (fun k => (k ≫ S.inv) ≫ 𝟙 (SM.X 0))
          (Category.id_comp f)).trans (Category.comp_id (f ≫ S.inv))
      have hSecond :
          (((U.inv ≫ 𝟙 (I.X 0)) ≫ 𝟙 (I.X 0)) ≫ U.hom) =
            U.inv ≫ U.hom := by
        exact (congrArg (fun k => k ≫ U.hom)
          (Category.comp_id (U.inv ≫ 𝟙 (I.X 0)))).trans
            (congrArg (fun k => k ≫ U.hom) (Category.comp_id U.inv))
      rw [hFirst, hSecond]
    rw [hTensor, Iso.inv_hom_id, MonoidalCategory.tensorHom_id]
    rw [MonoidalCategory.rightUnitor_naturality_assoc (f ≫ S.inv) S.hom]
    rw [Iso.inv_hom_id_assoc, Category.assoc, S.inv_hom_id,
      Category.comp_id]
  exact ConcreteCategory.congr_hom hRaw z

end HomologicalComplex

end
