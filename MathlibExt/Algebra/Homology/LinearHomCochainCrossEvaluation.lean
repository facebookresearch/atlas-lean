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

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import MathlibExt.Algebra.Homology.ChainGradedPairingHomologyAdapter
public import MathlibExt.Algebra.Homology.GradedPairingHomology
import MathlibExt.Algebra.Homology.CochainChainPairingDinaturality
import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyLaws
public import MathlibExt.Algebra.Homology.LinearHomCochainEvaluation
public import MathlibExt.Algebra.Homology.LinearHomCochainPairing
import MathlibExt.Algebra.Homology.LinearHomCochainPairingHomotopyNaturality
import MathlibExt.Algebra.Homology.TensorUnitor
import MathlibExt.Algebra.Homology.TensorHomFunctoriality
import MathlibExt.Algebra.Homology.LinearHomCochainChainPairingLeftNaturality

/-!
# Linear-Hom external pairings evaluated on homology cross products

An external linear-Hom cochain pairing and a homology cross product evaluate
as the tensor of the two factor evaluations.  The main theorem permits the
chain cross product and coproduct to be inverse only up to homotopy.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace HomologicalComplex

variable (R : Type u) [CommRing R]

/-- The monoidal structure on chain complexes of `R`-modules used in this
file, installed locally so that tensor notation refers to the total-complex
tensor product. -/
noncomputable local instance linearHomCrossEvaluationMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory
    (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- Evaluation of the identity-tensor external cochain pairing against the
identity-tensor homology pairing is the middle-four tensor of the two factor
evaluations, followed by the coefficient pairing. -/
public theorem linearHomCochainTensorEvaluation
    {K₁ K₂ : ChainComplex (ModuleCat.{u} R) ℕ} [K₁.HasTensor K₂]
    (M N L : ModuleCat.{u} R) (mu : M ⊗ N ⟶ L) (p q : ℕ) :
    (((linearHomCochainGradedPairing R
        (𝟙 (tensorObj K₁ K₂)) mu).pairHomology p q) ⊗ₘ
      (ChainGradedPairing.pairHomology
        (𝟙 (tensorObj K₁ K₂))
        (ChainGradedPairing.homologyDescentData
          (𝟙 (tensorObj K₁ K₂))) p q)) ≫
      linearHomCochainEvaluationHomology R (tensorObj K₁ K₂) L (p + q) =
    tensorμ
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
          (op K₁)).homology p)
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).obj
          (op K₂)).homology q)
        (K₁.homology p) (K₂.homology q) ≫
      (linearHomCochainEvaluationHomology R K₁ M p ⊗ₘ
        linearHomCochainEvaluationHomology R K₂ N q) ≫ mu := by
  let C₁ := (linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
    (op K₁)
  let C₂ := (linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).obj
    (op K₂)
  let T := tensorObj K₁ K₂
  let cup := linearHomCochainGradedPairing R (𝟙 T) mu
  let cross : ChainGradedPairing K₁ K₂ T := 𝟙 T
  let crossH := ChainGradedPairing.pairHomology cross
    (ChainGradedPairing.homologyDescentData cross) p q
  let evalT := linearHomCochainEvaluationHomology R T L (p + q)
  let eval₁ := linearHomCochainEvaluationHomology R K₁ M p
  let eval₂ := linearHomCochainEvaluationHomology R K₂ N q
  change (cup.pairHomology p q ⊗ₘ crossH) ≫
      linearHomCochainEvaluationHomology R T L (p + q) = _
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_fourfold'
  intro alpha beta x y
  obtain ⟨alpha₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (C₁.homologyπ p)).mp inferInstance alpha
  obtain ⟨beta₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (C₂.homologyπ q)).mp inferInstance beta
  obtain ⟨x₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K₁.homologyπ p)).mp inferInstance x
  obtain ⟨y₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K₂.homologyπ q)).mp inferInstance y
  change
    evalT.hom
        ((cup.pairHomology p q).hom
            ((C₁.homologyπ p).hom alpha₀ ⊗ₜ[R]
              (C₂.homologyπ q).hom beta₀) ⊗ₜ[R]
          crossH.hom
            ((K₁.homologyπ p).hom x₀ ⊗ₜ[R]
              (K₂.homologyπ q).hom y₀)) =
      mu.hom
        (eval₁.hom
            ((C₁.homologyπ p).hom alpha₀ ⊗ₜ[R]
              (K₁.homologyπ p).hom x₀) ⊗ₜ[R]
          eval₂.hom
            ((C₂.homologyπ q).hom beta₀ ⊗ₜ[R]
              (K₂.homologyπ q).hom y₀))
  rw [HomologicalComplex.CochainGradedPairing.pairHomology_π_apply R cup]
  have hCross := ConcreteCategory.congr_hom
    (ChainGradedPairing.tensor_homologyπ_comp_pairHomology cross
      (ChainGradedPairing.homologyDescentData cross) p q)
    (x₀ ⊗ₜ[R] y₀)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hCross
  rw [hCross]
  rw [linearHomCochainEvaluationHomology_π_apply R T L (p + q)]
  rw [linearHomCochainEvaluationHomology_π_apply R K₁ M p,
    linearHomCochainEvaluationHomology_π_apply R K₂ N q]
  let CT := (linearHomCochainComplexFunctor R (ModuleCat.{u} R) L).obj
    (op T)
  let alpha := (C₁.iCycles p).hom alpha₀
  change (K₁.X p ⟶ M) at alpha
  let beta := (C₂.iCycles q).hom beta₀
  change (K₂.X q ⟶ N) at beta
  let xraw := (K₁.iCycles p).hom x₀
  let yraw := (K₂.iCycles q).hom y₀
  let cupCycle := (cup.pairCycles p q).hom (alpha₀ ⊗ₜ[R] beta₀)
  let crossCycle := (ChainGradedPairing.pairCycles cross
    (ChainGradedPairing.homologyDescentData cross) p q).hom
      (x₀ ⊗ₜ[R] y₀)
  change
    ((CT.iCycles (p + q)).hom cupCycle).hom
        ((T.iCycles (p + q)).hom crossCycle) =
      mu.hom (alpha.hom xraw ⊗ₜ[R] beta.hom yraw)
  have hCupCycles := ConcreteCategory.congr_hom
    (cup.pairCycles_i p q) (alpha₀ ⊗ₜ[R] beta₀)
  have hCrossCycles := ConcreteCategory.congr_hom
    (ChainGradedPairing.pairCycles_i cross
      (ChainGradedPairing.homologyDescentData cross) p q)
    (x₀ ⊗ₜ[R] y₀)
  change (CT.iCycles (p + q)).hom cupCycle =
    (cup.pair p q).hom (alpha ⊗ₜ[R] beta) at hCupCycles
  change
    (T.iCycles (p + q)).hom crossCycle =
      (cross.pair p q).hom (xraw ⊗ₜ[R] yraw) at hCrossCycles
  rw [hCupCycles, hCrossCycles]
  rw [linearHomCochainGradedPairing_pair]
  have hCupApply :=
    linearHomCochainPair_tmul R (𝟙 T) mu p q alpha beta
  simp only [HomologicalComplex.id_f, Category.id_comp] at hCupApply
  have hCupEval := congrArg
    (fun k : T.X (p + q) ⟶ L =>
      k.hom ((cross.pair p q).hom (xraw ⊗ₜ[R] yraw))) hCupApply
  have hCrossPair :
      cross.pair p q = ιTensorObj K₁ K₂ p q (p + q) rfl := by
    dsimp only [cross]
    unfold ChainGradedPairing.pair
    rw [HomologicalComplex.id_f, Category.comp_id]
  calc
    _ = (linearHomPairingDesc R mu p q alpha beta).hom
        ((cross.pair p q).hom (xraw ⊗ₜ[R] yraw)) := hCupEval
    _ = (linearHomPairingDesc R mu p q alpha beta).hom
        ((ιTensorObj K₁ K₂ p q (p + q) rfl).hom
          (xraw ⊗ₜ[R] yraw)) := by rw [hCrossPair]
    _ = _ := by
      have hDesc := ConcreteCategory.congr_hom
        (ιTensorObj_comp_linearHomPairingDesc R mu p q p q rfl
          alpha beta) (xraw ⊗ₜ[R] yraw)
      simpa only [dite_eq_left, ModuleCat.comp_apply,
        ModuleCat.MonoidalCategory.tensorHom_tmul] using hDesc

/-- If a chain cross product followed by a chain coproduct is homotopic to
the identity, evaluation of the induced external cohomology product on the
induced homology cross product is the middle-four tensor of factor
evaluations. -/
public theorem linearHomCochainCrossEvaluation_of_homotopy
    {K₁ K₂ K₀ K₃ : ChainComplex (ModuleCat.{u} R) ℕ}
    [K₁.HasTensor K₂]
    (sigma : tensorObj K₁ K₂ ⟶ K₀) (c : K₀ ⟶ K₃)
    (a : K₃ ⟶ tensorObj K₁ K₂)
    (h : _root_.Homotopy ((sigma ≫ c) ≫ a) (𝟙 _))
    (M N L : ModuleCat.{u} R) (mu : M ⊗ N ⟶ L) (p q : ℕ) :
    (((linearHomCochainGradedPairing R a mu).pairHomology p q) ⊗ₘ
      (ChainGradedPairing.pairHomology sigma
          (ChainGradedPairing.homologyDescentData sigma) p q ≫
        K₀.homologyMap c (p + q))) ≫
      linearHomCochainEvaluationHomology R K₃ L (p + q) =
    tensorμ
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj
          (op K₁)).homology p)
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).obj
          (op K₂)).homology q)
        (K₁.homology p) (K₂.homology q) ≫
      (linearHomCochainEvaluationHomology R K₁ M p ⊗ₘ
        linearHomCochainEvaluationHomology R K₂ N q) ≫ mu := by
  let T := tensorObj K₁ K₂
  let s := sigma ≫ c
  let cupId := linearHomCochainGradedPairing R (𝟙 T) mu
  let cupA := linearHomCochainGradedPairing R a mu
  let crossId : ChainGradedPairing K₁ K₂ T := 𝟙 T
  let crossS : ChainGradedPairing K₁ K₂ K₃ := s
  let H := linearHomCochainComplexFunctor R (ModuleCat.{u} R) L
  let fK := H.map s.op
  let evalT := linearHomCochainEvaluationGradedPairing R T L
  let eval₃ := linearHomCochainEvaluationGradedPairing R K₃ L
  have hCross :
      ChainGradedPairing.pairHomology sigma
            (ChainGradedPairing.homologyDescentData sigma) p q ≫
          K₀.homologyMap c (p + q) =
        ChainGradedPairing.pairHomology crossS
          (ChainGradedPairing.homologyDescentData crossS) p q := by
    symm
    simpa only [s, crossS, HomologicalComplex.homologyMap_id,
      MonoidalCategory.id_tensorHom_id, Category.id_comp] using
      (ChainGradedPairing.pairHomology_naturality sigma
        (ChainGradedPairing.homologyDescentData sigma) crossS
        (ChainGradedPairing.homologyDescentData crossS)
        (𝟙 K₁) (𝟙 K₂) c (fun i j => by
          dsimp only [crossS, s]
          unfold ChainGradedPairing.pair
          simp only [HomologicalComplex.id_f, HomologicalComplex.comp_f,
            MonoidalCategory.id_tensorHom_id, Category.id_comp,
            Category.assoc]) p q)
  have hDelta : _root_.Homotopy
      (s ≫ a) ((𝟙 T) ≫ tensorHom (𝟙 K₁) (𝟙 K₂)) := by
    simpa only [T, s, Category.id_comp,
      HomologicalComplex.tensorHom_id_id] using h
  have hCup :
      cupId.pairHomology p q =
        cupA.pairHomology p q ≫ HomologicalComplex.homologyMap fK (p + q) := by
    have hCupRaw :=
      linearHomCochainGradedPairing_pairHomology_naturality_of_homotopy
        R a (𝟙 T) (𝟙 K₁) (𝟙 K₂) s hDelta mu p q
    simp only [op_id] at hCupRaw
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      HomologicalComplex.homologyMap_id,
      HomologicalComplex.homologyMap_id,
      MonoidalCategory.id_tensorHom_id, Category.id_comp] at hCupRaw
    simpa only [cupId, cupA, fK, T] using hCupRaw
  have hPair : ∀ i j,
      (fK.f i ⊗ₘ 𝟙 (T.X (i + j))) ≫ evalT.pair i j =
        (𝟙 (((H.obj (op K₃)).X i)) ⊗ₘ s.f (i + j)) ≫
          eval₃.pair i j := by
    intro i j
    exact linearHomCochainChainPair_naturality_left
      (R := R) (rightUnitor K₃).inv (rightUnitor T).inv s s
      (chainGradedPairingDegreeZeroAction R
        (rightUnitor ((ChainComplex.single₀ (ModuleCat.{u} R)).obj L)).hom)
      (MonoidalCategory.rightUnitor_inv_naturality s) i j
  have hEvalPair :=
    CochainChainGradedPairing.pairHomology_dinaturality
      R eval₃ evalT fK s hPair (p + q) 0
  have hEval :
      (HomologicalComplex.homologyMap fK (p + q) ⊗ₘ 𝟙 (T.homology (p + q))) ≫
          linearHomCochainEvaluationHomology R T L (p + q) =
        (𝟙 ((H.obj (op K₃)).homology (p + q)) ⊗ₘ
          T.homologyMap s (p + q)) ≫
          linearHomCochainEvaluationHomology R K₃ L (p + q) := by
    unfold linearHomCochainEvaluationHomology
    simpa only [Nat.add_zero, Category.assoc] using congrArg
      (fun k => k ≫ (singleObjHomologySelfIso
        (ComplexShape.down ℕ) 0 L).hom) hEvalPair
  rw [hCross]
  change (cupA.pairHomology p q ⊗ₘ
      ChainGradedPairing.pairHomology crossS
        (ChainGradedPairing.homologyDescentData crossS) p q) ≫
      linearHomCochainEvaluationHomology R K₃ L (p + q) = _
  have hCrossId :
      ChainGradedPairing.pairHomology crossS
          (ChainGradedPairing.homologyDescentData crossS) p q =
        ChainGradedPairing.pairHomology crossId
            (ChainGradedPairing.homologyDescentData crossId) p q ≫
          T.homologyMap s (p + q) := by
    simpa only [T, s, crossId, crossS, HomologicalComplex.homologyMap_id,
      MonoidalCategory.id_tensorHom_id, Category.id_comp] using
      (ChainGradedPairing.pairHomology_naturality crossId
        (ChainGradedPairing.homologyDescentData crossId) crossS
        (ChainGradedPairing.homologyDescentData crossS)
        (𝟙 K₁) (𝟙 K₂) s (fun i j => by
          dsimp only [crossId, crossS, s]
          unfold ChainGradedPairing.pair
          simp only [HomologicalComplex.id_f, HomologicalComplex.comp_f,
            MonoidalCategory.id_tensorHom_id, Category.id_comp,
            Category.assoc]
          rw [← Category.assoc, Category.comp_id]) p q)
  rw [hCrossId]
  have hTensorRight :
      cupA.pairHomology p q ⊗ₘ
          (ChainGradedPairing.pairHomology crossId
              (ChainGradedPairing.homologyDescentData crossId) p q ≫
            T.homologyMap s (p + q)) =
        (cupA.pairHomology p q ⊗ₘ
            ChainGradedPairing.pairHomology crossId
              (ChainGradedPairing.homologyDescentData crossId) p q) ≫
          (𝟙 _ ⊗ₘ T.homologyMap s (p + q)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  rw [hTensorRight]
  simp only [Category.assoc]
  rw [← hEval]
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  rw [← hCup]
  exact linearHomCochainTensorEvaluation R M N L mu p q

end HomologicalComplex

end
