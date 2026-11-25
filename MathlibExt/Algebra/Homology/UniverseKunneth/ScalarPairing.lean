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

public import MathlibExt.Algebra.Homology.UniverseScalarComplexTensor
public import MathlibExt.Algebra.Homology.UniverseKunneth.Graded
public import MathlibExt.Algebra.Homology.Kunneth.Graded

/-!
# Canonical cycle Künneth pairings commute with actual scalar transport

Both sides are the actual identity-chain-map cycle pairings. The proof
first checks their cycle inclusions through the actual balanced tensor
and tensor-complex comparisons, then descends through original homology
quotient epis. Thus an isomorphism carried from the lifted coefficient ring
will be the canonical original-ring cycle Künneth map.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ModuleCat.UniverseScalarRestriction

variable (R : Type u) [CommRing R]


/-- The actual cycle pairings commute with the actual module and complex
tensor comparisons, before taking homology. -/
theorem cyclePair_scalar_transport (K L : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) (p q : ℕ) :
    ((cyclesComparison.{u,v} R K p).hom ⊗ₘ (cyclesComparison.{u,v} R L q).hom) ≫
      (tensorIso.{u,v} R (K.cycles p) (L.cycles q)).hom ≫ (toOriginal.{u,v} R).map
    ((HomologicalComplex.ChainGradedPairing.pairCycles (𝟙 (K ⊗ L))
        (HomologicalComplex.ChainGradedPairing.homologyDescentData (𝟙 (K ⊗ L))) p q)) =
    (HomologicalComplex.ChainGradedPairing.pairCycles
      (𝟙 ((complexFunctor.{u,v} R).obj K ⊗ (complexFunctor.{u,v} R).obj L))
      (HomologicalComplex.ChainGradedPairing.homologyDescentData
        (𝟙 ((complexFunctor.{u,v} R).obj K ⊗ (complexFunctor.{u,v} R).obj L))) p q) ≫
      HomologicalComplex.cyclesMap (complexTensorIso.{u,v} R K L).hom (p + q) ≫
      (cyclesComparison.{u,v} R (K ⊗ L) (p + q)).hom := by
  letI : Mono ((toOriginal.{u,v} R).map ((K ⊗ L).iCycles (p + q))) := inferInstance
  apply (cancel_mono ((toOriginal.{u,v} R).map ((K ⊗ L).iCycles (p + q)))).1
  have hl : (((cyclesComparison.{u,v} R K p).hom ⊗ₘ
      (cyclesComparison.{u,v} R L q).hom) ≫
      (tensorIso.{u,v} R (K.cycles p) (L.cycles q)).hom ≫
      (toOriginal.{u,v} R).map ((HomologicalComplex.ChainGradedPairing.pairCycles (𝟙 (K ⊗ L))
        (HomologicalComplex.ChainGradedPairing.homologyDescentData (𝟙 (K ⊗ L))) p q))) ≫ (toOriginal.{u,v} R).map ((K
    ⊗ L).iCycles (p + q)) =
      ((cyclesComparison.{u,v} R K p).hom ⊗ₘ (cyclesComparison.{u,v} R L q).hom) ≫
        (tensorIso.{u,v} R (K.cycles p) (L.cycles q)).hom ≫
        (toOriginal.{u,v} R).map ((K.iCycles p ⊗ₘ L.iCycles q) ≫
          HomologicalComplex.ιTensorObj K L p q (p + q) rfl) := by
    have hPair := HomologicalComplex.ChainGradedPairing.pairCycles_i
      (𝟙 (K ⊗ L))
      (HomologicalComplex.ChainGradedPairing.homologyDescentData (𝟙 (K ⊗ L))) p q
    change HomologicalComplex.ChainGradedPairing.pairCycles (𝟙 (K ⊗ L)) _ p q ≫
        (K ⊗ L).iCycles (p + q) =
      (K.iCycles p ⊗ₘ L.iCycles q) ≫
        HomologicalComplex.ιTensorObj K L p q (p + q) rfl ≫ 𝟙 ((K ⊗ L).X (p + q)) at hPair
    have hF := congrArg (fun z =>
      ((cyclesComparison.{u,v} R K p).hom ⊗ₘ (cyclesComparison.{u,v} R L q).hom) ≫
        (tensorIso.{u,v} R (K.cycles p) (L.cycles q)).hom ≫ (toOriginal.{u,v} R).map z) hPair
    have hId := Category.comp_id
      (HomologicalComplex.ιTensorObj K L p q (p + q) rfl)
    have hNorm := congrArg (fun z =>
      ((cyclesComparison.{u,v} R K p).hom ⊗ₘ (cyclesComparison.{u,v} R L q).hom) ≫
        (tensorIso.{u,v} R (K.cycles p) (L.cycles q)).hom ≫
          (toOriginal.{u,v} R).map ((K.iCycles p ⊗ₘ L.iCycles q) ≫ z)) hId
    have hF' := hF.trans hNorm
    simpa only [Functor.map_comp, Category.assoc, Category.comp_id] using hF'
  have hr : ((HomologicalComplex.ChainGradedPairing.pairCycles
      (𝟙 ((complexFunctor.{u,v} R).obj K ⊗ (complexFunctor.{u,v} R).obj L))
      (HomologicalComplex.ChainGradedPairing.homologyDescentData
        (𝟙 ((complexFunctor.{u,v} R).obj K ⊗ (complexFunctor.{u,v} R).obj L))) p q) ≫
      HomologicalComplex.cyclesMap (complexTensorIso.{u,v} R K L).hom (p + q) ≫
      (cyclesComparison.{u,v} R (K ⊗ L) (p + q)).hom) ≫
      (toOriginal.{u,v} R).map ((K ⊗ L).iCycles (p + q)) =
      ((((complexFunctor.{u,v} R).obj K).iCycles p) ⊗ₘ (((complexFunctor.{u,v} R).obj L).iCycles q)) ≫
        (tensorIso.{u,v} R (K.X p) (L.X q)).hom ≫
        (toOriginal.{u,v} R).map (HomologicalComplex.ιTensorObj K L p q (p + q) rfl) := by
    simp only [Category.assoc]
    rw [cyclesComparison_i]
    rw [HomologicalComplex.cyclesMap_i]
    have hPair := HomologicalComplex.ChainGradedPairing.pairCycles_i
      (𝟙 ((complexFunctor.{u,v} R).obj K ⊗ (complexFunctor.{u,v} R).obj L))
      (HomologicalComplex.ChainGradedPairing.homologyDescentData
        (𝟙 ((complexFunctor.{u,v} R).obj K ⊗ (complexFunctor.{u,v} R).obj L))) p q
    change HomologicalComplex.ChainGradedPairing.pairCycles
        (𝟙 ((complexFunctor.{u,v} R).obj K ⊗ (complexFunctor.{u,v} R).obj L)) _ p q ≫
        (((complexFunctor.{u,v} R).obj K) ⊗ ((complexFunctor.{u,v} R).obj L)).iCycles (p + q) =
      ((((complexFunctor.{u,v} R).obj K).iCycles p) ⊗ₘ
        (((complexFunctor.{u,v} R).obj L).iCycles q)) ≫
        HomologicalComplex.ιTensorObj ((complexFunctor.{u,v} R).obj K)
          ((complexFunctor.{u,v} R).obj L) p q (p + q) rfl ≫ 𝟙 _ at hPair
    have hP := congrArg (fun z => z ≫ (complexTensorIso.{u,v} R K L).hom.f (p + q)) hPair
    have hT := congrArg (fun z =>
      ((((complexFunctor.{u,v} R).obj K).iCycles p) ⊗ₘ
        (((complexFunctor.{u,v} R).obj L).iCycles q)) ≫ z)
      (ι_complexTensorIso_hom.{u,v} R K L p q (p + q) rfl)
    exact (Category.assoc _ _ _).symm.trans (hP.trans hT)
  rw [hl, hr, Functor.map_comp]
  have hn := tensorIso_naturality.{u,v} R (K.iCycles p) (L.iCycles q)
  have hn' := congrArg (fun z =>
    ((cyclesComparison.{u,v} R K p).hom ⊗ₘ (cyclesComparison.{u,v} R L q).hom) ≫ z ≫
      (toOriginal.{u,v} R).map (HomologicalComplex.ιTensorObj K L p q (p + q) rfl)) hn.symm
  simp only [Category.assoc] at hn'
  have hTensor :
      ((cyclesComparison.{u,v} R K p).hom ⊗ₘ (cyclesComparison.{u,v} R L q).hom) ≫
        ((toOriginal.{u,v} R).map (K.iCycles p) ⊗ₘ (toOriginal.{u,v} R).map (L.iCycles q)) =
      (((complexFunctor.{u,v} R).obj K).iCycles p ⊗ₘ
        ((complexFunctor.{u,v} R).obj L).iCycles q) := by
    rw [tensorHom_comp_tensorHom, cyclesComparison_i, cyclesComparison_i]
  have hTensor' := congrArg (fun x => x ≫ (tensorIso.{u,v} R (K.X p) (L.X q)).hom ≫
    (toOriginal.{u,v} R).map (HomologicalComplex.ιTensorObj K L p q (p + q) rfl)) hTensor
  exact hn'.trans ((Category.assoc _ _ _).symm.trans hTensor')

/-- The actual bidegree homology pairings commute with the actual scalar
restriction comparisons. This is the canonical-cycle identification. -/
@[reassoc]
theorem pair_scalar_transport (K L : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) (p q : ℕ) :
    ((homologyComparison.{u,v} R K p).hom ⊗ₘ (homologyComparison.{u,v} R L q).hom) ≫
      (tensorIso.{u,v} R (K.homology p) (L.homology q)).hom ≫
      (toOriginal.{u,v} R).map (HomologicalComplex.Kunneth.pair K L p q) =
    HomologicalComplex.UniverseKunneth.pair ((complexFunctor.{u,v} R).obj K) ((complexFunctor.{u,v} R).obj L) p q ≫
      HomologicalComplex.homologyMap (complexTensorIso.{u,v} R K L).hom (p + q) ≫
      (homologyComparison.{u,v} R (K ⊗ L) (p + q)).hom := by
  let e := (((complexFunctor.{u,v} R).obj K).homologyπ p) ⊗ₘ (((complexFunctor.{u,v} R).obj L).homologyπ q)
  letI : Epi e := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact TensorProduct.map_surjective
      ((ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi (((complexFunctor.{u,v} R).obj K).homologyπ p)))
      ((ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi (((complexFunctor.{u,v} R).obj L).homologyπ q)))
  apply (cancel_epi e).1
  have ht : e ≫ ((homologyComparison.{u,v} R K p).hom ⊗ₘ
      (homologyComparison.{u,v} R L q).hom) =
      ((cyclesComparison.{u,v} R K p).hom ⊗ₘ (cyclesComparison.{u,v} R L q).hom) ≫
        ((toOriginal.{u,v} R).map (K.homologyπ p) ⊗ₘ (toOriginal.{u,v} R).map (L.homologyπ q)) := by
    dsimp only [e]
    rw [tensorHom_comp_tensorHom, quotient_homologyComparison,
      quotient_homologyComparison, tensorHom_comp_tensorHom]
  rw [← Category.assoc e, ht]
  simp only [Category.assoc]
  rw [tensorIso_naturality_assoc]
  rw [← Functor.map_comp,
    HomologicalComplex.ChainGradedPairing.tensor_homologyπ_comp_pairHomology]
  rw [Functor.map_comp]
  simp only [e, Category.assoc]
  rw [HomologicalComplex.ChainGradedPairing.tensor_homologyπ_comp_pairHomology_assoc,
    HomologicalComplex.homologyπ_naturality_assoc]
  have hq := quotient_homologyComparison.{u,v} R (K ⊗ L) (p + q)
  have hq' := congrArg (fun z =>
    HomologicalComplex.ChainGradedPairing.pairCycles
      (𝟙 ((complexFunctor.{u,v} R).obj K ⊗ (complexFunctor.{u,v} R).obj L))
      (HomologicalComplex.ChainGradedPairing.homologyDescentData
        (𝟙 ((complexFunctor.{u,v} R).obj K ⊗ (complexFunctor.{u,v} R).obj L))) p q ≫
      HomologicalComplex.cyclesMap (complexTensorIso.{u,v} R K L).hom (p + q) ≫ z) hq
  rw [hq']
  have hc := congrArg (fun z => z ≫ (toOriginal.{u,v} R).map ((K ⊗ L).homologyπ (p + q)))
    (cyclePair_scalar_transport.{u,v} R K L p q)
  change _ = _ at hc
  exact hc

end ModuleCat.UniverseScalarRestriction
