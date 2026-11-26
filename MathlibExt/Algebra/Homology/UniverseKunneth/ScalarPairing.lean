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
# Scalar compatibility of cycle and homology Künneth pairings

Let R be a commutative ring in universe u, W=max(u,v), and R̂ its lifted copy in W. Restricting
scalars S from R̂ to R has canonical tensor, cycle and homology comparisons. For chain complexes
K,L over R̂ of shape down ℕ, these comparisons carry the tensor of cycles in degrees p,q to the
same degree p+q cycle pairing in the restricted tensor complex.

Writing c:S_CK⊗_R S_CL≅S_C(K⊗_R̂ L), z_K:Z_p(S_CK)≅S(Z_pK), and t for the module tensor
comparison, the cycle equation is (z_K⊗z_L)≫t≫S(κ^Z_KL)=κ^Z_{S_CK,S_CL}≫Z_{p+q}(c)≫z_{K⊗L}.
Replacing cycles and z by homology and its canonical comparison gives the same equation for κ^H.
The coefficient carriers stay in W while the two scalar rings are compared; no field hypothesis
is needed.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ModuleCat.UniverseScalarRestriction

variable (R : Type u) [CommRing R]


/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. Write R̂ for the canonical lifted copy of R in W, S for restriction from
R̂-modules to R-modules, and S_C,S_G for its termwise chain and graded functors. For chain
complexes K,L over R̂ of shape down ℕ and p,q∈ℕ, let z_K:Z_p(S_CK)≅S(Z_pK), z_L and z_{K⊗L} be
the cycle comparisons, t the scalar module tensor comparison and c:S_CK⊗_R S_CL≅S_C(K⊗_R̂ L) the
tensor-complex comparison. Then
(z_K.hom⊗z_L.hom)≫t.hom≫S(κ^Z_{K,L})=κ^Z_{S_CK,S_CL}≫Z_{p+q}(c.hom)≫z_{K⊗L}.hom. Both cycle
pairings tensor representatives in degrees p,q into degree p+q. -/
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

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. Write R̂ for the canonical lifted copy of R in W, S for restriction from
R̂-modules to R-modules, and S_C,S_G for its termwise chain and graded functors. For chain
complexes K,L over R̂ of shape down ℕ and p,q∈ℕ, let σ_K:H_p(S_CK)≅S(H_pK), σ_L, σ_{K⊗L}, t the
scalar tensor comparison and c the tensor-complex comparison. The homology pairings satisfy
(σ_K.hom⊗σ_L.hom)≫t.hom≫S(κ^H_{K,L})=κ^H_{S_CK,S_CL}≫H_{p+q}(c.hom)≫σ_{K⊗L}.hom. The equality is
obtained from the same cycle tensor maps by their homology quotient projections. -/
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
