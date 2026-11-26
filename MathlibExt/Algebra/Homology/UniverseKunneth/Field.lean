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

public import MathlibExt.Algebra.Homology.UniverseKunneth.ScalarPairing
public import MathlibExt.Algebra.Homology.UniverseKunneth.Braiding
public import MathlibExt.Algebra.Homology.Kunneth.Collapse
public import Mathlib.Algebra.Field.ULift

/-!
# Scalar transport and field Künneth in a larger coefficient universe

Let R be a commutative ring in universe u and W=max(u,v) for an independent lift height v. Its
lifted copy R̂ lies in W. Restriction of scalars S identifies R̂-modules and R-modules in W,
with inverse T and their canonical chain, tensor, graded and homology comparisons. For chain
complexes K,L over R, these comparisons give ψ:H(K)⊗H(L)≅S_G(H(TK)⊗H(TL)) and
θ:H(K⊗L)≅S_G(H(TK⊗TL)).

The cycle tensorators satisfy μ_R≫θ.hom=ψ.hom≫S_G(μ_R̂), so scalar transport identifies the
specified Künneth maps. When R=k is a field, the field Künneth map over k̂ is invertible; hence
μ_k is invertible in every degree and as a graded map. Together with the canonical unit
comparison, it gives a monoidal graded-homology functor on nonnegative chain complexes over k in
W. The scalar comparison statements preceding the field specialization hold over every
commutative ring.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.UniverseKunneth

variable {R : Type u} [CommRing R]


/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. Write R̂ for the canonical lifted copy of R in W, S for restriction from
R̂-modules to R-modules, and S_C,S_G for its termwise chain and graded functors. For a chain
complex K over R̂ of shape down ℕ, this is the graded isomorphism σ_K:H_R(S_CK)≅S_G(H_R̂(K)).
Its component in degree n∈ℕ is the canonical scalar-restriction homology comparison. The
restriction retains the carriers in W and changes only the scalar action. -/
def mappedHomologyIso (K : ChainComplex (ModuleCat.{max u v} (ModuleCat.UniverseScalarRestriction.LiftedRing.{u,v} R))
    ℕ) : (homologyFunctor (R := R)).obj ((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj K) ≅
    (ModuleCat.UniverseScalarRestriction.gradedFunctor.{u,v} R).obj ((HomologicalComplex.Kunneth.homologyFunctor).obj
    K) :=
  GradedObject.isoMk _ _ (ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R K)

@[reassoc]
private theorem mappedHomologyIso_hom_apply
    (K : ChainComplex (ModuleCat.{max u v}
      (ModuleCat.UniverseScalarRestriction.LiftedRing.{u,v} R)) ℕ) (n : ℕ) :
    (mappedHomologyIso K).hom n =
      (ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R K n).hom := rfl

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. Write R̂ for the canonical lifted copy of R in W, S for restriction from
R̂-modules to R-modules, and S_C,S_G for its termwise chain and graded functors. Let K,L be
chain complexes over R̂ of shape down ℕ. Write c:S_CK⊗_R S_CL≅S_C(K⊗_R̂ L) for the
tensor-complex comparison, g for the graded tensor comparison, and σ for the homology
comparisons. Then μ_R(S_CK,S_CL)≫H_R(c.hom)≫σ_{K⊗L}.hom=(σ_K.hom⊗σ_L.hom)≫g.hom≫S_G(μ_R̂(K,L)).
Both sides map H_R(S_CK)⊗H_R(S_CL) to S_G(H_R̂(K⊗L)). -/
@[reassoc]
theorem mapped_tensorator (K L : ChainComplex (ModuleCat.{max u v}
    (ModuleCat.UniverseScalarRestriction.LiftedRing.{u,v} R)) ℕ) :
    tensorator ((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj K)
    ((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj L) ≫
      (homologyFunctor (R := R)).map (ModuleCat.UniverseScalarRestriction.complexTensorIso.{u,v} R K L).hom ≫
      (mappedHomologyIso (K ⊗ L) (R := R)).hom =
    ((mappedHomologyIso K (R := R)).hom ⊗ₘ (mappedHomologyIso L (R := R)).hom) ≫
      (ModuleCat.UniverseScalarRestriction.gradedTensorIso.{u,v} R ((HomologicalComplex.Kunneth.homologyFunctor).obj
    K) ((HomologicalComplex.Kunneth.homologyFunctor).obj L)).hom ≫
      (ModuleCat.UniverseScalarRestriction.gradedFunctor.{u,v} R).map (HomologicalComplex.Kunneth.tensorator K L) := by
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  change GradedObject.Monoidal.ιTensorObj
      (homologyFunctor.obj ((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj K))
      (homologyFunctor.obj ((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj L))
      p q n h ≫ tensorator _ _ n ≫ homologyMap _ n ≫ (mappedHomologyIso (K ⊗ L)).hom n =
    GradedObject.Monoidal.ιTensorObj
      (homologyFunctor.obj ((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj K))
      (homologyFunctor.obj ((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj L))
      p q n h ≫ (((mappedHomologyIso K).hom ⊗ₘ (mappedHomologyIso L).hom) n) ≫
      (ModuleCat.UniverseScalarRestriction.gradedTensorIso.{u,v} R
        (HomologicalComplex.Kunneth.homologyFunctor.obj K)
        (HomologicalComplex.Kunneth.homologyFunctor.obj L)).hom n ≫ _
  change _ = _
  rw [ι_tensorator_assoc]
  simp only [mappedHomologyIso_hom_apply]
  change _ = GradedObject.Monoidal.ιTensorObj _ _ p q n h ≫
    GradedObject.Monoidal.tensorHom (mappedHomologyIso K).hom (mappedHomologyIso L).hom n ≫ _
  rw [GradedObject.Monoidal.ι_tensorHom_assoc,
    ModuleCat.UniverseScalarRestriction.ι_gradedTensorIso_hom_assoc]
  rw [← Functor.map_comp]
  have hHigh := HomologicalComplex.Kunneth.ι_tensorator K L p q n h
  have hHigh' := congrArg (fun x =>
    ((ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R K p).hom ⊗ₘ
      (ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R L q).hom) ≫
      (ModuleCat.UniverseScalarRestriction.tensorIso.{u,v} R (K.homology p) (L.homology q)).hom ≫
      (ModuleCat.UniverseScalarRestriction.toOriginal.{u,v} R).map x) hHigh
  simp only [mappedHomologyIso_hom_apply]
  have hHighEq := hHigh'
  change _ = _ at hHighEq
  have hMiddle : (pair
      ((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj K)
      ((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj L) p q ≫
      (homologyIsoOfEq
        (((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj K) ⊗
          ((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj L)) h).hom) ≫
      homologyMap (ModuleCat.UniverseScalarRestriction.complexTensorIso.{u,v} R K L).hom n ≫
      (ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R (K ⊗ L) n).hom =
    ((ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R K p).hom ⊗ₘ
      (ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R L q).hom) ≫
      (ModuleCat.UniverseScalarRestriction.tensorIso.{u,v} R (K.homology p) (L.homology q)).hom ≫
      (ModuleCat.UniverseScalarRestriction.toOriginal.{u,v} R).map
        (HomologicalComplex.Kunneth.pair K L p q ≫ (homologyIsoOfEq (K ⊗ L) h).hom) := by
    have hPair := ModuleCat.UniverseScalarRestriction.pair_scalar_transport.{u,v} R K L p q
    have hDegree := ModuleCat.UniverseScalarRestriction.homologyComparison_degree_transport.{u,v} R
      (K ⊗ L) h
    have hNatural := homologyIsoOfEq_hom_naturality
      (ModuleCat.UniverseScalarRestriction.complexTensorIso.{u,v} R K L).hom h
    calc
      _ = pair _ _ p q ≫ homologyMap
          (ModuleCat.UniverseScalarRestriction.complexTensorIso.{u,v} R K L).hom (p + q) ≫
          (HomologicalComplex.homologyIsoOfEq
            ((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj (K ⊗ L)) h).hom ≫
          (ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R (K ⊗ L) n).hom := by
        simpa only [Category.assoc] using congrArg (fun x => pair _ _ p q ≫ x ≫
          (ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R (K ⊗ L) n).hom) hNatural.symm
      _ = _ := by
        have hDegree' := congrArg (fun x => pair
          ((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj K)
          ((ModuleCat.UniverseScalarRestriction.complexFunctor.{u,v} R).obj L) p q ≫
          homologyMap (ModuleCat.UniverseScalarRestriction.complexTensorIso.{u,v} R K L).hom
            (p + q) ≫ x) hDegree
        exact hDegree'.trans (by
          simpa only [Functor.map_comp, Category.assoc] using congrArg (fun x => x ≫
            (ModuleCat.UniverseScalarRestriction.toOriginal.{u,v} R).map
              (HomologicalComplex.homologyIsoOfEq (K ⊗ L) h).hom) hPair.symm)
  exact hMiddle.trans hHighEq.symm

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. Write R̂ for the canonical lifted copy of R in W, S for restriction from
R̂-modules to R-modules, and S_C,S_G for its termwise chain and graded functors. Let T_C be the
inverse chain scalar functor and K a chain complex over R of shape down ℕ. The counit
ε_K:S_C(T_CK)≅K and σ_{T_CK}:H_R(S_C(T_CK))≅S_G(H_R̂(T_CK)) give this isomorphism
H_R(K)≅S_G(H_R̂(T_CK)), with forward map H_R(ε_K)^{-1}≫σ_{T_CK}.hom. -/
def representationHomologyIso (K : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ) :
    (homologyFunctor (R := R)).obj K ≅ (ModuleCat.UniverseScalarRestriction.gradedFunctor.{u,v} R).obj
    ((HomologicalComplex.Kunneth.homologyFunctor).obj ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v}
    R).obj K)) :=
  GradedObject.isoMk _ _ fun n =>
    (ModuleCat.UniverseScalarRestriction.originalHomologyIso.{u,v} R K n).symm ≪≫
      ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R
    ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K) n

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. Write R̂ for the canonical lifted copy of R in W, S for restriction from
R̂-modules to R-modules, and S_C,S_G for its termwise chain and graded functors. For chain
complexes K,L over R of shape down ℕ, let T_C represent them over R̂. This source comparison is
ψ:H_R(K)⊗_R H_R(L)≅S_G(H_R̂(T_CK)⊗_R̂ H_R̂(T_CL)). It tensors the two representation homology
isomorphisms and then applies the graded scalar tensor comparison. -/
def tensorSourceIso (K L : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ) :
    (homologyFunctor (R := R)).obj K ⊗ (homologyFunctor (R := R)).obj L ≅
    (ModuleCat.UniverseScalarRestriction.gradedFunctor.{u,v} R).obj ((HomologicalComplex.Kunneth.homologyFunctor).obj
    ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K) ⊗
    (HomologicalComplex.Kunneth.homologyFunctor).obj ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v}
    R).obj L)) :=
  (representationHomologyIso K ⊗ᵢ representationHomologyIso L) ≪≫
    ModuleCat.UniverseScalarRestriction.gradedTensorIso.{u,v} R ((HomologicalComplex.Kunneth.homologyFunctor).obj
    ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K))
    ((HomologicalComplex.Kunneth.homologyFunctor).obj ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v}
    R).obj L))

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. Write R̂ for the canonical lifted copy of R in W, S for restriction from
R̂-modules to R-modules, and S_C,S_G for its termwise chain and graded functors. For chain
complexes K,L over R of shape down ℕ and their lifted-ring representations T_CK,T_CL, this
target comparison is θ:H_R(K⊗_R L)≅S_G(H_R̂(T_CK⊗_R̂ T_CL)). Its component in degree n is the
inverse homology map of the canonical tensor-complex counit S_C(T_CK⊗T_CL)≅K⊗L, followed by the
scalar-restriction homology comparison. -/
def tensorTargetIso (K L : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ) :
    (homologyFunctor (R := R)).obj (K ⊗ L) ≅ (ModuleCat.UniverseScalarRestriction.gradedFunctor.{u,v} R).obj
    ((HomologicalComplex.Kunneth.homologyFunctor).obj ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v}
    R).obj K ⊗ (ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L)) :=
  GradedObject.isoMk _ _ fun n =>
    (HomologicalComplex.homologyMapIso
      (ModuleCat.UniverseScalarRestriction.originalTensorComplexIso.{u,v} R K L) n).symm ≪≫
      ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R
    ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K ⊗
    (ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L) n

private theorem representationHomologyIso_hom (K : ChainComplex
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ) (n : ℕ) :
    (representationHomologyIso K).hom n =
      (HomologicalComplex.homologyMapIso
        (ModuleCat.UniverseScalarRestriction.originalComplexIso.{u,v} R K) n).inv ≫
      (ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K) n).hom := rfl

private theorem tensorTargetIso_hom (K L : ChainComplex
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ) (n : ℕ) :
    (tensorTargetIso K L).hom n =
      (HomologicalComplex.homologyMapIso
        (ModuleCat.UniverseScalarRestriction.originalTensorComplexIso.{u,v} R K L) n).inv ≫
      (ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K ⊗
          (ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L) n).hom := rfl

private theorem originalTensorHomologyComparison
    (K L : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ) :
    homologyFunctor.map
      ((ModuleCat.UniverseScalarRestriction.originalComplexIso.{u,v} R K).hom ⊗ₘ
        (ModuleCat.UniverseScalarRestriction.originalComplexIso.{u,v} R L).hom) ≫
      (tensorTargetIso K L).hom =
    homologyFunctor.map
      (ModuleCat.UniverseScalarRestriction.complexTensorIso.{u,v} R
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K)
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L)).hom ≫
      (mappedHomologyIso
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K ⊗
          (ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L)).hom := by
  let f := (ModuleCat.UniverseScalarRestriction.originalComplexIso.{u,v} R K).hom
  let g := (ModuleCat.UniverseScalarRestriction.originalComplexIso.{u,v} R L).hom
  funext n
  change homologyMap (f ⊗ₘ g) n ≫ (tensorTargetIso K L).hom n =
    homologyMap
      (ModuleCat.UniverseScalarRestriction.complexTensorIso.{u,v} R
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K)
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L)).hom n ≫
      (mappedHomologyIso
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K ⊗
        (ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L)).hom n
  rw [tensorTargetIso_hom, mappedHomologyIso_hom_apply]
  let e := ModuleCat.UniverseScalarRestriction.originalComplexIso.{u,v} R K ⊗ᵢ
    ModuleCat.UniverseScalarRestriction.originalComplexIso.{u,v} R L
  have he : (f ⊗ₘ g) ≫ e.inv ≫
      (ModuleCat.UniverseScalarRestriction.complexTensorIso.{u,v} R
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K)
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L)).hom =
    (ModuleCat.UniverseScalarRestriction.complexTensorIso.{u,v} R
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K)
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L)).hom := by
    have hHom : f ⊗ₘ g = e.hom := by
      apply HomologicalComplex.hom_ext
      intro i
      dsimp only [e, f, g]
      rw [MonoidalCategory.tensorIso_hom]

    exact (congrArg (fun x => x ≫ e.inv ≫
      (ModuleCat.UniverseScalarRestriction.complexTensorIso.{u,v} R
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K)
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L)).hom) hHom).trans
      (Iso.hom_inv_id_assoc e _)
  have hMapped := congrArg (fun x => homologyMap x n ≫
    (ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R
      ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K ⊗
        (ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L) n).hom) he
  dsimp only [e, HomologicalComplex.Kunneth.homologyFunctor,
    HomologicalComplex.gradedHomologyFunctor] at hMapped ⊢
  simpa only [ModuleCat.UniverseScalarRestriction.originalTensorComplexIso,
    HomologicalComplex.homologyMapIso_inv, Iso.trans_inv, Iso.symm_inv,
    HomologicalComplex.homologyMap_comp, Category.assoc] using hMapped

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v) the
coefficient universe. Write R̂ for the canonical lifted copy of R in W, S for restriction from
R̂-modules to R-modules, and S_C,S_G for its termwise chain and graded functors. For chain
complexes K,L over R of shape down ℕ, let ψ and θ be the source and target comparison
isomorphisms for their lifted-ring representations T_CK,T_CL. The canonical cycle tensorators
satisfy μ_R(K,L)≫θ.hom=ψ.hom≫S_G(μ_R̂(T_CK,T_CL)). Thus the scalar comparison carries the full
graded Künneth map, including every homogeneous antidiagonal component. -/
@[reassoc]
theorem tensorator_scalar_transport (K L : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ) :
    tensorator K L ≫ (tensorTargetIso K L).hom =
      (tensorSourceIso K L).hom ≫ (ModuleCat.UniverseScalarRestriction.gradedFunctor.{u,v} R).map
    (HomologicalComplex.Kunneth.tensorator ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K)
    ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L)) := by
  let f := (ModuleCat.UniverseScalarRestriction.originalComplexIso.{u,v} R K).hom
  let g := (ModuleCat.UniverseScalarRestriction.originalComplexIso.{u,v} R L).hom
  apply (cancel_epi ((homologyFunctor (R := R)).map f ⊗ₘ (homologyFunctor (R := R)).map g)).1
  rw [← Category.assoc, tensorator_naturality]
  have htarget := originalTensorHomologyComparison (R := R) K L
  have hsource : ((homologyFunctor (R := R)).map f ⊗ₘ (homologyFunctor (R := R)).map g) ≫ (tensorSourceIso K L).hom =
      ((mappedHomologyIso ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K)).hom ⊗ₘ
    (mappedHomologyIso ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L)).hom) ≫
        (ModuleCat.UniverseScalarRestriction.gradedTensorIso.{u,v} R
          ((HomologicalComplex.Kunneth.homologyFunctor).obj
    ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K))
    ((HomologicalComplex.Kunneth.homologyFunctor).obj ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v}
    R).obj L))).hom := by
    have hK : homologyFunctor.map f ≫ (representationHomologyIso K).hom =
        (mappedHomologyIso ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K)).hom := by
      funext n
      change homologyMap f n ≫ (representationHomologyIso K).hom n = _
      rw [representationHomologyIso_hom, mappedHomologyIso_hom_apply]
      change (HomologicalComplex.homologyMapIso
          (ModuleCat.UniverseScalarRestriction.originalComplexIso.{u,v} R K) n).hom ≫
        (HomologicalComplex.homologyMapIso
          (ModuleCat.UniverseScalarRestriction.originalComplexIso.{u,v} R K) n).inv ≫ _ = _
      exact Iso.hom_inv_id_assoc _ _
    have hL : homologyFunctor.map g ≫ (representationHomologyIso L).hom =
        (mappedHomologyIso ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L)).hom := by
      funext n
      change homologyMap g n ≫ (representationHomologyIso L).hom n = _
      rw [representationHomologyIso_hom, mappedHomologyIso_hom_apply]
      change (HomologicalComplex.homologyMapIso
          (ModuleCat.UniverseScalarRestriction.originalComplexIso.{u,v} R L) n).hom ≫
        (HomologicalComplex.homologyMapIso
          (ModuleCat.UniverseScalarRestriction.originalComplexIso.{u,v} R L) n).inv ≫ _ = _
      exact Iso.hom_inv_id_assoc _ _
    unfold tensorSourceIso
    rw [Iso.trans_hom]
    change (homologyFunctor.map f ⊗ₘ homologyFunctor.map g) ≫
      ((representationHomologyIso K).hom ⊗ₘ (representationHomologyIso L).hom) ≫ _ = _
    have hTensor :
        ((homologyFunctor.map f ≫ (representationHomologyIso K).hom) ⊗ₘ
          (homologyFunctor.map g ≫ (representationHomologyIso L).hom)) =
        ((mappedHomologyIso ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K)).hom ⊗ₘ
          (mappedHomologyIso ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L)).hom) :=
      congrArg₂ (fun a b => a ⊗ₘ b) hK hL
    have hComp : (homologyFunctor.map f ⊗ₘ homologyFunctor.map g) ≫
        ((representationHomologyIso K).hom ⊗ₘ (representationHomologyIso L).hom) =
      ((homologyFunctor.map f ≫ (representationHomologyIso K).hom) ⊗ₘ
        (homologyFunctor.map g ≫ (representationHomologyIso L).hom)) := by
      exact MonoidalCategory.tensorHom_comp_tensorHom
        (homologyFunctor.map f) (homologyFunctor.map g)
        (representationHomologyIso K).hom (representationHomologyIso L).hom
    have h := congrArg (fun x => x ≫
      (ModuleCat.UniverseScalarRestriction.gradedTensorIso.{u,v} R
        (HomologicalComplex.Kunneth.homologyFunctor.obj
          ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K))
        (HomologicalComplex.Kunneth.homologyFunctor.obj
          ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L))).hom)
      (hComp.trans hTensor)
    exact (Category.assoc _ _ _).symm.trans h
  rw [Category.assoc, htarget]
  have hs := congrArg (fun z => z ≫
    (ModuleCat.UniverseScalarRestriction.gradedFunctor.{u,v} R).map
      (HomologicalComplex.Kunneth.tensorator
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K)
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L))) hsource
  exact (mapped_tensorator ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K)
    ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj L)).trans ((Category.assoc _ _ _).symm.trans
    hs.symm)

section Field

variable {k : Type u} [Field k]


private theorem liftedFieldTensorator_isIso
    (K L : ChainComplex
      (ModuleCat.{max u v} (ModuleCat.UniverseScalarRestriction.LiftedRing.{u,v} k)) ℕ)
    (n : ℕ) : IsIso (HomologicalComplex.Kunneth.tensorator K L n) := by
  letI : Field (ModuleCat.UniverseScalarRestriction.LiftedRing.{u,v} k) :=
    (ULift.field : Field (ULift.{v} k))
  rw [HomologicalComplex.Kunneth.tensorator_eq]
  exact IsIso.comp_isIso'
    (f := (HomologicalComplex.Kunneth.antidiagonalIso K L n).hom)
    (h := HomologicalComplex.kunnethHomologyTensorMap K L n)
    (HomologicalComplex.Kunneth.antidiagonalIso K L n).isIso_hom
    (HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field
      (k := ModuleCat.UniverseScalarRestriction.LiftedRing.{u,v} k) K L n)

/-- Let k be a field in universe u and W=max(u,v) for an independent lift height v. For arbitrary
chain complexes K,L of shape down ℕ with k-module terms in W, the canonical cycle tensorator
μ:H(K)⊗_k H(L)→H(K⊗_k L) is an isomorphism. In degree n it is the Künneth map from the sum of
H_pK⊗H_qL over p+q=n. The conclusion follows through the scalar comparison with the lifted field
k̂ in W. -/
theorem isIso_tensorator_of_field (K L : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) : IsIso
    (tensorator K L) := by
  let K0 : ChainComplex (ModuleCat.{max u v}
    (ModuleCat.UniverseScalarRestriction.LiftedRing.{u,v} k)) ℕ :=
      (ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} k).obj K
  let L0 : ChainComplex (ModuleCat.{max u v}
    (ModuleCat.UniverseScalarRestriction.LiftedRing.{u,v} k)) ℕ :=
      (ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} k).obj L
  have hIso : ∀ n : ℕ, IsIso (HomologicalComplex.Kunneth.tensorator K0 L0 n) := by
    intro n
    exact liftedFieldTensorator_isIso (k := k) K0 L0 n
  letI := hIso
  letI : IsIso (HomologicalComplex.Kunneth.tensorator K0 L0) :=
    GradedObject.isIso_of_isIso_apply (HomologicalComplex.Kunneth.tensorator K0 L0)
  have h : tensorator K L = (tensorSourceIso K L).hom ≫
      (ModuleCat.UniverseScalarRestriction.gradedFunctor.{u,v} k).map (HomologicalComplex.Kunneth.tensorator
    ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} k).obj K)
    ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} k).obj L)) ≫
        (tensorTargetIso K L).inv := by
    apply (cancel_mono (tensorTargetIso K L).hom).1
    rw [tensorator_scalar_transport]
    simp
  have hNative : IsIso (HomologicalComplex.Kunneth.tensorator
      ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} k).obj K)
      ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} k).obj L)) := by
    exact (inferInstance : IsIso (HomologicalComplex.Kunneth.tensorator K0 L0))
  letI := hNative
  have hMap : IsIso ((ModuleCat.UniverseScalarRestriction.gradedFunctor.{u,v} k).map
      (HomologicalComplex.Kunneth.tensorator
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} k).obj K)
        ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} k).obj L))) :=
    Functor.map_isIso _ _
  letI := hMap
  rw [h]
  infer_instance

/-- Let k be a field in universe u, v an independent lift height and W=max(u,v). Graded homology
from k-linear chain complexes of shape down ℕ in W to ℕ-graded k-modules has a monoidal
structure whose unit map is the canonical comparison 𝟙≅H(𝟙) and whose tensorator is the cycle
Künneth isomorphism H(K)⊗H(L)≅H(K⊗L). Its associativity and unit laws are the cycle-pairing
coherence laws. -/
def monoidalOfField :
    (homologyFunctor (R := k) : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ ⥤ GradedObject ℕ
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)).Monoidal := by
  letI : (homologyFunctor (R := k)).LaxMonoidal := laxMonoidal
  letI : ∀ K L : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ, IsIso (tensorator K L) :=
    isIso_tensorator_of_field
  letI : IsIso (Functor.LaxMonoidal.ε (homologyFunctor (R := k))) := by
    change IsIso (unitMap.{u,v} (R := k))
    infer_instance
  letI : ∀ A B, IsIso (Functor.LaxMonoidal.μ (homologyFunctor (R := k)) A B) := by
    intro A B
    change IsIso (tensorator A B)
    infer_instance
  exact Functor.Monoidal.ofLaxMonoidal (homologyFunctor (R := k))

end Field

end HomologicalComplex.UniverseKunneth
