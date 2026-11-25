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
# Field Künneth in the actual original larger coefficient world

Native field collapse is invoked over the actual ring `ULift.{v} k :
Type (max u v)`, in its actual same-world module category. The original
field remains `k : Type u` in the target. Earned scalar, graded tensor,
complex tensor and native homology isomorphisms compare the actual maps.
The scalar-pairing theorem identifies the carried map with the literal
original-field cycle Künneth tensorator. No caller Künneth certificate or
universe-cumulativity identification is used.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.UniverseKunneth

variable {R : Type u} [CommRing R]


/-- The actual component homology comparisons form a native graded isomorphism. -/
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

/-- The actual mapped-complex Künneth diagram commutes on every canonical cycle summand. -/
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

/-- The original homology object is represented over the actual lifted ring,
through the actual complex counit and native homology comparison. -/
def representationHomologyIso (K : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} R) ℕ) :
    (homologyFunctor (R := R)).obj K ≅ (ModuleCat.UniverseScalarRestriction.gradedFunctor.{u,v} R).obj
    ((HomologicalComplex.Kunneth.homologyFunctor).obj ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v}
    R).obj K)) :=
  GradedObject.isoMk _ _ fun n =>
    (ModuleCat.UniverseScalarRestriction.originalHomologyIso.{u,v} R K n).symm ≪≫
      ModuleCat.UniverseScalarRestriction.homologyComparison.{u,v} R
    ((ModuleCat.UniverseScalarRestriction.toLiftedComplex.{u,v} R).obj K) n

/-- The actual tensor of original homologies compares with the actual
restriction of the lifted-ring tensor of lifted-ring homologies. -/
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

/-- Homology of the actual original tensor complex compares with the actual
restriction of homology of the actual lifted-ring tensor complex. -/
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

/-- The canonical original-field Künneth map is the actual scalar transport
of the canonical lifted-ring map under the earned source/target isomorphisms. -/
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

/-- The actual canonical original-field tensorator is invertible in the
actual larger carrier world. Existing field collapse is used only over the
actual lifted ring in its actual same-world module category. -/
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

/-- The earned canonical original-field tensorator gives the native
monoidal structure on actual larger-world graded homology. -/
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
