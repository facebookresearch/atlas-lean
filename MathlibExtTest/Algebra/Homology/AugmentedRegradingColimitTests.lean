/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.AugmentedModelTransport
import MathlibExt.Algebra.Homology.ChainComplex.SignedRegradingHomology
import MathlibExt.Algebra.Homology.RootAdjoinedUnderCokernelColimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Data.ZMod.Basic
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Nonzero augmented, regraded and fixed-source colimit coordinates

Reduction from ZMod6 to ZMod2 gives a coaugmentation with value 3 ↦ 1.
An integer chain with differential multiplication by two acquires the value
four under signed regrading. Its signed homology comparison commutes with
cycle quotient maps. The same nonzero complex is the fixed source of a
supported identity-pair colimit. Adjoining that source recovers the correct
carrier and cokernel colimits; forgetting it fails to preserve this coproduct.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ChainComplex

namespace MathlibExtTest.AugmentedRegradingColimit

private abbrev C := ModuleCat.{0} ℤ
private abbrev N6 : C := ModuleCat.of ℤ (ZMod 6)
private abbrev N2 : C := ModuleCat.of ℤ (ZMod 2)
private def reduction : N6 ⟶ N2 := ModuleCat.ofHom
  ((ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)).toAddMonoidHom.toIntLinearMap)
private def coaugmented : CosimplicialObject.Augmented C where
  left := N6
  right := (CosimplicialObject.const C).obj N2
  hom := (CosimplicialObject.const C).map reduction
private abbrev cochainPresentation :=
  CosimplicialObject.Augmented.cochainCoaugmentationFunctor.obj coaugmented

private lemma coaugmentation_value :
    (cochainPresentation.hom.f 0).hom (3 : ZMod 6) = (1 : ZMod 2) := by
  change reduction.hom (3 : ZMod 6) = (1 : ZMod 2)
  decide

example : (cochainPresentation.hom.f 0).hom (3 : ZMod 6) = (1 : ZMod 2) := coaugmentation_value
example : (cochainPresentation.hom.f 0).hom (3 : ZMod 6) ≠ 0 := by
  intro hz
  exact (by decide : (1 : ZMod 2) ≠ 0) (coaugmentation_value.symm.trans hz)

private abbrev twice : N6 ⟶ N6 := (2 : ℤ) • 𝟙 N6
private def K : ChainComplex C ℤ where
  X _ := N6
  d i j := if i = 1 ∧ j = 0 then twice else 0
  shape i j hij := by
    by_cases h : i = 1 ∧ j = 0
    · rcases h with ⟨rfl, rfl⟩
      exact (hij (by decide)).elim
    · exact if_neg h
  d_comp_d' i j k _ _ := by
    by_cases h : i = 1 ∧ j = 0
    · have h' : ¬ (j = 1 ∧ k = 0) := by
        intro hj
        exact (by decide : (0 : ℤ) ≠ 1) (h.2.symm.trans hj.1)
      simp only [if_pos h, if_neg h', comp_zero]
    · simp only [if_neg h, zero_comp]

private lemma original_d_value : (K.d 1 0).hom (1 : ZMod 6) = (2 : ZMod 6) := by
  change (if (1 : ℤ) = 1 ∧ (0 : ℤ) = 0 then twice else 0).hom (1 : ZMod 6) = _
  rw [if_pos (by decide)]
  change (2 : ℤ) • (1 : ZMod 6) = (2 : ZMod 6)
  decide

private lemma regraded_d_value :
    ((signedRegrading K 1).d 0 1).hom (1 : ZMod 6) = (4 : ZMod 6) := by
  change (-(2 : ℤ)) • (1 : ZMod 6) = (4 : ZMod 6)
  decide

example : (K.d 1 0).hom (1 : ZMod 6) = (2 : ZMod 6) ∧
    ((signedRegrading K 1).d 0 1).hom (1 : ZMod 6) = (4 : ZMod 6) :=
  ⟨original_d_value, regraded_d_value⟩

example :
    ((signedRegradingShortComplexIso K 1 0).hom.τ₃).hom (1 : ZMod 6) = (5 : ZMod 6) := by
  change -(1 : ZMod 6) = (5 : ZMod 6)
  decide

example : (signedRegrading K 1).homologyπ 0 ≫ (signedRegradingHomologyIso K 1 0).hom =
    (signedRegradingCyclesIso K 1 0).hom ≫ K.homologyπ 1 :=
  signedRegradingHomologyIso_hom_quotient K 1 0

private lemma fixed_source_nonzero : ¬ IsZero K := by
  intro hz
  have h := congrArg (fun f : K ⟶ K => (f.f 0).hom (1 : ZMod 6))
    (hz.eq_of_src (𝟙 K) (0 : K ⟶ K))
  change (1 : ZMod 6) = 0 at h
  exact (by decide : (1 : ZMod 6) ≠ 0) h

private abbrev identityUnder := supportedUnderIdentity K
private abbrev D := pair identityUnder identityUnder
private abbrev inclusion := (underCokernelNonnegativeProperty K).ι
private def underCocone : Cocone (D ⋙ inclusion) :=
  inclusion.mapCocone (BinaryCofan.mk (𝟙 identityUnder) (𝟙 identityUnder))
private def underColimit : IsColimit underCocone := by
  letI : CreatesColimit D inclusion := createsColimitFullSubcategoryInclusion D
    (underCokernelNonnegativeProperty_colimit K (D ⋙ inclusion)
      (fun j => (D.obj j).property))
  letI : PreservesColimit D inclusion :=
    preservesColimit_of_createsColimit_and_hasColimit D inclusion
  exact isColimitOfPreserves inclusion (isColimitSupportedUnderIdentityBinaryCofan K)
private def rootCocone : Cocone (rootAdjoinedUnderCokernelDiagram K D) :=
  WithInitial.coconeEquiv.functor.obj underCocone
private def rootColimit : IsColimit rootCocone :=
  (WithInitial.isColimitEquiv (t := underCocone)).symm underColimit

example : IsColimit (rootAdjoinedUnderCokernelCocone K rootColimit) :=
  isColimitRootAdjoinedUnderCokernelCocone K rootColimit

example : IsColimit ((underCokernel K).mapCocone
    (inclusion.mapCocone (rootAdjoinedUnderCokernelCocone K rootColimit))) :=
  isColimitRootAdjoinedUnderCokernelReduction K rootColimit

example : (rootAdjoinedUnderCokernelCocone K rootColimit).pt.obj.hom = 𝟙 K := by
  rw [rootAdjoinedUnderCokernelCocone_hom]
  change (WithInitial.coconeEquiv.functor.obj underCocone).ι.app WithInitial.star = _
  rw [WithInitial.coconeEquiv_functor_obj_ι_app_star]
  rfl

example : ¬ PreservesColimit D (inclusion ⋙ Under.forget K) :=
  bareUnderCokernelCarrier_not_preserves_identityPair K fixed_source_nonzero

end MathlibExtTest.AugmentedRegradingColimit
