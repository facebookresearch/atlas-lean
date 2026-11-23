/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CartesianClosed
public import MathlibExt.Topology.Category.CGWH.CartesianClosedComputations

/-!
# Joint evaluation of genuine compactly generated mapping families

A continuous family in the native internal Hom, indexed by a locally
compact Hausdorff parameter, evaluates jointly continuously on the
ordinary parameter-by-source product. The parameter is the compact
interval or square in the homotopy applications; no local compactness
is required of the active source. The native product is converted to
an ordinary product only where the existing homeomorphism theorem
applies to that parameter.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology

universe u v

namespace CGWH

variable {K A B : CGWH.{u, v}} [LocallyCompactSpace K] [T2Space K]

private def compactProductHomeomorph (A K : CGWH.{u, v})
    [LocallyCompactSpace K] [T2Space K] :
    (A ⊗ K : CGWH.{u, v}) ≃ₜ (A × K) :=
  IsHomeomorph.homeomorph (prodComparisonToTop A K)
    (prodComparisonToTop_isHomeomorph_of_locallyCompact_right A K)

private theorem compactProductHomeomorph_coordinates
    (z : A × K) :
    tensorEquivProd A K ((compactProductHomeomorph A K).symm z) = z := by
  exact (tensorEquivProd_eq_prodComparisonToTop A K _).trans
    ((compactProductHomeomorph A K).apply_symm_apply z)

private def compactParameterEvaluationRecipe (f : K ⟶ internalHom A B) :
    ContinuousMap (K × A) B :=
  (ConcreteCategory.hom (C := CGWH.{u, v}) (MonoidalClosed.uncurry f)).comp
    (((compactProductHomeomorph A K).symm : C(A × K, (A ⊗ K : CGWH.{u, v}))).comp
      (Homeomorph.prodComm K A : C(K × A, A × K)))

private theorem compactParameterEvaluationRecipe_apply
    (f : K ⟶ internalHom A B) (k : K) (a : A) :
    compactParameterEvaluationRecipe f (k, a) =
      (WithGeneratedByTopology.equiv
        (X := CompactlyGenerated.compactHausProbes.{u})
        (Y := ContinuousMapGeneratedBy
          CompactlyGenerated.compactHausProbes.{u} A B)
        (f k) : ContinuousMapGeneratedBy
          CompactlyGenerated.compactHausProbes.{u} A B) a := by
  let z := (compactProductHomeomorph A K).symm (a, k)
  have hz : tensorEquivProd A K z = (a, k) :=
    compactProductHomeomorph_coordinates (a, k)
  have ha : CartesianMonoidalCategory.fst A K z = a :=
    (tensorEquivProd_apply_fst A K z).symm.trans (congrArg Prod.fst hz)
  have hk : CartesianMonoidalCategory.snd A K z = k :=
    (tensorEquivProd_apply_snd A K z).symm.trans (congrArg Prod.snd hz)
  change MonoidalClosed.uncurry f z = _
  exact (internalHom_uncurry_apply f z).trans (by rw [ha, hk])

/-- A genuine native mapping-space family with a locally compact
Hausdorff parameter evaluates as an ordinary jointly continuous map,
even when the active source is not locally compact. -/
public def compactParameterEvaluationMap (f : K ⟶ internalHom A B) :
    ContinuousMap (K × A) B :=
  compactParameterEvaluationRecipe f

/-- The joint map is the original native family evaluated at the original
active point, with no replacement of either carrier. -/
public theorem compactParameterEvaluationMap_apply
    (f : K ⟶ internalHom A B) (k : K) (a : A) :
    compactParameterEvaluationMap f (k, a) =
      (WithGeneratedByTopology.equiv
        (X := CompactlyGenerated.compactHausProbes.{u})
        (Y := ContinuousMapGeneratedBy
          CompactlyGenerated.compactHausProbes.{u} A B)
        (f k) : ContinuousMapGeneratedBy
          CompactlyGenerated.compactHausProbes.{u} A B) a := by
  unfold compactParameterEvaluationMap
  exact compactParameterEvaluationRecipe_apply f k a

end CGWH

end
