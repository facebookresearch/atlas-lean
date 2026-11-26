/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.EnhancedConvolutionModels
public import MathlibExt.AlgebraicGeometry.CoefficientSheafDimensionModels
public import Mathlib.Topology.Compactness.SigmaCompact
public import MathlibExt.AlgebraicGeometry.EnhancedConvolutionSourceRequestsActualBoundedProperImageOfFiniteAmplitude

import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Boundedness of the actual Ind inverse image

The model's given exact Ind inverse image preserves bounded cohomology on the native derived
categories: this is the boundedness consequence of inverse image preserving both halves of the
standard t-structure.

Source: D'Agnolo--Kashiwara, arXiv:1311.2374v2, Section 2 conventions and Proposition 3.4.4(ii).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.EnhancedConvolutionSourceRequests

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafCoefficientModels
open MathlibExt.AlgebraicGeometry.IndSheafInverseImageModels
open MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
open MathlibExt.AlgebraicGeometry.BoundedIndImageModels
open MathlibExt.AlgebraicGeometry.BorderedRealSpaceModels
open MathlibExt.AlgebraicGeometry.BorderedIndDerivedModels
open MathlibExt.AlgebraicGeometry.EnhancedIndQuotientModels
open MathlibExt.AlgebraicGeometry.BorderedGraphKernelModels
open MathlibExt.AlgebraicGeometry.BorderedRealTimeModels
open MathlibExt.AlgebraicGeometry.BoundedIndOperationSources
open MathlibExt.AlgebraicGeometry.EnhancedConvolutionModels
open MathlibExt.AlgebraicGeometry.CoefficientSheafDimensionModels

attribute [local instance] requestAbelianPreadditive

attribute [local instance] HasDerivedCategory.standard

/-- The original exact Ind inverse image preserves actual bounded cohomology. -/
theorem actual_bounded_inverse_image_source (k : Type) [Field k] (X Y : TopCat.{0})
    [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (S : OrdinaryIndSource k X) (D : IndInverseImageSource k f S)
    [(indInverseImage k f S D).Additive] (E : ExactIndInverseImageSource k f S D) :
    BoundedInverseImageSource k f S D E
    := by
  constructor
  intro K
  obtain ⟨a, b, hK⟩ := K.property
  have : K.obj.IsGE a := (DerivedCategory.isGE_iff K.obj a).2
    (fun n hn => hK n (Or.inl hn))
  have : K.obj.IsLE b := (DerivedCategory.isLE_iff K.obj b).2
    (fun n hn => hK n (Or.inr hn))
  obtain ⟨L, _, _, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE K.obj a b
  let F := indInverseImage k f S D
  let L' := (F.mapHomologicalComplex (.up ℤ)).obj L
  let e' := (derivedIndInverseImage k f S D E).mapIso e ≪≫
    (derivedInverseImageComparison k f S D E).app L
  refine ⟨a, b, fun n hn => ?_⟩
  have hL' : Limits.IsZero
      ((DerivedCategory.homologyFunctor (IndSheaf k X) n).obj (DerivedCategory.Q.obj L')) := by
    rcases hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE (DerivedCategory.Q.obj L') a n hn
    · exact DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj L') b n hn
  exact hL'.of_iso ((DerivedCategory.homologyFunctor (IndSheaf k X) n).mapIso e')

end WantedExt.AlgebraicGeometry.EnhancedConvolutionSourceRequests
