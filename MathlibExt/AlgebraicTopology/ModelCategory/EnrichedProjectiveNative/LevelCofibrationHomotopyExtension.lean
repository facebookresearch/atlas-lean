/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.HomotopyExtensionClosure

/-!
# Native projective cofibrations and based homotopy extension

For any pointed CGWH-enriched index, the left class of the original free
boundary generators has based homotopy extension against every target.
The property persists under coproducts, pushouts and continuous ordinal
compositions. Thus every cofibration of the original native projective model
has based homotopy extension, without a cofibrant source hypothesis.
-/

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalMonoidHEPClosure

section OriginalIndex

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf

/-- The original free boundary left class has based HEP against every target. -/
theorem originalI_leftClass_le_basedHEP :
    (HomotopicalAlgebra.EnrichedProjective.generators
      (A := I) PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp.llp ≤
        PointedCGWH.EnrichedBasedHomotopyExtension.property := by
  have hI : HomotopicalAlgebra.EnrichedProjective.generators
      (A := I) PointedCGWH.realizedBoundaryInclusions.{u, v} ≤
        (PointedCGWH.Spectra.Orthogonal.OriginalIClosedHomotopyExtension.cotensorEndpointFamily
          (I := I)).llp := by
    rw [← PointedCGWH.Spectra.Orthogonal.OriginalIClosedHomotopyExtension.nativeHEP_eq_llp]
    exact PointedCGWH.Spectra.Orthogonal.OriginalIClosedHomotopyExtension.originalFreeI_le_nativeHEP
  rw [PointedCGWH.Spectra.Orthogonal.OriginalIClosedHomotopyExtension.nativeHEP_eq_llp]
  exact MorphismProperty.antitone_llp
    ((MorphismProperty.le_llp_iff_le_rlp _ _).mp hI)

/-- Coproducts, pushouts and continuous ordinal compositions retain based HEP. -/
theorem cellularClosure_le_basedHEP
    (P : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hP : P ≤ PointedCGWH.EnrichedBasedHomotopyExtension.property) :
    transfiniteCompositions.{w} (coproducts.{w} P).pushouts ≤
      PointedCGWH.EnrichedBasedHomotopyExtension.property := by
  have hC : coproducts.{w} P ≤ PointedCGWH.EnrichedBasedHomotopyExtension.property :=
    (MorphismProperty.coproducts_monotone hP).trans
      (PointedCGWH.Spectra.Orthogonal.OriginalIClosedHomotopyExtension.nativeHEP_coproducts_le
        (I := I))
  have hU : (coproducts.{w} P).pushouts ≤
      PointedCGWH.EnrichedBasedHomotopyExtension.property :=
    (MorphismProperty.pushouts_monotone hC).trans
      (PointedCGWH.Spectra.Orthogonal.OriginalIClosedHomotopyExtension.nativeHEP_pushouts_le
        (I := I))
  exact (MorphismProperty.transfiniteCompositions_monotone hU).trans
    (MorphismProperty.transfiniteCompositions_le _)

end OriginalIndex

section OriginalLevel

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  MonoidalClosed.enrichedCategorySelf

/-- Native projective cofibrations have based HEP on arbitrary source objects. -/
theorem nativeCofibrations_le_basedHEP :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) ≤
      PointedCGWH.EnrichedBasedHomotopyExtension.property := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.cofibrations_eq]
  exact originalI_leftClass_le_basedHEP

end OriginalLevel

end PointedCGWH.Spectra.OriginalMonoidHEPClosure
