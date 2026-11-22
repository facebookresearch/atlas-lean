/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOrthogonalHEPOmegaPushoutGluing
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOmegaMappingOrdinalClosure
import MathlibExt.CategoryTheory.MorphismProperty.CoproductClosure

/-!
# Coproduct closure of original orthogonal HEP Omega equivalences

The conjunction of genuine based HEP and all original Omega-target tests is
closed under continuous transfinite composition and arbitrary small coproducts.
The coproduct argument uses the original coordinate pushout chain and cocone.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.OriginalHEPOmegaClosure

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  MonoidalClosed.enrichedCategorySelf PointedCGWH.EnrichedMapping.hasSmallLimits
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The actual original HEP/Omega class uses the earned continuous ordinal
theorem on every original small shape. -/
instance originalHEPOmega_transfinite :
    (originalHEPOmega (B := B)).IsStableUnderTransfiniteComposition.{v} where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    unfold originalHEPOmega
    infer_instance

/-- The same genuine HEP/Omega class has every original coproduct, through
its complete actual coordinate pushout chain and endpoint cocone. -/
instance originalHEPOmega_coproducts :
    (originalHEPOmega (B := B)).IsStableUnderCoproducts.{v} :=
  MorphismProperty.isStableUnderCoproducts_of_cobase_transfinite (originalHEPOmega (B := B))

/-- The actual original coproduct of genuine HEP/Omega arrows remains in
that same class, with every original source and target component retained. -/
theorem originalHEPOmega_coproductMap {J : Type v}
    {X Y : J → Actual.OrthogonalCarrier.{u, v}} (f : ∀ j, X j ⟶ Y j)
    (hf : ∀ j, originalHEPOmega (B := B) (f j)) :
    originalHEPOmega (B := B) (Limits.Sigma.map f) :=
  MorphismProperty.coproductMap_mem_of_cobase_transfinite (originalHEPOmega (B := B)) f hf

end PointedCGWH.Spectra.Orthogonal.OriginalHEPOmegaClosure
