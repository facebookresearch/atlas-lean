/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.DerivedLocalMapping

/-!
# Omega tests for the original stabilization arrows

The full original native stabilization family passes every Omega-target
Hom test through its actual mapping-end transpose and its original
cofibrant free endpoints. Index comparisons and gamma corollaries use
this same generic theorem.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.EnrichedFunctorCat MonoidalCategory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.IndexKan

variable {A L : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory

/-- Every original stabilization arrow passes all source-family Omega tests through its
actual original full mapping-end precomposition map. -/
theorem originalStabilization_omegaTests (s : NativeStabilizationFamily.{u, v} A L) (l : L) :
    NativeK.omegaTests s (NativeK.stabilization s l) := by
  let _ : IsCofibrant (Free.object (s.target l) (s.coefficient l)) :=
    NativeK.stabilization_source_cofibrant s l
  let _ : IsCofibrant (Free.object (s.source l) (𝟙_ PointedCGWH.{u, v})) :=
    NativeK.stabilization_target_cofibrant s l
  apply DerivedLocalMapping.omegaTests_of_mappingPre_weak s (NativeK.stabilization s l)
  intro E hE
  exact (NativeK.stabilization_mapping_weak_iff s l E).mpr (hE l)

end PointedCGWH.Spectra.Orthogonal.IndexKan
