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

public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Compact open operators have finite-dimensional targets

An open compact continuous linear map has finite-dimensional target over a
complete nontrivially normed scalar field. Neither ambient space is assumed
complete, and surjectivity is unnecessary. The proof uses the stock Riesz
criterion on an actual compact neighborhood of zero in the target.
-/

@[expose] public section

open Filter Set Topology

universe u𝕜 uE uF

namespace FiniteDimensional

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An open compact continuous linear map has finite-dimensional target.
Only the scalar field, not either ambient space, is assumed complete. -/
theorem of_isCompactOperator_of_isOpenMap (f : E →L[𝕜] F)
    (hCompact : IsCompactOperator f) (hOpen : IsOpenMap f) : FiniteDimensional 𝕜 F := by
  obtain ⟨K, hK, hPre⟩ := hCompact
  have hImage : f '' (f ⁻¹' K) ∈ 𝓝 (0 : F) := by
    simpa only [map_zero] using hOpen.image_mem_nhds hPre
  have hK0 : K ∈ 𝓝 (0 : F) :=
    mem_of_superset hImage (image_preimage_subset f K)
  exact FiniteDimensional.of_totallyBounded_nhds_zero 𝕜 hK0 hK.totallyBounded

end FiniteDimensional
