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
# Finite-dimensional target of an open compact map

Let `𝕜` be a complete nontrivially normed field and `E,F` normed `𝕜`-spaces. A bounded linear
map `f : E → F` that is both compact and open has finite-dimensional target `F` over `𝕜`.

Completeness of `E` or `F` and surjectivity of `f` are not premises. The conclusion follows from
a compact neighborhood of zero in `F`.
-/

@[expose] public section

open Filter Set Topology

universe u𝕜 uE uF

namespace FiniteDimensional

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **An open compact linear map has finite-dimensional target.** Let `𝕜` be a complete
nontrivially normed field and `E,F` normed `𝕜`-spaces, possibly incomplete. If `f : E
→L[𝕜] F` is compact and open, then `FiniteDimensional 𝕜 F`. Surjectivity is not assumed. -/
theorem of_isCompactOperator_of_isOpenMap (f : E →L[𝕜] F)
    (hCompact : IsCompactOperator f) (hOpen : IsOpenMap f) : FiniteDimensional 𝕜 F := by
  obtain ⟨K, hK, hPre⟩ := hCompact
  have hImage : f '' (f ⁻¹' K) ∈ 𝓝 (0 : F) := by
    simpa only [map_zero] using hOpen.image_mem_nhds hPre
  have hK0 : K ∈ 𝓝 (0 : F) :=
    mem_of_superset hImage (image_preimage_subset f K)
  exact FiniteDimensional.of_totallyBounded_nhds_zero 𝕜 hK0 hK.totallyBounded

end FiniteDimensional
