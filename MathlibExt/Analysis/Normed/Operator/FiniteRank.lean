/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The complex or scalar-general module of bounded finite-rank maps

For normed spaces `E,F` over a nontrivially normed field `𝕜`, bounded operators with
finite-dimensional range form a `𝕜`-submodule of `E →L[𝕜] F`.

The carrier is the inverse image of the finite-range submodule of linear maps under the
forgetful map from bounded operators. Membership is equivalent to finite-dimensional range of
the underlying linear map. Completeness and finite dimension of either ambient space are not
required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ContinuousLinearMap

universe u𝕜 uE uF
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Submodule of bounded finite-rank operators.** Let `𝕜` be a nontrivially normed field and
`E,F` normed `𝕜`-spaces. `finiteRankOperator` is the submodule of `E →L[𝕜] F` consisting
of bounded maps with finite-dimensional range, obtained by taking the preimage of the
finite-range linear-map submodule. -/
abbrev finiteRankOperator : Submodule 𝕜 (E →L[𝕜] F) :=
  (LinearMap.finiteRange 𝕜 E F).comap (ContinuousLinearMap.coeLM 𝕜)

/-- **Membership in the bounded finite-rank submodule.** Let `𝕜` be a nontrivially normed
field and `E,F` normed `𝕜`-spaces. A bounded `T : E →L[𝕜] F` lies in `finiteRankOperator`
exactly when its underlying linear map has finite-dimensional range, that is,
`T.toLinearMap.HasFiniteRange`. -/
theorem mem_finiteRankOperator (T : E →L[𝕜] F) :
    T ∈ finiteRankOperator (𝕜 := 𝕜) ↔ T.toLinearMap.HasFiniteRange := by
  change T.toLinearMap.HasNoetherianRange ↔ T.toLinearMap.HasFiniteRange
  exact ⟨fun h => h.hasFiniteRange, fun h => h.hasNoetherianRange⟩

/-- **Finite-rank bounded maps as a linear-map preimage.** Let `𝕜` be a nontrivially normed
field and `E,F` normed `𝕜`-spaces. The submodule `finiteRankOperator` equals the preimage
of `LinearMap.finiteRange 𝕜 E F` under the linear map forgetting continuity. -/
theorem finiteRankOperator_eq_comap_finiteRange :
    finiteRankOperator (𝕜 := 𝕜) (E := E) (F := F) =
      (LinearMap.finiteRange 𝕜 E F).comap (ContinuousLinearMap.coeLM 𝕜) :=
  rfl

end ContinuousLinearMap
