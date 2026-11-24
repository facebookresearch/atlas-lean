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
# Bounded finite-rank operators

The scalar-general carrier reuses Mathlib's finite-range submodule by comapping
along the continuous-linear-map inclusion. The original normed domain and
range and nontrivially normed field are unchanged. Over a field, noetherian
range and finitely generated range are equivalent; the membership theorem
retains the source finite-range characterization.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ContinuousLinearMap

universe u𝕜 uE uF
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Bounded finite-rank operators are the comap of Mathlib's finite-range submodule. -/
abbrev finiteRankOperator : Submodule 𝕜 (E →L[𝕜] F) :=
  (LinearMap.finiteRange 𝕜 E F).comap (ContinuousLinearMap.coeLM 𝕜)

/-- Membership is the finite-range property on the same underlying linear map.
Use this equivalence explicitly: stock comap simp rules already normalize its left side. -/
theorem mem_finiteRankOperator (T : E →L[𝕜] F) :
    T ∈ finiteRankOperator (𝕜 := 𝕜) ↔ T.toLinearMap.HasFiniteRange := by
  change T.toLinearMap.HasNoetherianRange ↔ T.toLinearMap.HasFiniteRange
  exact ⟨fun h => h.hasFiniteRange, fun h => h.hasNoetherianRange⟩

/-- Compatibility with the canonical noetherian-range comap over the same field. -/
theorem finiteRankOperator_eq_comap_finiteRange :
    finiteRankOperator (𝕜 := 𝕜) (E := E) (F := F) =
      (LinearMap.finiteRange 𝕜 E F).comap (ContinuousLinearMap.coeLM 𝕜) :=
  rfl

end ContinuousLinearMap
