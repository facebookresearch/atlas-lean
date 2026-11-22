/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import MathlibExt.Analysis.FunctionalAnalysis.DiscontinuousLinearFunctional

/-!
# Tests for discontinuous linear functionals

* On `Fin 3 → ℝ`, a finite-dimensional space, every linear functional is
  continuous (the reverse direction of the iff).
* On `ℓ²(ℕ, ℝ)`, conditionally on infinite-dimensionality, there is a
  discontinuous linear functional, one that is not given by any bounded
  linear functional, and not every linear functional is continuous.
-/

open MathlibExt.Analysis.FunctionalAnalysis.DiscontinuousLinearFunctional
open scoped lp

namespace MathlibExtTest.Analysis.FunctionalAnalysis.DiscontinuousLinearFunctionalTests

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On `Fin 3 → ℝ`, every linear functional is continuous. -/
example : ∀ f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ, Continuous f :=
  forall_linearMap_continuous_iff_finiteDimensional.mpr inferInstance

/-- On `Fin 3 → ℝ`, finite-dimensionality holds via the iff. -/
example : FiniteDimensional ℝ (Fin 3 → ℝ) :=
  forall_linearMap_continuous_iff_finiteDimensional.mp
    (fun f => LinearMap.continuous_of_finiteDimensional f)

/-- On `ℓ²(ℕ, ℝ)`, conditionally on infinite-dimensionality, there is a
discontinuous linear functional. -/
example (h : ¬ FiniteDimensional ℝ ℓ²(ℕ, ℝ)) :
    ∃ f : ℓ²(ℕ, ℝ) →ₗ[ℝ] ℝ, ¬ Continuous f :=
  exists_discontinuous_linearMap_of_not_finiteDimensional h

/-- On `ℓ²(ℕ, ℝ)`, conditionally on infinite-dimensionality, not every linear
functional is continuous. -/
example (h : ¬ FiniteDimensional ℝ ℓ²(ℕ, ℝ)) :
    ¬ ∀ f : ℓ²(ℕ, ℝ) →ₗ[ℝ] ℝ, Continuous f :=
  fun hall => h (forall_linearMap_continuous_iff_finiteDimensional.mp hall)

/-- On `ℓ²(ℕ, ℝ)`, conditionally on infinite-dimensionality, there is a linear
functional not given by any bounded linear functional. -/
example (h : ¬ FiniteDimensional ℝ ℓ²(ℕ, ℝ)) :
    ∃ f : ℓ²(ℕ, ℝ) →ₗ[ℝ] ℝ, ∀ g : ℓ²(ℕ, ℝ) →L[ℝ] ℝ, f ≠ (g : ℓ²(ℕ, ℝ) →ₗ[ℝ] ℝ) :=
  exists_linearMap_not_continuousLinearMap h

end MathlibExtTest.Analysis.FunctionalAnalysis.DiscontinuousLinearFunctionalTests
