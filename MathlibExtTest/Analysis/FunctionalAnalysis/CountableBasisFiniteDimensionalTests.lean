/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import MathlibExt.Analysis.FunctionalAnalysis.CountableBasisFiniteDimensional

/-!
# Tests for finite-dimensionality from a countable Hamel basis

* `Fin 3 → ℝ` is finite-dimensional, via its standard basis
  `Pi.basisFun`, which is indexed by the countable (finite) type `Fin 3`.
* `Fin 2 → ℂ` is finite-dimensional, via `Pi.basisFun`.
* `ℝ` is finite-dimensional, via the singleton basis indexed by `PUnit`.
* The contrapositive is usable on `ℓ²(ℕ, ℝ)`: assuming `ℓ²(ℕ, ℝ)` is
  not finite-dimensional, no Hamel basis of it is indexed by a countable
  type.
-/

open MathlibExt.Analysis.FunctionalAnalysis.CountableBasisFiniteDimensional
open scoped lp

namespace MathlibExtTest.Analysis.FunctionalAnalysis.CountableBasisFiniteDimensionalTests

/-- `Fin 3 → ℝ` is finite-dimensional, via its standard basis. -/
example : FiniteDimensional ℝ (Fin 3 → ℝ) :=
  finiteDimensional_of_countable_basis (Pi.basisFun ℝ (Fin 3))

/-- `Fin 2 → ℂ` is finite-dimensional, via its standard basis. -/
example : FiniteDimensional ℂ (Fin 2 → ℂ) :=
  finiteDimensional_of_countable_basis (Pi.basisFun ℂ (Fin 2))

/-- `ℝ` is finite-dimensional, via the singleton basis. -/
example : FiniteDimensional ℝ ℝ :=
  finiteDimensional_of_countable_basis (Module.Basis.singleton (ι := PUnit.{1}) ℝ)

/-- The contrapositive applies to `ℓ²(ℕ, ℝ)`: if it is not
finite-dimensional, then no Hamel basis of it has a countable index type. -/
example (h : ¬ FiniteDimensional ℝ ℓ²(ℕ, ℝ)) {ι : Type*}
    (b : Module.Basis ι ℝ ℓ²(ℕ, ℝ)) : ¬ Countable ι :=
  not_countable_basis_of_not_finiteDimensional h b

end MathlibExtTest.Analysis.FunctionalAnalysis.CountableBasisFiniteDimensionalTests
