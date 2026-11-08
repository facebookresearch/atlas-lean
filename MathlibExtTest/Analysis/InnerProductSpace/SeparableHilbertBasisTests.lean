/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.PiL2
import MathlibExt.Analysis.InnerProductSpace.SeparableHilbertBasis

/-!
# Tests for separability from a countable Hilbert basis

* `ℓ²(ℕ, ℂ)` is separable, via its canonical (identity) Hilbert basis.
* `ℓ²(Fin 3, ℝ)` is separable, via its canonical Hilbert basis.
* `EuclideanSpace ℂ (Fin 2)` is separable, via the Hilbert basis obtained
  from its standard orthonormal basis `EuclideanSpace.basisFun`.
* The separability instance is usable: `ℓ²(ℕ, ℂ)` has a countable dense set.
-/

open TopologicalSpace Set
open scoped lp
open MathlibExt.Analysis.InnerProductSpace.SeparableHilbertBasis

namespace MathlibExtTest.Analysis.InnerProductSpace.SeparableHilbertBasisTests

/-- `ℓ²(ℕ, ℂ)` is separable, via its canonical Hilbert basis. -/
example : SeparableSpace ℓ²(ℕ, ℂ) :=
  separableSpace_of_countable_hilbertBasis (default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ))

/-- `ℓ²(Fin 3, ℝ)` is separable, via its canonical Hilbert basis. -/
example : SeparableSpace ℓ²(Fin 3, ℝ) :=
  separableSpace_of_countable_hilbertBasis (default : HilbertBasis (Fin 3) ℝ ℓ²(Fin 3, ℝ))

/-- `EuclideanSpace ℂ (Fin 2)` is separable, via the Hilbert basis obtained
from its standard orthonormal basis. -/
example : SeparableSpace (EuclideanSpace ℂ (Fin 2)) :=
  separableSpace_of_countable_hilbertBasis
    (EuclideanSpace.basisFun (Fin 2) ℂ).toHilbertBasis

/-- The separability conclusion is usable: `ℓ²(ℕ, ℂ)` has a countable dense set. -/
example : ∃ s : Set ℓ²(ℕ, ℂ), s.Countable ∧ Dense s :=
  @TopologicalSpace.exists_countable_dense _ _
    (separableSpace_of_countable_hilbertBasis (default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ)))

end MathlibExtTest.Analysis.InnerProductSpace.SeparableHilbertBasisTests
