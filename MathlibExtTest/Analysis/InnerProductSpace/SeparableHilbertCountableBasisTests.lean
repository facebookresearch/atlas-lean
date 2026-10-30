/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.PiL2
import MathlibExt.Analysis.InnerProductSpace.SeparableHilbertCountableBasis

/-!
# Tests for countable Hilbert bases in separable Hilbert spaces

* The standard orthonormal family in `EuclideanSpace ℝ (Fin 2)` is countable.
* `EuclideanSpace ℝ (Fin 2)` and `ℝ` have Hilbert bases indexed by countable types.
* The basis so obtained has countable range.
-/

open MathlibExt.Analysis.InnerProductSpace.SeparableHilbertCountableBasis

namespace MathlibExtTest.Analysis.InnerProductSpace.SeparableHilbertCountableBasisTests

/-- The standard orthonormal family in `EuclideanSpace ℝ (Fin 2)` is countable. -/
example : Countable (Fin 2) :=
  countable_of_orthonormal (H := EuclideanSpace ℝ (Fin 2)) EuclideanSpace.orthonormal_single

/-- `EuclideanSpace ℝ (Fin 2)` admits a Hilbert basis indexed by a countable type. -/
example : ∃ (ι : Type) (_ : Countable ι),
    Nonempty (HilbertBasis ι ℝ (EuclideanSpace ℝ (Fin 2))) :=
  exists_countable_hilbertBasis

/-- `ℝ` admits a Hilbert basis indexed by a countable type. -/
example : ∃ (ι : Type) (_ : Countable ι), Nonempty (HilbertBasis ι ℝ ℝ) :=
  exists_countable_hilbertBasis

/-- The Hilbert basis obtained for `EuclideanSpace ℝ (Fin 2)` has countable range. -/
example : ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis ι ℝ (EuclideanSpace ℝ (Fin 2))),
    (Set.range b).Countable := by
  obtain ⟨ι, hι, ⟨b⟩⟩ := exists_countable_hilbertBasis (𝕜 := ℝ)
    (H := EuclideanSpace ℝ (Fin 2))
  have := hι
  exact ⟨ι, hι, b, Set.countable_range b⟩

end MathlibExtTest.Analysis.InnerProductSpace.SeparableHilbertCountableBasisTests
