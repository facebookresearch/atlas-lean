/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoGeneratedNumericalSemigroup
import Mathlib.NumberTheory.FrobeniusNumber

namespace TwoGeneratedNumericalSemigroupTest

private theorem reflect_three_five (x : ℕ) (hx : x ≤ 7) :
    x ∈ AddSubmonoid.closure ({3, 5} : Set ℕ) ↔ 7 - x ∉ AddSubmonoid.closure ({3, 5} : Set ℕ) := by
  have hF : FrobeniusNumber 7 {3, 5} :=
    frobeniusNumber_pair (m := 3) (n := 5) (by decide) (by decide) (by decide)
  obtain ⟨hgap, hmax⟩ := frobeniusNumber_iff.mp hF
  exact MetaMathlibExt.numericalSemigroup_two_generated_symmetric hgap hmax x hx

-- Reflection exchanges the endpoints 0 and 7.
example : 7 ∉ AddSubmonoid.closure ({3, 5} : Set ℕ) :=
  (reflect_three_five 0 (by decide)).mp (zero_mem _)

-- Reflecting the generator 3 gives the interior gap 4.
example : 4 ∉ AddSubmonoid.closure ({3, 5} : Set ℕ) :=
  (reflect_three_five 3 (by decide)).mp (AddSubmonoid.subset_closure (by simp))

-- Reflecting the gap 1 gives the semigroup element 6.
example : 6 ∈ AddSubmonoid.closure ({3, 5} : Set ℕ) := by
  apply (reflect_three_five 6 (by decide)).mpr
  rw [AddSubmonoid.mem_closure_pair]
  simp only [smul_eq_mul]
  omega

end TwoGeneratedNumericalSemigroupTest
