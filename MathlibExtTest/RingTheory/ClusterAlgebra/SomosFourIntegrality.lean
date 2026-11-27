/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.ClusterAlgebra.SomosFourIntegrality
import Mathlib.Tactic.NormNum

/-!
# Tests for Somos-4 integrality
-/

namespace MathlibExtTest.RingTheory.ClusterAlgebra.SomosFourIntegrality

open MathlibExt.RingTheory.ClusterAlgebra LaurentPhenomenonWanted

example (m : ℕ) : ∃ z : ℤ, somos4 m = z := somos4_isInt m

-- By index 10, the recurrence has divided by 2, 3, and 7.
example : ∃ z : ℤ, somos4 10 = z ∧ z = 1529 := by
  obtain ⟨z, hz⟩ := somos4_isInt 10
  have hvalue : somos4 10 = (1529 : ℤ) := by norm_num [somos4]
  exact ⟨z, hz, Int.cast_injective (hz.symm.trans hvalue)⟩

end MathlibExtTest.RingTheory.ClusterAlgebra.SomosFourIntegrality
