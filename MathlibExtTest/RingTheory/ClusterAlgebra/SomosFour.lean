/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.ClusterAlgebra.SomosFour

/-!
# Tests for the Somos-4 sequence
-/

namespace MathlibExtTest.RingTheory.ClusterAlgebra.SomosFour

open MathlibExt.RingTheory.ClusterAlgebra

example : somos4 8 = 59 := somos4_four_to_nine.2.2.2.2.1

example (m : ℕ) : somos4 m ≠ 0 := (somos4_pos m).ne'

example : somos4 6 * somos4 2 = somos4 5 * somos4 3 + somos4 4 ^ 2 := somos4_add_four_mul 2

end MathlibExtTest.RingTheory.ClusterAlgebra.SomosFour
