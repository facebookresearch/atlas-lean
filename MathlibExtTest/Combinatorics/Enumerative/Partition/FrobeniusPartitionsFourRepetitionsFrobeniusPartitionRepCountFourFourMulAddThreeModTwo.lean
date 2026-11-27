/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.FrobeniusPartitionsFourRepetitionsFrobeniusPartitionRepCountFourFourMulAddThreeModTwo
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.ModEq
import MathlibExt.Combinatorics.Enumerative.Partition.LevelFiveEulerDissection
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProduct

/-!
# Tests for parity of Frobenius partitions with four repetitions

The examples apply the parity theorem to partitions of seven and eleven.
-/

namespace MathlibExtTest.Combinatorics.Enumerative.Partition
namespace FrobeniusPartitionsFourRepetitionsFrobeniusPartitionRepCountFourFourMulAddThreeModTwo

public section

example : MetaMathlibExt.frobeniusPartitionRepCount 4 7 ≡ 0 [MOD 2] := by
  simpa using MetaMathlibExt.frobeniusPartitionRepCount_four_four_mul_add_three_mod_two 1

example : 2 ∣ MetaMathlibExt.frobeniusPartitionRepCount 4 11 := by
  apply Nat.modEq_zero_iff_dvd.mp
  simpa using MetaMathlibExt.frobeniusPartitionRepCount_four_four_mul_add_three_mod_two 2

end

end FrobeniusPartitionsFourRepetitionsFrobeniusPartitionRepCountFourFourMulAddThreeModTwo
end MathlibExtTest.Combinatorics.Enumerative.Partition
