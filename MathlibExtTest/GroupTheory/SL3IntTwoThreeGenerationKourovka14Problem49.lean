/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SL3IntTwoThreeGenerationKourovka14Problem49

open Matrix
open MathlibExt.GroupTheory.SL3IntTwoThreeGenerationKourovka14Problem49Wanted

namespace SL3IntTwoThreeGenerationTest

private def involution : SpecialLinearGroup (Fin 3) ℤ :=
  .mk !![1, 1, 0; 0, -1, 0; 0, 0, -1] (by decide)

private def cycle : SpecialLinearGroup (Fin 3) ℤ :=
  .mk !![0, 0, 1; 1, 0, 0; 0, 1, 0] (by decide)

-- Both prescribed orders occur, even with the involution nontrivial modulo two.
example : orderOf involution = 2 ∧ orderOf cycle = 3 ∧
    Subgroup.closure {involution, cycle} ≠ ⊤ := by
  have ha : orderOf involution = 2 := orderOf_eq_prime (by decide) (by decide)
  have hb : orderOf cycle = 3 := orderOf_eq_prime (by decide) (by decide)
  exact ⟨ha, hb, fun hg => sl3IntGeneratedByOrderTwoAndThree_refuted ⟨_, _, ha, hb, hg⟩⟩

end SL3IntTwoThreeGenerationTest
