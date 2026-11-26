/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FibStepConvolutionCompProdSumEven

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.FibStepConvolutionCompProdSumEven` -/

namespace MathlibExtTest.Combinatorics.Enumerative.FibStepConvolutionCompProdSumEven

open MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

-- l = 1, m = 2, n = 4: T_4 - F_4 = 4 - 3.
example : compProdSum (fun (j : Fin 2) k => fibStep (2 + j.val) k) 2 = 1 := by
  rw [compProdSum_even 1 2 4 (by decide) (by decide) (by decide)]
  decide

-- l = 1, m = 2, n = 5: T_5 - F_5 = 7 - 5.
example : compProdSum (fun (j : Fin 2) k => fibStep (2 + j.val) k) 3 = 2 := by
  rw [compProdSum_even 1 2 5 (by decide) (by decide) (by decide)]
  decide

-- l = 2, m = 1, n = 8: two consecutive pairs above the shift.
example : compProdSum (fun (j : Fin 4) k => fibStep (1 + j.val) k) 4 = 1 := by
  rw [compProdSum_even 2 1 8 (by decide) (by decide) (by decide)]
  decide

-- l = 2, m = 2, n = 10: two consecutive pairs above the shift.
example : compProdSum (fun (j : Fin 4) k => fibStep (2 + j.val) k) 4 = 1 := by
  rw [compProdSum_even 2 2 10 (by decide) (by decide) (by decide)]
  decide

end MathlibExtTest.Combinatorics.Enumerative.FibStepConvolutionCompProdSumEven
