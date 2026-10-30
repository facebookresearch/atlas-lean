/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.TreePercolation

/-!
# Tests for `MathlibExt.Probability.Percolation.TreePercolation`

* `binomialOffspringPMF` and `treeGF` at small inputs.
* `treePc_eq`: the critical parameter of the binary tree is `1/2`.
* `survivalProb` vanishes at `p = 1/4` and is positive at `p = 3/4` on the binary tree.
* `treeMean` equals the derivative of the generating function at `1`.
-/

@[expose] public section

open StatMech.Percolation

namespace MathlibExtTest.StatMech.Probability.Percolation.TreePercolation

example : binomialOffspringPMF 2 (1 / 2) 1 = 1 / 2 := by
  norm_num [binomialOffspringPMF]

example : treeGF 2 (1 / 2) 0 = 1 / 4 := by
  norm_num [treeGF]

example : treeGF 3 (1 / 3) 1 = 1 := treeGF_one 3 (1 / 3)

example : ∑ k ∈ Finset.range 4, binomialOffspringPMF 3 (1 / 5) k = 1 :=
  binomialOffspringPMF_sum 3 (1 / 5)

example : treeMean 2 (1 / 2) = deriv (treeGF 2 (1 / 2)) 1 := treeMean_eq_deriv 2 (1 / 2)

/-- The critical parameter of the binary tree. -/
example : treePc 2 = 1 / 2 := by
  rw [treePc_eq 2 (by norm_num)]; norm_num

example : survivalProb 2 (1 / 4) = 0 :=
  survivalProb_eq_zero_of_lt_treePc 2 (by norm_num) (by norm_num) (by norm_num)

example : 0 < survivalProb 2 (3 / 4) :=
  survivalProb_pos_of_gt_treePc 2 (by norm_num) (by norm_num) (by norm_num)

end MathlibExtTest.StatMech.Probability.Percolation.TreePercolation
