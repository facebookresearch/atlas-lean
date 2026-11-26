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
* The Galton–Watson bridge: the binary tree at `p = 3/4` and the Galton–Watson process with
  offspring law `Binomial(2, 3/4)` have extinction probability `1/9`; the offspring laws `δ₀`
  (`b = 0` or `p = 0`) and `δ₂` (`b = 2`, `p = 1`) give extinction probabilities `1` and `0`.
* `survivalProb_eq_zero_iff`: the critical binary tree (`p = 1/2`) dies out, and the deterministic
  case `b = p = 1` survives although its mean is `1`.
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

/-! ### The Galton–Watson process with binomial offspring law -/

section GaltonWatsonBridge

open ProbabilityTheory MathlibExt.Probability

/-- The fixed points of `((1 + 3 s) / 4) ^ 2` in `[0, 1]` are `1/9` and `1`, so the Galton–Watson
process with offspring law `Binomial(2, 3/4)` dies out with probability `1/9`. -/
example : GaltonWatson.extinctionProb (binomial 2 ⟨3 / 4, by norm_num, by norm_num⟩) = 1 / 9 := by
  rw [← extinctionProb_eq_galtonWatson_extinctionProb]
  change extinctionProb 2 (3 / 4) = 1 / 9
  refine le_antisymm
    (csInf_le (fixedSet_bddBelow 2 _) ⟨⟨by norm_num, by norm_num⟩, by norm_num [treeGF]⟩) ?_
  refine le_csInf (fixedSet_nonempty 2 _) ?_
  rintro s ⟨⟨-, -⟩, hs⟩
  simp only [treeGF] at hs
  nlinarith [sq_nonneg (s - 1 / 9)]

/-- With no children the offspring law is `δ₀`, and extinction is certain. -/
example (p : unitInterval) : GaltonWatson.extinctionProb (binomial 0 p) = 1 := by
  have h := (survivalProb_eq_zero_iff 0 p).2 ⟨by simp, by simp⟩
  rw [survivalProb_eq_one_sub_galtonWatson_extinctionProb, sub_eq_zero] at h
  exact h.symm

/-- With closed edges (`p = 0`) the offspring law is `δ₀`, and extinction is certain. -/
example (b : ℕ) : GaltonWatson.extinctionProb (binomial b 0) = 1 := by
  have h := (survivalProb_eq_zero_iff b 0).2 ⟨by simp, by simp⟩
  rw [survivalProb_eq_one_sub_galtonWatson_extinctionProb, sub_eq_zero] at h
  exact h.symm

/-- With open edges on the binary tree (`p = 1`) the offspring law is `δ₂`: `0` is a fixed point
of `s ↦ s ^ 2`, and extinction never happens. -/
example : GaltonWatson.extinctionProb (binomial 2 1) = 0 := by
  rw [← extinctionProb_eq_galtonWatson_extinctionProb]
  exact le_antisymm (csInf_le (fixedSet_bddBelow 2 _) ⟨⟨le_rfl, zero_le_one⟩, by simp [treeGF]⟩)
    (extinctionProb_nonneg 2 _)

/-- The critical binary tree (`p = 1/2`, mean `1`) dies out. -/
example : survivalProb 2 (1 / 2) = 0 :=
  (survivalProb_eq_zero_iff 2 ⟨1 / 2, by norm_num, by norm_num⟩).2 ⟨by norm_num, by norm_num⟩

/-- The deterministic case `b = p = 1` (offspring law `δ₁`) survives although its mean is `1`: the
exception in `survivalProb_eq_zero_iff` is needed. -/
example : 0 < survivalProb 1 1 := by
  refine (survivalProb_nonneg 1 1).lt_of_ne fun h => ?_
  exact ((survivalProb_eq_zero_iff 1 1).1 h.symm).2 ⟨rfl, rfl⟩

end GaltonWatsonBridge

end MathlibExtTest.StatMech.Probability.Percolation.TreePercolation
