/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TruncatedLogResultantPos

open MetaMathlibExt Polynomial

-- The degree-one resultant is an empty product.
example : 0 < truncatedLogResultantProduct 1 :=
  truncatedLogResultantProduct_pos (hn := le_rfl)

-- In degree two the derivative has the single real root -1.
example : truncatedLogResultantProduct 2 = 1 := by
  have hlcm : truncatedLogLcm 2 = 2 := by decide
  have hindices : Finset.Icc 1 2 = {1, 2} := by decide
  have hgeom : (∑ i ∈ Finset.range 2, (X : ℤ[X]) ^ i) = X + C 1 := by
    simp [Finset.sum_range_succ, add_comm]
  unfold truncatedLogResultantProduct
  rw [hgeom, natDegree_X_add_C, resultant_X_add_C_left _ _ _ le_rfl]
  norm_num [scaledTruncatedLogPolynomial, hlcm, hindices]

-- In degree three the derivative's roots form a nonreal conjugate pair.
example : 0 < truncatedLogResultantProduct 3 :=
  truncatedLogResultantProduct_pos (hn := by decide)
