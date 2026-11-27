/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.GDifferenceBasesTendstoGroupDiffBasisNumberGaloisFieldProd

/-! # Tests for difference bases of squares of finite fields -/

namespace MathlibExtTest.Combinatorics.GDifferenceBasesTendstoGroupDiffBasisNumberGaloisFieldProd

open MetaMathlibExt Filter Topology

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

open Classical in
-- The normalized difference basis numbers converge for the smallest odd prime.
example : Tendsto (fun t : ℕ =>
    (groupDiffBasisNumber 1 (GaloisField 3 t × GaloisField 3 t) : ℝ) / (3 : ℝ) ^ t)
    atTop (𝓝 1) :=
  tendsto_groupDiffBasisNumber_galoisField_prod 3 (by norm_num)

open Classical in
-- Hence the ratio minus one tends to zero.
example : Tendsto (fun t : ℕ =>
    (groupDiffBasisNumber 1 (GaloisField 3 t × GaloisField 3 t) : ℝ) / (3 : ℝ) ^ t - 1)
    atTop (𝓝 0) := by
  have h := tendsto_groupDiffBasisNumber_galoisField_prod 3 (by norm_num)
  have h2 := h.sub_const 1
  simpa using h2

end MathlibExtTest.Combinatorics.GDifferenceBasesTendstoGroupDiffBasisNumberGaloisFieldProd
