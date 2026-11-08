/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.WirsingConstant

@[expose] public section

namespace MathlibExtTest.WirsingConstant

open MathlibExt.Analysis.WirsingConstant

/-- The Gauss density is an eigenfunction at the dominant eigenvalue. -/
example : IsEigenvalue 1 := isEigenvalue_one

/-- The defining series converges for the constant function at every
point of `[0, 1]`. -/
example {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Summable (gkwTerm (fun _ => 1) x) :=
  summable_gkwTerm (M := 1) hx (by intro y _; norm_num)

end MathlibExtTest.WirsingConstant
