/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import MathlibExt.Analysis.Complex.ZeroCount

@[expose] public section

open scoped ENNReal Classical

namespace MathlibExtTest.Analysis.Complex.ZeroCount

open MetaMathlibExt

-- Analysis 381: Analytic Zero Count with Multiplicity

theorem analyticZeroCount_const_one
    (S : Set ℂ) :
    analyticZeroCount (fun _ : ℂ => 1) S = 0 := by
  classical
  simp [analyticZeroCount]

end MathlibExtTest.Analysis.Complex.ZeroCount

end
