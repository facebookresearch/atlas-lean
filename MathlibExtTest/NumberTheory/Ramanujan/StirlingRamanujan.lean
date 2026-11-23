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

public import MathlibExt.NumberTheory.Ramanujan.StirlingRamanujan

@[expose] public section

namespace MathlibExtTest.NumberTheory.Ramanujan.StirlingRamanujan

open MetaMathlibExt

-- Analysis 398: Ramanujan Sum in the Stirling-Ramanujan Setting

theorem IsRamanujanSum.congr
    {a b : ℕ → ℝ}
    {S : ℝ}
    (hab : a = b)
    (h : IsRamanujanSum a S) :
    IsRamanujanSum b S := by
  subst b
  exact h

-- Analysis 399: Stirling-Ramanujan Constant

theorem IsStirlingRamanujanConstant_one_iff
    (S : ℝ) :
    IsStirlingRamanujanConstant 1 S ↔
      IsRamanujanSum
        (fun k : ℕ =>
          (k : ℝ) * Real.log (k : ℝ))
        S := by
  simp [IsStirlingRamanujanConstant]

theorem IsStirlingRamanujanConstant_neg_one_iff
    (S : ℝ) :
    IsStirlingRamanujanConstant (-1) S ↔
      IsRamanujanSum
        (fun k : ℕ => ((k : ℝ)⁻¹))
        S := by
  simp [IsStirlingRamanujanConstant]

end MathlibExtTest.NumberTheory.Ramanujan.StirlingRamanujan

end
