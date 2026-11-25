/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.WignerMatrix

open MathlibExt.Analysis.WignerSemicircleWanted.Analysis.WignerSemicircleProblem

-- The two off-diagonal entries both read the upper entry of an asymmetric input.
example (ω : Unit) :
    let X := fun (i j : ℕ) (_ : Unit) => (10 * i + j : ℝ)
    let M := wignerMatrix X 2 ω
    M 0 1 = 1 ∧ M 1 0 = 1 ∧ M 1 1 = 11 := by
  norm_num [wignerMatrix]

example {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (wignerMatrix X n ω).conjTranspose = wignerMatrix X n ω :=
  wignerMatrix_isHermitian X n ω
