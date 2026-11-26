/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.OddZetaDirichletBetaEulerDirichletBetaTwoMulAddOne
import Mathlib.Tactic.NormNum

/-!
# Tests for Dirichlet beta at odd positive integers

The general formula gives the values at one and three.
-/

namespace MathlibExtTest.NumberTheory.OddZetaDirichletBetaEulerDirichletBetaTwoMulAddOne

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry
open MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

example : chapter7DirichletBeta 1 = (Real.pi : ℂ) / 4 := by
  have h := MetaMathlibExt.dirichletBeta_two_mul_add_one 0
  norm_num [chapter5EulerEven_zero] at h
  exact h

example : chapter7DirichletBeta 3 = (Real.pi : ℂ) ^ 3 / 32 := by
  have he : chapter5EulerEven 1 = -1 := by
    rw [chapter5EulerEven_step 1 (by decide)]
    simp [chapter5EulerEven_zero]
  have h := MetaMathlibExt.dirichletBeta_two_mul_add_one 1
  norm_num [he] at h
  exact h

end MathlibExtTest.NumberTheory.OddZetaDirichletBetaEulerDirichletBetaTwoMulAddOne
