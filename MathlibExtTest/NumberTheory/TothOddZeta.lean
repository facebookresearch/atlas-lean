/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TothOddZeta

namespace MathlibExtTest.NumberTheory.TothOddZeta

open MetaMathlibExt MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry

private lemma euler_one : chapter5EulerEven 1 = -1 := by
  rw [chapter5EulerEven_step 1 (by decide)]
  simp [chapter5EulerEven_zero]

example : HurwitzZeta.hurwitzZeta ((3 / 4 : ℝ) : UnitAddCircle) 3 =
    28 * riemannZeta 3 - (Real.pi : ℂ) ^ 3 := by
  have h := hurwitzZeta_three_quarters_two_mul_add_one 1 (by decide)
  norm_num [euler_one, Nat.factorial] at h
  linear_combination h

example : HurwitzZeta.hurwitzZeta ((3 / 4 : ℝ) : UnitAddCircle) 5 =
    496 * riemannZeta 5 - 5 / 3 * (Real.pi : ℂ) ^ 5 := by
  have hE : chapter5EulerEven 2 = 5 := by
    rw [chapter5EulerEven_step 2 (by decide)]
    norm_num [Fin.sum_univ_two, chapter5EulerEven_zero, euler_one, Nat.choose]
  have h := hurwitzZeta_three_quarters_two_mul_add_one 2 (by decide)
  norm_num [hE, Nat.factorial] at h
  linear_combination h

end MathlibExtTest.NumberTheory.TothOddZeta
