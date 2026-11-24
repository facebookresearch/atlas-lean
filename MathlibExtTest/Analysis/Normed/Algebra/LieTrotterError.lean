/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Algebra.LieTrotterError

@[expose] public section

namespace MathlibExtTest.Analysis.Normed.Algebra.LieTrotterError

open scoped Matrix.Norms.L2Operator
open MathlibExt.Analysis.Normed.Algebra.LieTrotterError

/-- For the zero matrix pair, one step is the identity. -/
theorem trotterStep_zero (t : ℝ) :
    trotterStep (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 t = 1 := by
  unfold trotterStep
  simp only [smul_zero, NormedSpace.exp_zero, mul_one]

/-- Commuting diagonal Hermitian matrices have an exact one step. -/
theorem trotterStep_diagonal (a b : Fin 2 → ℝ) (t : ℝ) :
    trotterStep (Matrix.diagonal fun i => (a i : ℂ))
        (Matrix.diagonal fun i => (b i : ℂ)) t =
      NormedSpace.exp
        (-(Complex.I * (t : ℂ)) • Matrix.diagonal fun i => ((a i + b i : ℝ) : ℂ)) := by
  have hcomm : Commute (Matrix.diagonal fun i => (a i : ℂ))
      (Matrix.diagonal fun i => (b i : ℂ)) := by
    show _ * _ = _ * _
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    simp [Pi.mul_apply, mul_comm]
  rw [trotterStep_of_commute hcomm]
  congr 1
  congr 1
  first | rw [Matrix.diagonal_add] | rw [← Matrix.diagonal_add]
  congr 1
  ext i
  simp [Pi.add_apply, Complex.ofReal_add]

#print axioms trotterStep_of_commute
#print axioms norm_trotterStep_sub_exp_le
#print axioms norm_trotterStep_pow_sub_exp_le
#print axioms norm_trotterStep_pow_sub_exp_le_of_steps

end MathlibExtTest.Analysis.Normed.Algebra.LieTrotterError
