/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.BonamiTensorize

/-!
# Tests for `MathlibExt.Probability.Hypercontractivity.BonamiTensorize`

* `bnt_uexp`, `bnt_noiseKernel` and `bnt_noiseOp` computed on `Fin 1 → Bool`: the uniform
  expectation of a constant, the kernel at `ρ = 1` (the identity) and `ρ = 0` (uniform);
* `bnt_hypercontractivity` (tensorization) instantiated with its only hypothesis
  `bnt_VectorTwoPoint 0` discharged by `bnt_vectorTwoPoint_zero`, at `n = 2`;
* `bnt_tensorStep_of_vec` used to build `bnt_TensorStep 0`, fed to
  `bnt_hypercontractivity_of_twoPoint`.

The vector two-point inequality for all `0 ≤ ρ ≤ 1` is tested in
`MathlibExtTest.StatMech.Probability.Hypercontractivity.VectorTwoPoint`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.Hypercontractivity.BonamiTensorize

open _root_.StatMech.Probability

-- The uniform expectation of a constant is that constant.
example : bnt_uexp (fun _ : Fin 1 → Bool => (3 : ℝ)) = 3 := by
  simp [bnt_uexp]

-- At `ρ = 1` the noise kernel is the identity kernel.
example (x : Fin 1 → Bool) : bnt_noiseKernel 1 x x = 1 := by
  norm_num [bnt_noiseKernel]

-- At `ρ = 1` the kernel vanishes off the diagonal.
example : bnt_noiseKernel 1 (fun _ : Fin 1 => true) (fun _ => false) = 0 := by
  norm_num [bnt_noiseKernel]

-- At `ρ = 0` the kernel is uniform, `1/2` per coordinate.
example (x y : Fin 2 → Bool) : bnt_noiseKernel 0 x y = 1 / 4 := by
  simp only [bnt_noiseKernel, Fin.prod_univ_two]
  split_ifs <;> norm_num

-- `T_ρ` of a constant is that constant (here `ρ = 0`, `n = 1`).
example (x : Fin 1 → Bool) : bnt_noiseOp 0 (fun _ => (5 : ℝ)) x = 5 := by
  simp only [bnt_noiseOp, bnt_noiseKernel, Fin.prod_univ_one]
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp only [Fintype.sum_bool]
  split_ifs <;> norm_num

-- `bnt_hypercontractivity` with `bnt_VectorTwoPoint 0` discharged.
example (f : (Fin 2 → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp 0 f) ≤ bnt_qnorm (1 + 0 ^ 2) f :=
  bnt_hypercontractivity bnt_vectorTwoPoint_zero 2 f

-- `bnt_TensorStep 0` from `bnt_tensorStep_of_vec`, then `bnt_hypercontractivity_of_twoPoint`.
example (f : (Fin 3 → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp 0 f) ≤ bnt_qnorm (1 + 0 ^ 2) f :=
  bnt_hypercontractivity_of_twoPoint
    (fun n ih => bnt_tensorStep_of_vec bnt_vectorTwoPoint_zero n ih) 3 f

end MathlibExtTest.StatMech.Probability.Hypercontractivity.BonamiTensorize
