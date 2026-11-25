/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.GreenKernel

open GreenKernel Set

example {u v C : ℝ → ℝ} {x y : ℝ} (h : x ≤ y) :
    kernel u v C x y = C y * u x :=
  kernel_of_le h

example {u v C : ℝ → ℝ} {x y : ℝ} (h : y < x) :
    kernel u v C x y = C y * (u y / v y) * v x :=
  kernel_of_lt h

example {u v C : ℝ → ℝ} {y : ℝ} :
    kernel u v C y y = C y * u y :=
  kernel_self

example {u v C : ℝ → ℝ} {y : ℝ} (hv : v y ≠ 0) :
    kernel u v C y y = C y * (u y / v y) * v y :=
  kernel_self_eq_right hv

example {u v C : ℝ → ℝ} {x y : ℝ} (hC : 0 < C y) (hux : 0 < u x)
    (huy : 0 < u y) (hvy : 0 < v y) (hvx : 0 < v x) :
    0 < kernel u v C x y :=
  kernel_pos hC hux huy hvy hvx

example {u v C : ℝ → ℝ} {y u' : ℝ} (hu : HasDerivAt u u' y) :
    HasDerivWithinAt (fun x => kernel u v C x y) (C y * u') (Iic y) y :=
  hasDerivWithinAt_kernel_Iic hu

example {u v C : ℝ → ℝ} {y v' : ℝ} (hv : HasDerivAt v v' y) (hvy : v y ≠ 0) :
    HasDerivWithinAt (fun x => kernel u v C x y)
      (C y * (u y / v y) * v') (Ici y) y :=
  hasDerivWithinAt_kernel_Ici hv hvy

example {u v C : ℝ → ℝ} {y : ℝ} (hu : ContinuousAt u y) (hv : ContinuousAt v y)
    (hvy : v y ≠ 0) :
    ContinuousAt (fun x => kernel u v C x y) y :=
  continuousAt_kernel_diagonal hu hv hvy

example {u v C : ℝ → ℝ} {y : ℝ} (hu : DifferentiableAt ℝ u y)
    (hv : DifferentiableAt ℝ v y) (hvy : v y ≠ 0) :
    derivWithin (fun x => kernel u v C x y) (Ici y) y -
        derivWithin (fun x => kernel u v C x y) (Iic y) y =
      C y * (u y / v y * deriv v y - deriv u y) :=
  derivWithin_kernel_jump hu hv hvy

-- Dirichlet Laplacian kernel on `[0, 1]`: `u x = x`, `v x = 1 - x`, `C y = 1 - y`.
example :
    kernel (fun x : ℝ => x) (fun x : ℝ => 1 - x) (fun y : ℝ => 1 - y)
      (1 / 4) (1 / 2) = 1 / 8 := by
  rw [kernel_of_le (by norm_num)]
  norm_num

example :
    kernel (fun x : ℝ => x) (fun x : ℝ => 1 - x) (fun y : ℝ => 1 - y)
      (3 / 4) (1 / 2) = 1 / 8 := by
  rw [kernel_of_lt (by norm_num)]
  norm_num

example :
    ContinuousAt
      (fun x => kernel (fun x : ℝ => x) (fun x : ℝ => 1 - x)
        (fun y : ℝ => 1 - y) x (1 / 2)) (1 / 2) :=
  continuousAt_kernel_diagonal continuousAt_id (by fun_prop) (by norm_num)

#print axioms GreenKernel.derivWithin_kernel_jump_wronskian
#print axioms GreenKernel.continuousAt_kernel_diagonal
