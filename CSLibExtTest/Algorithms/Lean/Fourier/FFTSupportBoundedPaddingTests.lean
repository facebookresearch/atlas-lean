/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.SupportBoundedPadding

@[expose] public section

set_option autoImplicit false

open CSLibExt.Algorithms.Lean.Fourier.FFT.SupportBoundedPadding

/-- Unit-support linear convolution at index 0 is the product `2 * 3 = 6`. -/
example : linearConvolution 1 1 (fun _ => (2 : ℂ)) (fun _ => (3 : ℂ)) 0 = 6 := by
  norm_num [linearConvolution, extendNat]

/-- Unit-support linear convolution at index 1 vanishes. -/
example : linearConvolution 1 1 (fun _ => (2 : ℂ)) (fun _ => (3 : ℂ)) 1 = 0 := by
  norm_num [linearConvolution, extendNat, Finset.sum_range_succ]

/-- The same signals padded to length 3 have cyclic coefficient `6` at index 0. -/
example : cyclicConvolution 3 (zeroExtend 1 3 (fun _ => (2 : ℂ)))
    (zeroExtend 1 3 (fun _ => (3 : ℂ))) 0 = 6 := by
  norm_num [cyclicConvolution, zeroExtend, extendNat]
