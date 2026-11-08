/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.ZModConvolution
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExt.Analysis.Fourier.ZModConvolutionTests

theorem wrap_coefficient :
    ZMod.dft.symm (fun k =>
      ZMod.dft (fun j : ZMod 4 => if j = 3 then (2 : ℂ) else 0) k *
      ZMod.dft (fun j : ZMod 4 => if j = 2 then (3 : ℂ) else 0) k) (1 : ZMod 4) = 6 := by
  classical
  rw [ZMod.invDFT_mul_dft, Finset.sum_eq_single (3 : ZMod 4)]
  · have hw : (1 : ZMod 4) - 3 = 2 := by decide
    rw [hw]
    norm_num
  · intro b _ hb
    simp [hb]
  · simp

end MathlibExt.Analysis.Fourier.ZModConvolutionTests
