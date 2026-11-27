/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeConvolution

open BooleanCube
open scoped BigOperators

/-! ### Convolution on the Boolean cube -/

/-- A concrete product: `(+1, -1) · (-1, -1) = (-1, +1)`. -/
example : cubeMul (n := 2) ![true, false] ![false, false] = ![false, true] := by
  decide

/-- Characters are multiplicative. -/
example (x y : BoolCube 3) :
    cubeChi 3 {0, 2} (cubeMul x y) = cubeChi 3 {0, 2} x * cubeChi 3 {0, 2} y :=
  cubeChi_cubeMul _ x y

/-- The convolution of two different characters has no Fourier weight at either index. -/
example : boolFourierCoeff 2 (boolConv (cubeChi 2 {0}) (cubeChi 2 {1})) {0} = 0 := by
  rw [boolFourierCoeff_boolConv, boolFourierCoeff_cubeChi, boolFourierCoeff_cubeChi]
  simp

/-- A character convolved with itself keeps coefficient one at its index. -/
example (S : Finset (Fin 3)) :
    boolFourierCoeff 3 (boolConv (cubeChi 3 S) (cubeChi 3 S)) S = 1 := by
  simp [boolFourierCoeff_boolConv]

/-- Convolution is commutative. -/
example (f g : BoolCube 3 → ℝ) : boolConv f g = boolConv g f :=
  boolConv_comm f g
