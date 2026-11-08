/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT
public import Mathlib.Data.ZMod.Basic
public meta import CSLibExt.Algorithms.Lean.Fourier.FFT
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Data.ZMod.Basic

@[expose] public section

set_option autoImplicit false

open Cslib.Algorithms.Lean.TimeM

private def checkFFT : IO (Array (ZMod 17) × Nat) := do
  let input : Vector (ZMod 17) 4 := ⟨#[0, 1, 2, 3], rfl⟩
  let result := fft 2 4 input
  unless result.ret.toArray == #[6, 7, 15, 6] do
    throw (IO.userError "Wrong four-entry FFT output")
  unless result.time == 59 do
    throw (IO.userError "Wrong FFT operation charge")
  pure (result.ret.toArray, result.time)

#eval checkFFT
