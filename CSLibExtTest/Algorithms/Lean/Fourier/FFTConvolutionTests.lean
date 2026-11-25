/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.ConvolutionCost
public import Mathlib.Algebra.Field.ZMod
public meta import CSLibExt.Algorithms.Lean.Fourier.FFT.Convolution
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.Algebra.Star.Basic

@[expose] public section

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.TimeM

local instance convolutionFFTTestStarRing : StarRing (ZMod 17) := starRingOfComm
local instance convolutionFFTTestPrime : Fact (Nat.Prime 17) := ⟨by decide⟩

private def checkConvolution (actual : TimeM Nat (Option (Array (ZMod 17))))
    (expected : Option (Array (ZMod 17))) (cost : Nat) : IO String := do
  if actual.ret != expected || actual.time != cost then
    throw (IO.userError "wrong convolution output or execution charge")
  pure (reprStr (actual.ret, actual.time))

-- The nontrivial two-point principal root -1 is fixed by the canonical involution.
#eval checkConvolution (fftCircularArray (16 : ZMod 17) #[1, 2] #[3, 4])
  (some #[11, 10]) 72

#eval checkConvolution (fftCircularArray (1 : ZMod 17) #[1] #[2]) (some #[2]) 14

-- Padding one entry to two exercises the actual nontrivial transform and final zero.
#eval checkConvolution (fftLinearArray (16 : ZMod 17) #[1] #[2]) (some #[2, 0]) 78

#eval checkConvolution (fftCircularArray (1 : ZMod 17) #[1, 2] #[3]) none 0

#eval checkConvolution (fftLinearArray (1 : ZMod 17) #[1] #[2, 3]) none 0

#eval checkConvolution (fftCircularArray (1 : ZMod 17) #[] #[]) none 0

#eval checkConvolution (fftLinearArray (1 : ZMod 17) #[1, 2, 3] #[4, 5, 6]) none 0

example (d : Nat) (omega : ZMod 17) (xs ys : Vector (ZMod 17) (2 ^ d)) :
    (fftCircular d omega xs ys).time ≤ (21 * d + 16) * 2 ^ d :=
  fftCircular_time_le d omega xs ys

example (d : Nat) (omega : ZMod 17) (xs ys : Vector (ZMod 17) (2 ^ d)) :
    (fftLinear d omega xs ys).time ≤ (42 * d + 80) * 2 ^ d :=
  fftLinear_time_le d omega xs ys
