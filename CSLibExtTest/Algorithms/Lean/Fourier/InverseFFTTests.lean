/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.InverseCost
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public meta import CSLibExt.Algorithms.Lean.Fourier.FFT.Inverse
public meta import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.Algebra.Star.Basic

@[expose] public section

open Cslib.Algorithms.Lean.TimeM

-- The canonical trivial involution fixes the valid two-point sample root -1.
local instance inverseFFTTestStarRing : StarRing (ZMod 17) := starRingOfComm
local instance inverseFFTTestPrime : Fact (Nat.Prime 17) := ⟨by decide⟩

#eval do
  let input : Vector (ZMod 17) 2 := ⟨#[3, 16], rfl⟩
  let actual := ifft 1 (16 : ZMod 17) input
  if actual.ret.toArray != #[1, 2] || actual.time != 34 then
    throw (IO.userError "wrong two-point source inverse FFT value or cost")
  IO.println (reprStr (actual.ret.toArray, actual.time))

#eval do
  let input : Vector (ZMod 17) 1 := ⟨#[9], rfl⟩
  let actual := ifft 0 (1 : ZMod 17) input
  if actual.ret.toArray != #[9] || actual.time != 10 then
    throw (IO.userError "wrong singleton source inverse FFT value or cost")
  IO.println (reprStr (actual.ret.toArray, actual.time))

example (d : Nat) (omega : ZMod 17) (xs : Vector (ZMod 17) (2 ^ d)) :
    (ifft d omega xs).time ≤ 8 * (2 ^ d) * d + 9 * (2 ^ d) + 1 :=
  ifft_time_le d omega xs
