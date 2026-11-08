/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Array
public import CSLibExt.Algorithms.Lean.Fourier.FFT.ArrayCorrectness
public import Mathlib.Data.ZMod.Basic
public meta import CSLibExt.Algorithms.Lean.Fourier.FFT.Array
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Data.ZMod.Basic

@[expose] public section

open Cslib.Algorithms.Lean.TimeM

example {R : Type 1} [CommRing R] (d : Nat) (omega : R)
    (xs : Vector R (2 ^ d)) :
    (fftArray omega xs.toArray).ret = some (fft d omega xs).ret.toArray :=
  fftArray_ret_of_vector d omega xs

example (d : Nat) (omega : ℂ) (hroot : IsPrimitiveRoot omega (2 ^ d))
    (xs : Vector ℂ (2 ^ d)) (k : Fin (2 ^ d)) :
    ∃ ys : Array ℂ, (fftArray omega xs.toArray).ret = some ys ∧
      ys.size = 2 ^ d ∧
      ys.getD k.val 0 =
        MathlibExt.Analysis.Fourier.FastFourierTransformWanted.dftSum
          (2 ^ d) omega (fun j => xs.toArray.getD j 0) k.val :=
  fftArray_correct d omega hroot xs k

#eval do
  let actual := fftArray (4 : ZMod 17) #[0, 1, 2, 3]
  if actual.ret != some #[6, 7, 15, 6] || actual.time != 59 then
    throw (IO.userError "wrong admitted four-point FFT result or cost")
  IO.println (reprStr (actual.ret, actual.time))

#eval do
  let actual := fftArray (16 : ZMod 17) #[1, 2]
  if actual.ret != some #[3, 16] || actual.time != 15 then
    throw (IO.userError "wrong admitted two-point FFT result or cost")
  IO.println (reprStr (actual.ret, actual.time))

#eval do
  let actual := fftArray (4 : ZMod 17) #[9]
  if actual.ret != some #[9] || actual.time != 0 then
    throw (IO.userError "wrong singleton FFT admission")
  IO.println (reprStr (actual.ret, actual.time))

#eval do
  let actual := fftArray (4 : ZMod 17) #[0, 1, 2]
  if actual.ret != none || actual.time != 0 then
    throw (IO.userError "nonpower length was admitted or charged")
  IO.println (reprStr (actual.ret, actual.time))

#eval do
  let actual := fftArray (4 : ZMod 17) #[]
  if actual.ret != none || actual.time != 0 then
    throw (IO.userError "empty FFT input was admitted or charged")
  IO.println (reprStr (actual.ret, actual.time))
