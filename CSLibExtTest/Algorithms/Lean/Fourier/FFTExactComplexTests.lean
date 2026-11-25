/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Array
public import CSLibExt.Algorithms.Lean.Fourier.FFT.ConvolutionCost
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public meta import CSLibExt.Algorithms.Lean.Fourier.FFT.Array
public meta import CSLibExt.Algorithms.Lean.Fourier.FFT.Convolution
public meta import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

@[expose] public section

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.TimeM

-- Canonical rational quadratic arithmetic supplies a computable field and conjugation.
private abbrev ExactComplex := QuadraticAlgebra ℚ (-1) 0

local instance : Fact (∀ r : ℚ, r ^ 2 ≠ (-1 : ℚ) + 0 * r) := ⟨by
  intro r h
  have hr := sq_nonneg r
  norm_num at h
  nlinarith⟩

private def qc (re im : ℚ) : ExactComplex := ⟨re, im⟩

private def omega : ExactComplex := QuadraticAlgebra.omega

-- Each actual sample root is primitive of order four, not merely a fourth root.
private theorem omega_primitive : IsPrimitiveRoot omega 4 := by
  refine IsPrimitiveRoot.mk_of_lt omega (by decide) ?_ ?_
  · apply QuadraticAlgebra.ext <;>
      norm_num [omega, QuadraticAlgebra.omega, pow_succ,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · intro l hl hlt
    interval_cases l <;>
      norm_num [omega, QuadraticAlgebra.omega, pow_succ, QuadraticAlgebra.ext_iff,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem neg_omega_primitive : IsPrimitiveRoot (-omega) 4 := by
  refine IsPrimitiveRoot.mk_of_lt (-omega) (by decide) ?_ ?_
  · apply QuadraticAlgebra.ext <;>
      norm_num [omega, QuadraticAlgebra.omega, pow_succ,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · intro l hl hlt
    interval_cases l <;>
      norm_num [omega, QuadraticAlgebra.omega, pow_succ, QuadraticAlgebra.ext_iff,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

#print axioms omega_primitive
#print axioms neg_omega_primitive

-- Compose the two actual TimeM calls, retaining both execution charges.
private def roundtripExact (root : ExactComplex) (xs : Array ExactComplex) :
    TimeM Nat (Option (Array ExactComplex)) := do
  let transformed ← fftArray root xs
  match transformed with
  | none => pure none
  | some values =>
    if h : values.size = 2 ^ values.size.log2 then do
      let restored ← ifft values.size.log2 root ⟨values, h⟩
      pure (some restored.toArray)
    else pure none

private def checkExact (label : String)
    (actual : TimeM Nat (Option (Array ExactComplex)))
    (expected : Array (ℚ × ℚ)) (cost : Nat) : IO String := do
  match actual.ret with
  | none => throw (IO.userError "exact-complex executor rejected a valid input")
  | some values =>
    let coordinates := values.map (fun z => (z.re, z.im))
    if coordinates != expected || actual.time != cost then
      throw (IO.userError "wrong exact-complex coefficients or execution charge")
    pure (reprStr (label, coordinates, actual.time))

#eval checkExact "fft positive"
  (fftArray omega #[qc 0 0, qc 1 0, qc 2 0, qc 3 0])
  #[(6, 0), (-2, -2), (-2, 0), (-2, 2)] 59

#eval checkExact "roundtrip positive"
  (roundtripExact omega #[qc 0 0, qc 1 0, qc 2 0, qc 3 0])
  #[(0, 0), (1, 0), (2, 0), (3, 0)] 155

#eval checkExact "circular positive"
  (fftCircularArray omega #[qc 1 0, qc 2 0, qc 3 0, qc 4 0]
    #[qc 5 0, qc 6 0, qc 7 0, qc 8 0])
  #[(66, 0), (68, 0), (66, 0), (60, 0)] 230

#eval checkExact "linear real positive"
  (fftLinearArray omega #[qc 1 0, qc 2 0] #[qc 3 0, qc 4 0])
  #[(3, 0), (10, 0), (8, 0), (0, 0)] 242

-- Both input coefficients and conjugation carry nonzero imaginary parts.
#eval checkExact "linear complex positive"
  (fftLinearArray omega #[qc 1 1, qc 2 (-1)] #[qc 3 (-2), qc (-1) 4])
  #[(5, 1), (-1, -4), (2, 9), (0, 0)] 242

#eval checkExact "fft negative"
  (fftArray (-omega) #[qc 0 0, qc 1 0, qc 2 0, qc 3 0])
  #[(6, 0), (-2, 2), (-2, 0), (-2, -2)] 59

#eval checkExact "roundtrip negative"
  (roundtripExact (-omega) #[qc 0 0, qc 1 0, qc 2 0, qc 3 0])
  #[(0, 0), (1, 0), (2, 0), (3, 0)] 155

#eval checkExact "circular negative"
  (fftCircularArray (-omega) #[qc 1 0, qc 2 0, qc 3 0, qc 4 0]
    #[qc 5 0, qc 6 0, qc 7 0, qc 8 0])
  #[(66, 0), (68, 0), (66, 0), (60, 0)] 230

#eval checkExact "linear real negative"
  (fftLinearArray (-omega) #[qc 1 0, qc 2 0] #[qc 3 0, qc 4 0])
  #[(3, 0), (10, 0), (8, 0), (0, 0)] 242

#eval checkExact "linear complex negative"
  (fftLinearArray (-omega) #[qc 1 1, qc 2 (-1)] #[qc 3 (-2), qc (-1) 4])
  #[(5, 1), (-1, -4), (2, 9), (0, 0)] 242
