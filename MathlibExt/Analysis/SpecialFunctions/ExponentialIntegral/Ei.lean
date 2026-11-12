/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Analysis 385

/-!
# Real Exponential Integral

## References

* This is the standard power-series representation of the real exponential integral away from the
  origin. For the present conjecture only the positive value, $$ x=\log 3>0, $$ is required. See
  also: C. Lopez Zapata, Polylogarithmic Decomposition of a Borwein--Bailey--Girgensohn Series and
  its Connection to Ei(log 3), arXiv:2603.14548. (for `realExponentialIntegral`)

## References

* This is the standard power-series representation of the real exponential integral away from the
  origin. For the present conjecture only the positive value, $$ x=\log 3>0, $$ is required. See
  also: C. Lopez Zapata, Polylogarithmic Decomposition of a Borwein--Bailey--Girgensohn Series and
  its Connection to Ei(log 3), arXiv:2603.14548. (for `realExponentialIntegral`)

## References

* This is the standard power-series representation of the real exponential integral away from the
  origin. For the present conjecture only the positive value, $$ x=\log 3>0, $$ is required. See
  also: C. Lopez Zapata, Polylogarithmic Decomposition of a Borwein--Bailey--Girgensohn Series and
  its Connection to Ei(log 3), arXiv:2603.14548. (for `realExponentialIntegral`)

## References

* This is the standard power-series representation of the real exponential integral away from the
  origin. For the present conjecture only the positive value, $$ x=\log 3>0, $$ is required. See
  also: C. Lopez Zapata, Polylogarithmic Decomposition of a Borwein--Bailey--Girgensohn Series and
  its Connection to Ei(log 3), arXiv:2603.14548. (for `realExponentialIntegral`)

## References

* This is the standard power-series representation of the real exponential integral away from the
  origin. For the present conjecture only the positive value, $$ x=\log 3>0, $$ is required. See
  also: C. Lopez Zapata, Polylogarithmic Decomposition of a Borwein--Bailey--Girgensohn Series and
  its Connection to Ei(log 3), arXiv:2603.14548. (for `realExponentialIntegral`)

## References

* This is the standard power-series representation of the real exponential integral away from the
  origin. For the present conjecture only the positive value, $$ x=\log 3>0, $$ is required. See
  also: C. Lopez Zapata, Polylogarithmic Decomposition of a Borwein--Bailey--Girgensohn Series and
  its Connection to Ei(log 3), arXiv:2603.14548. (for `realExponentialIntegral`)

## References

* This is the standard power-series representation of the real exponential integral away from the
  origin. For the present conjecture only the positive value, $$ x=\log 3>0, $$ is required. See
  also: C. Lopez Zapata, Polylogarithmic Decomposition of a Borwein--Bailey--Girgensohn Series and
  its Connection to Ei(log 3), arXiv:2603.14548. (for `realExponentialIntegral`)
-/

namespace MetaMathlibExt

-- Analysis 385: Real Exponential Integral

/-- For real x≠0, define the real exponential integral by

Ei(x)=γ+log|x|+∑ₙ₌₁^∞xⁿ/(n⋅ n!),

where γ is the Euler-Mascheroni constant.

For x>0, this becomes

Ei(x)=γ+log x+∑ₙ₌₁^∞xⁿ/(n⋅ n!).
-/
noncomputable def realExponentialIntegral
    (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant +
    Real.log x +
    ∑' k : ℕ,
      x ^ (k + 1) /
        (((k : ℝ) + 1) *
          (Nat.factorial (k + 1) : ℝ))

end MetaMathlibExt

end
