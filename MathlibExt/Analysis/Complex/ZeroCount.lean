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

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Analysis 381

open scoped ENNReal Classical

/-!
# Analytic Zero Count with Multiplicity

## References

* This is the standard multiplicity-weighted zero-counting construction for analytic functions.
  Mathlib already provides the local multiplicity through `analyticOrderNatAt'. The present
  definition packages these local multiplicities into a global zero count over a specified set.
  (for `analyticZeroCount`)

## References

* This is the standard multiplicity-weighted zero-counting construction for analytic functions.
  Mathlib already provides the local multiplicity through `analyticOrderNatAt'. The present
  definition packages these local multiplicities into a global zero count over a specified set.
  (for `analyticZeroCount`)

## References

* This is the standard multiplicity-weighted zero-counting construction for analytic functions.
  Mathlib already provides the local multiplicity through `analyticOrderNatAt'. The present
  definition packages these local multiplicities into a global zero count over a specified set.
  (for `analyticZeroCount`)

## References

* This is the standard multiplicity-weighted zero-counting construction for analytic functions.
  Mathlib already provides the local multiplicity through `analyticOrderNatAt'. The present
  definition packages these local multiplicities into a global zero count over a specified set.
  (for `analyticZeroCount`)

## References

* This is the standard multiplicity-weighted zero-counting construction for analytic functions.
  Mathlib already provides the local multiplicity through `analyticOrderNatAt'. The present
  definition packages these local multiplicities into a global zero count over a specified set.
  (for `analyticZeroCount`)

## References

* This is the standard multiplicity-weighted zero-counting construction for analytic functions.
  Mathlib already provides the local multiplicity through `analyticOrderNatAt'. The present
  definition packages these local multiplicities into a global zero count over a specified set.
  (for `analyticZeroCount`)

## References

* This is the standard multiplicity-weighted zero-counting construction for analytic functions.
  Mathlib already provides the local multiplicity through `analyticOrderNatAt'. The present
  definition packages these local multiplicities into a global zero count over a specified set.
  (for `analyticZeroCount`)
-/

namespace MetaMathlibExt

-- Analysis 381: Analytic Zero Count with Multiplicity

/-- Let

f:ℂ→ℂ

and let S⊂ℂ.

The analytic zero count of f in S is the sum of the multiplicities of
all zeros of f lying in S:
$$
N(f,S)=\sum_{\substack{z\in S\\f(z)=0}}\operatorname{ord}_z(f).
$$

The value lies in the extended nonnegative reals, so the construction can also represent an infinite
total zero count.
-/
noncomputable def analyticZeroCount
    (f : ℂ → ℂ)
    (S : Set ℂ) : ℝ≥0∞ :=
  ∑' z : ℂ,
    if z ∈ S ∧ f z = 0 then
      (analyticOrderNatAt f z : ℝ≥0∞)
    else
      0

end MetaMathlibExt

end
