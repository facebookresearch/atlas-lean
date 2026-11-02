/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Single-set sum-difference exponent

The constant `C₃d` is the least real exponent that bounds the normalized
sumset cardinality by the corresponding normalized difference-set cardinality.
The frozen source states that its exact value is `2`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Combinatorics.SingleSetSumDifferenceExponentWanted

open scoped Pointwise

/-! Source record `C3d`, file SHA-256
`115fbd7c1cb17caa8e865a1dd2850589c09e102659247ffece53ad3824ec01cb`. -/

/-- **Admissible exponents for sums and differences.** A real number $\theta$ is an admissible
exponent when every nonempty finite set $A$ of integers satisfies
$|A+A|/|A| \le (|A-A|/|A|)^{\theta}$, where $A+A$ and $A-A$ are the sumset and the difference
set of $A$. -/
def IsAdmissibleExponent (θ : ℝ) : Prop :=
  ∀ A : Finset ℤ, A.Nonempty →
    ((A + A).card : ℝ) / (A.card : ℝ) ≤
      Real.rpow (((A - A).card : ℝ) / (A.card : ℝ)) θ

/-- **The single-set sum-difference exponent.** The single-set sum-difference exponent $C_{3d}$ is
the infimum of the admissible exponents, that is, of the set of real numbers $\theta$ such that
$|A+A|/|A| \le (|A-A|/|A|)^{\theta}$ for every nonempty finite set $A$ of integers, where $A+A$
and $A-A$ are the sumset and the difference set of $A$.

This is the source's equivalent formulation of $C_{3d}$ as a least admissible exponent, over
finite sets of integers. -/
noncomputable def singleSetSumDifferenceExponent : ℝ :=
  sInf {θ : ℝ | IsAdmissibleExponent θ}

/-- **The proposition that the single-set sum-difference exponent equals 2.** This is the
statement that the single-set sum-difference exponent $C_{3d}$ is equal to $2$. -/
def singleSetSumDifferenceExponent_eq_two : Prop :=
  singleSetSumDifferenceExponent = 2

/-- **The single-set sum-difference exponent equals 2.** The single-set sum-difference exponent
$C_{3d}$ is equal to $2$.

Known constructions approach this value but do not attain it.

Source: Haowei Lin and Shanda Li, Settling the optimal
exponent relating sumsets and difference sets, arXiv:2607.27199v1 (2026),
https://arxiv.org/abs/2607.27199v1. Moved from
`OpenConjectures/Combinatorics/SingleSetSumDifferenceExponent`.
-/
public theorem_wanted singleSetSumDifferenceExponent_eq_two_holds : singleSetSumDifferenceExponent_eq_two

end MathlibExt.Combinatorics.SingleSetSumDifferenceExponentWanted
