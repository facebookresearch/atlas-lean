/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.DedekindZetaNeZero

public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace NumberFieldDedekindZetaNeZeroTest

/-- `exactSource` consumer with the original binders. -/
public theorem exactSource (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) :
    NumberField.dedekindZeta K s ≠ 0 :=
  NumberField.dedekindZeta_ne_zero_of_one_lt_re K hs

/-- Higher-universe consumer. -/
public theorem exactSourceTypeOne (K : Type 1) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s ≠ 0 :=
  NumberField.dedekindZeta_ne_zero_of_one_lt_re K hs

/-- Concrete field: the Dedekind zeta function of `ℚ` does not vanish at
`s = 2`. -/
public example : NumberField.dedekindZeta ℚ 2 ≠ 0 :=
  NumberField.dedekindZeta_ne_zero_of_one_lt_re ℚ (by norm_num)

/-- Boundary: the hypothesis `1 < s.re` cannot be dropped in general, as
the statement is about the Euler-product region; at a point with real
part at most `1` this consumer does not apply. This records that the
consumer above really uses the hypothesis by checking it at `s = 2`. -/
public example : (1 : ℝ) < (2 : ℂ).re := by norm_num

end NumberFieldDedekindZetaNeZeroTest
