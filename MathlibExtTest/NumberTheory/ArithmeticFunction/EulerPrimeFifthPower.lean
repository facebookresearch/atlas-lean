/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.EulerPrimeFifthPower

open MetaMathlibExt

-- Five is the first admissible exponent after one.
example {n q m : ℕ} (h : EulerianForm n q 5 m) : q ^ 5 < 2 * m ^ 2 :=
  (eulerianForm_exponent_eq_one_or_pow_five_lt n q 5 m h).resolve_left (by decide)

-- The weak reverse inequality forces exponent one, including at the threshold.
example {n q e m : ℕ} (h : EulerianForm n q e m) (hle : 2 * m ^ 2 ≤ q ^ 5) : e = 1 :=
  (eulerianForm_exponent_eq_one_or_pow_five_lt n q e m h).resolve_right hle.not_gt
