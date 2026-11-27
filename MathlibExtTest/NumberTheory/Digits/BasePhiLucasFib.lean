/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.BasePhiLucasFib

namespace MetaMathlibExt

-- The source includes the endpoint `n = 0`.
example : lucasNumber 2 = 3 :=
  (fib_add_three_mul_fib_succ_eq_lucasNumber 0).symm

-- Check an odd index beyond both induction bases.
example : lucasNumber 7 = 29 :=
  (fib_add_three_mul_fib_succ_eq_lucasNumber 5).symm

end MetaMathlibExt
