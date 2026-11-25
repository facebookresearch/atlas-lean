/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellLucasCoprimality

open MathlibExt.NumberTheory.PellLucasDiophantineWanted

example : Nat.gcd 0 1 = 1 :=
  gcd_pellNumber_pellLucasSequence (n := 0)

-- At index 5 the Pell number is 29 and the Pell–Lucas number is 41.
example : Nat.gcd 29 41 = 1 :=
  gcd_pellNumber_pellLucasSequence (n := 5)
