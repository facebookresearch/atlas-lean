/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectNotIsDeficientFPerfectOfPrime
namespace MathlibExtTest.NumberTheory.FkPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

example : ¬ IsDeficientFPerfect 2 :=
  not_isDeficientFPerfect_of_prime 2 Nat.prime_two

example : ¬ IsDeficientFPerfect 3 :=
  not_isDeficientFPerfect_of_prime 3 (by decide)

end MathlibExtTest.NumberTheory.FkPerfect
