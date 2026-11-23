/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DucciSequence

open MathlibExt.NumberTheory.DucciWanted

-- The endpoints of the first admissible row both have residue one.
example : (Nat.choose 6 0 : ZMod 3) = 1 :=
  (choose_prime_pow_sub_mod 3 2 0 (by decide) (by decide) (by decide) (by decide)).trans (by decide)

example : (Nat.choose 6 6 : ZMod 3) = 1 :=
  (choose_prime_pow_sub_mod 3 2 6 (by decide) (by decide) (by decide) (by decide)).trans (by decide)

-- With k = 3, divisibility by p alone does not give a nonzero residue.
example : (Nat.choose 18 3 : ZMod 3) = 0 :=
  (choose_prime_pow_sub_mod 3 3 3 (by decide) (by decide) (by decide) (by decide)).trans (by decide)

example : (Nat.choose 18 9 : ZMod 3) = -1 :=
  (choose_prime_pow_sub_mod 3 3 9 (by decide) (by decide) (by decide) (by decide)).trans (by decide)

-- Three different indices contribute to the same cyclic coefficient.
example : ducciCoeff 2 4 1 = 1 + 6 + 1 := by decide
