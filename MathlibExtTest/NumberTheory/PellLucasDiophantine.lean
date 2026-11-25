/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellLucasDiophantine

open MathlibExt.NumberTheory.PellLucasDiophantineWanted
open MetaMathlibExt

example (n : ℕ) : Nat.gcd (pellLucasSequence n) (pellLucasSequence (n + 1)) = 1 :=
  gcd_pellLucasSequence_succ (n := n)

example : Nat.gcd (pellLucasSequence 0) (pellLucasSequence 1) = 1 :=
  gcd_pellLucasSequence_succ (n := 0)

-- The terms at indices 4 and 5 are 17 and 41.
example : Nat.gcd 17 41 = 1 :=
  gcd_pellLucasSequence_succ (n := 4)

#print axioms MathlibExt.NumberTheory.PellLucasDiophantineWanted.gcd_pellLucasSequence_succ
