/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SophieGermainPrimeWilson

open MetaMathlibExt

-- At 11, the first residue certifies primality of 11 and 23.
example : Nat.IsSophieGermainPrime 11 :=
  ((isSophieGermainPrime_ne_two_iff_factorial_modEq (a := 11) (by decide)).mpr
    (Or.inl (by decide))).1

-- At 3, only the negative residue represents 2! modulo 21.
example : (Nat.factorial 2 : ℤ) ≡ -19 [ZMOD 21] := by
  have h := (isSophieGermainPrime_ne_two_iff_factorial_modEq (a := 3) (by decide)).mp
    ⟨⟨by decide, by decide⟩, by decide⟩
  exact h.resolve_left (by decide)

-- The excluded Sophie Germain prime 2 satisfies neither congruence.
example : ¬ ((1 : ℤ) ≡ 3 [ZMOD 10] ∨ (1 : ℤ) ≡ -13 [ZMOD 10]) := by
  intro h
  exact ((isSophieGermainPrime_ne_two_iff_factorial_modEq (a := 2) (by decide)).mpr h).2 rfl
