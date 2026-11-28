/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.Recurrences.LucasPowerParamsFinitePrimes
public import MathlibExt.NumberTheory.Recurrences.LucasQOneShiftComposite
public import MathlibExt.NumberTheory.Recurrences.LucasSquareQFinitePrimes
public import MathlibExt.NumberTheory.Recurrences.ShiftedLucasComposite
public import MathlibExt.NumberTheory.Recurrences.ShiftedLucasQNegOneComposite
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Basic

/-! # Shifting Lucas sequences away from primes

Composite values of Lucas sequences `U_n(P, Q)` and of their unit shifts. An integer `m` is
composite when `1 < m` and `m` is not prime.
-/
