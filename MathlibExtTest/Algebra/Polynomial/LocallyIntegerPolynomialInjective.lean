/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Interval.Set.Infinite
import MathlibExt.Algebra.Polynomial.LocallyIntegerPolynomialInjective

/-! # Tests for injectivity of polynomial evaluation into LIP -/

open MetaMathlibExt Polynomial

-- Recover an integer polynomial from its image on all of ℤ.
example (p : ℤ[X]) (h : polynomialToLIP Set.univ p = polynomialToLIP Set.univ (X ^ 2 + C 1)) :
    p = X ^ 2 + C 1 :=
  polynomialToLIP_injective Set.infinite_univ h

-- Evaluation on the nonnegative integers is also injective.
example : Function.Injective (polynomialToLIP (Set.Ici (0 : ℤ))) :=
  polynomialToLIP_injective (Set.Ici_infinite 0)
