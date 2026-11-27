/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Real zeros bounded by coefficient parity changes (AMR-021-0014)

For a polynomial with positive coefficients, the number of (distinct) real
zeros does not exceed the number of parity changes in the positive-`c̃`
index sequence.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import MathlibExt.Algebra.RealZerosParityChangeBound
