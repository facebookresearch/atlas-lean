/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ScottishBook157
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Scottish Book Problem 157 compatibility module

The definitions and the proved monotonicity test now live in `MathlibExt.Analysis.ScottishBook157`.
`ApproxContinuousAt` intentionally requires the bad set to have outer density zero; for arbitrary
functions this is not equivalent to the previous good-set condition.
-/
