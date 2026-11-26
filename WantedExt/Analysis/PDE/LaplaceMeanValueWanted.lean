/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.PDE.LaplaceHarnack
public import MathlibExt.Analysis.PDE.LaplaceMeanValue
public import MathlibExt.Analysis.PDE.LaplaceStrongMaximumPrinciple
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Harmonic mean-value property, Harnack's inequality and the strong maximum principle

This module re-exports the proved results formerly stated here.
-/
