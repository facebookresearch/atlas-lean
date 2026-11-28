/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Logistic incidence models under case-control sampling

Suppose disease incidence follows a logistic model, `P(D = 1 | X = x) = σ(α + β · φ(x))`,
and a case-control study samples cases with probability `π₁` and controls with probability
`π₀`, independently of the covariate `X` given disease status. Then among the sampled
individuals disease still follows a logistic model in `x` with the same coefficients `β`; only
the intercept changes, to `α + log (π₁ / π₀)`. This is the identity behind Prentice and Pyke's
result that prospective logistic regression applied to case-control data estimates the
odds-ratio parameters `β` consistently.

The covariate takes finitely many values here. Prentice and Pyke's further statements, that
the prospective maximum-likelihood estimate of `β` coincides with the semiparametric
retrospective one and has the same asymptotic covariance, are not stated in this module.

Here `σ t = 1 / (1 + exp (-t))` is the logistic function, Mathlib's `Real.sigmoid`.

Sources: R. L. Prentice and R. Pyke, "Logistic disease incidence models and case-control
studies", Biometrika 66 (1979) 403–411.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Domains.Biology.StatisticalGenetics.AssociationTests.PrenticePykeCaseControl
