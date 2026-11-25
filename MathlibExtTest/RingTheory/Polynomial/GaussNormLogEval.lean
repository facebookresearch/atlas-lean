/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Polynomial.GaussNormLogEval

@[expose] public section

open Polynomial

-- exactSource consumer: the original binders apply verbatim.
example {K : Type*} [Field K] [IsAlgClosed K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (p : K[X]) (hp : p ≠ 0)
    {z : K} (hz : v z ≤ 1) (hpz : p.eval z ≠ 0) :
    Real.log (v (p.eval z)) = Real.log (p.gaussNorm v 1)
      + ((p.roots.filter fun a => v a ≤ 1).map fun a => Real.log (v (z - a))).sum :=
  Polynomial.log_abv_eval_eq_log_gaussNorm_add_sum v hv p hp hz hpz

-- Boundary: a constant polynomial has no roots, so the root sum is empty and
-- the formula reduces to the value at the constant coefficient.
example {K : Type*} [Field K] [IsAlgClosed K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (c : K) (hc : c ≠ 0) (z : K)
    (hz : v z ≤ 1) :
    Real.log (v c) = Real.log ((C c).gaussNorm v 1) := by
  have h := Polynomial.log_abv_eval_eq_log_gaussNorm_add_sum v hv (C c) (C_ne_zero.mpr hc)
    hz (by simpa using hc)
  simpa using h
