/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AffineAdicSpectra
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.GroupWithZero.WithZero
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-! Actual polynomial evaluation gives distinct all-rank valuation points.
The rational condition 1 <= X excludes the zero of its denominator.
These examples require no perfectoid or sheaf provider.
-/

open MathlibExt.AlgebraicGeometry.AffineAdicSpectra

noncomputable section

private def trivialValuation : Valuation ℚ (WithZero (Multiplicative ℤ)) := 1

private def point (a : ℚ) : Spectrum (Polynomial ℚ) :=
  ⟨comapRelation (Polynomial.evalRingHom a)
    (ValuativeRel.ofValuation trivialValuation)⟩

private lemma zeroExcluded :
    point 0 ∉ basicOpen (1 : Polynomial ℚ) Polynomial.X := by
  change ¬ (trivialValuation ((Polynomial.evalRingHom 0) 1) ≤
    trivialValuation ((Polynomial.evalRingHom 0) Polynomial.X) ∧
    ¬ trivialValuation ((Polynomial.evalRingHom 0) Polynomial.X) ≤
      trivialValuation ((Polynomial.evalRingHom 0) 0))
  simp

private lemma oneIncluded :
    point 1 ∈ basicOpen (1 : Polynomial ℚ) Polynomial.X := by
  change trivialValuation ((Polynomial.evalRingHom 1) 1) ≤
    trivialValuation ((Polynomial.evalRingHom 1) Polynomial.X) ∧
    ¬ trivialValuation ((Polynomial.evalRingHom 1) Polynomial.X) ≤
      trivialValuation ((Polynomial.evalRingHom 1) 0)
  simp

example : point 0 ≠ point 1 := by
  intro h
  exact zeroExcluded (h ▸ oneIncluded)

example : point 1 ∉ basicOpen (1 : Polynomial ℚ) 0 := by
  change ¬ (trivialValuation ((Polynomial.evalRingHom 1) 1) ≤
    trivialValuation ((Polynomial.evalRingHom 1) 0) ∧
    ¬ trivialValuation ((Polynomial.evalRingHom 1) 0) ≤
      trivialValuation ((Polynomial.evalRingHom 1) 0))
  simp

/-- Mod-p Frobenius alone does not impose the ramification condition. -/
example : Function.Surjective (fun x : ZMod 2 ↦ x ^ 2) := by decide

/-- The divisibility condition is inside the integral ring, not its field. -/
example : ¬ (2 : ℤ) ^ 2 ∣ (2 : ℤ) := by norm_num
