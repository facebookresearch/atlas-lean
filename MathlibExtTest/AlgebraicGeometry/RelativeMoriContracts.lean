/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.RelativeMoriContracts

noncomputable section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.RelativeMoriContracts
open MathlibExt.AlgebraicGeometry.NumericalCurveCones
open MathlibExt.AlgebraicGeometry.MoriContractionModels
open scoped BigOperators

universe u
variable {k : Type u} [Field k] {n : ℕ}
variable {S : Over (Spec (.of k))}

/-- Relative degree evaluation retains the actual underlying curve degrees. -/
example (V : NormalVariety k n) (q : V.X ⟶ S) (D : CartierCombination V)
    (C : Curve V.X) (h : IsContracted q C) :
    combinationOnClass q D (relativeClass q C h) = combinationOnCurve D C := rfl

/-- Anti-adjoint input really negates the actual curve-degree functional. -/
example (V : NormalVariety k n) (D : CartierCombination V) (C : Curve V.X) :
    combinationOnCurve (negativeCombination D) C = -combinationOnCurve D C := by
  simp only [combinationOnCurve, negativeCombination, neg_mul, Finset.sum_neg_distrib, neg_inj]
  rfl

/-- A zero numerical vector is never accepted as an extremal ray. -/
example (V : NormalVariety k n) (q : V.X ⟶ S) : ¬IsExtremal (0 : RelativeN1 q) := by
  intro h
  exact h.1 rfl
