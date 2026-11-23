/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RealAlgebraicBundleStrata
import Mathlib.Tactic.Linarith

open MathlibExt.AlgebraicGeometry.RealAlgebraicBundleStrata
open MvPolynomial

namespace MathlibExtTest.AlgebraicGeometry.RealBundleFibres

noncomputable def identityProjection {n : ℕ} (X : RealVariety n) (r : ℕ) :
    ProjectionBundle X r where
  projection _ := 1
  continuous := continuous_const
  idempotent _ := by simp
  symmetric _ := by simp

example {n : ℕ} (X : RealVariety n) (r : ℕ) (x : X.locus) :
    (identityProjection X r).fiber x = ⊤ := by
  simp [ProjectionBundle.fiber, identityProjection]

example {n : ℕ} {S : Set (Ambient n)} (x : S) (i : Fin n) :
    pointEvaluation x (Ideal.Quotient.mk (vanishingIdeal ℝ S) (MvPolynomial.X i)) = x.val i := by
  exact eval_X (R := ℝ) (f := x.val) i

noncomputable def identityIso {n : ℕ} {X : RealVariety n} {r : ℕ}
    (P : ProjectionBundle X r) : BundleIso P P where
  forward := P.projection
  inverse := P.projection
  forward_continuous := P.continuous
  inverse_continuous := P.continuous
  preserves x := ⟨P.idempotent x, P.idempotent x⟩
  inverse_preserves x := ⟨P.idempotent x, P.idempotent x⟩
  left := P.idempotent
  right := P.idempotent

example {n : ℕ} {X : RealVariety n} {r : ℕ} (P : ProjectionBundle X r)
    (S : Stratification X) (h : IsAlgebraicFor P S) : IsAlgebraicIsoFor (identityIso P) S :=
  ⟨h, h, fun i ↦ ⟨h i, h i⟩⟩

example :
    RegularOn (Set.univ : Set (Ambient 1)) (fun x ↦ 1 / (1 + (x 0) ^ 2)) := by
  intro x _
  refine ⟨1, 1 + (MvPolynomial.X 0) ^ 2, ?_, ?_⟩
  · simp only [eval_add, map_one, eval_pow, eval_X]
    nlinarith [sq_nonneg (x 0)]
  · intro y _ _
    simp only [eval_add, map_one, eval_pow, eval_X]
    have hy : 1 + (y 0) ^ 2 ≠ 0 := by nlinarith [sq_nonneg (y 0)]
    simp [hy]

end MathlibExtTest.AlgebraicGeometry.RealBundleFibres
