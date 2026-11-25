/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Euclidean.Morley

/-! # Tests for Morley's trisector theorem -/

open MathlibExt.Geometry.MorleyWanted.Geometry.Morley

-- A repeated point forces all three points of an equilateral triple to coincide.
example (P Q : Plane) : IsEquilateralTriple P P Q ↔ P = Q := by
  simp [IsEquilateralTriple, dist_comm Q P]

-- The closed triangle contains its edges, including when its vertices are collinear.
example (A B C : Plane) : LiesInTriangle A B C (midpoint ℝ A B) :=
  (convex_convexHull ℝ _).midpoint_mem
    (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))

example (A B C P Q R : Plane) (h : Collinear ℝ ({A, B, C} : Set Plane)) :
    ¬ IsMorleyConfiguration A B C P Q R :=
  fun hconfig => hconfig.1 h

example (A B C P Q R : Plane) (h : IsMorleyConfiguration A B C P Q R) :
    dist P Q = dist Q R ∧ dist Q R = dist R P :=
  morley_theorem A B C P Q R h
