/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CoxNormalizedSheafification

open CategoryTheory
open MathlibExt.AlgebraicGeometry
open FiniteToricCoordinates CoxGradedSheaves CoxNormalizedSheafification

example {n : ℕ} {F : FiniteFan n} (R : Rays F) (u : Lattice n) :
    (QuotientAddGroup.mk' (characterRayMap R).range) (characterRayMap R u) = 0 := by
  exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨u, rfl⟩

example {n : ℕ} {F : FiniteFan n} (R : Rays F) (sigma : Cone n) (M : GradedModule R)
    (x : degreeZeroModule R sigma M) :
    degreeZeroMap R sigma (𝟙 M) x = x := by
  apply Subtype.ext
  change (LocalizedModule.map (Submonoid.powers (denominator R sigma)) LinearMap.id) x.val = x.val
  rw [LocalizedModule.map_id]
  rfl

example {n : ℕ} {F : FiniteFan n} (R : Rays F) :
    (1 : CoxRing R) ≠ 0 := one_ne_zero

