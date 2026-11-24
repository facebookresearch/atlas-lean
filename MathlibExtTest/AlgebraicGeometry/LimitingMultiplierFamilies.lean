/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.LimitingMultiplierFamilies

/-!
# Tests for limiting multiplier families

Every candidate image lies in the limiting ideal, and on an affine open the limiting ideal is the
supremum of the candidate images there.
-/

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.NaturalPullbackMultiplierModules
open MathlibExt.AlgebraicGeometry.LimitingMultiplierFamilies

variable {k : Type} [Field k] {n : ℕ} {V : NormalVariety k n} {C : CanonicalData V}
  [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]
  {I : V.X.left.IdealSheafData} {c : ℝ}

example (F : LimitingFamily V C I c) (m : ℕ+) : (F.image m).ideal ≤ limitingIdeal F :=
  le_iSup (fun m : ℕ+ ↦ (F.image m).ideal) m

example (F : LimitingFamily V C I c) (U : V.X.left.affineOpens) :
    (limitingIdeal F).ideal U = ⨆ m : ℕ+, (F.image m).ideal.ideal U :=
  limitingIdeal_affine F U
