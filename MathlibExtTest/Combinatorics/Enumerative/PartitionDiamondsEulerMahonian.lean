/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PartitionDiamondsEulerMahonian
import Mathlib.Data.ZMod.Basic

open MetaMathlibExt

-- Positions are numbered from one, and the last letter has no following descent.
example : permDescentSet (Fin.revPerm : Equiv.Perm (Fin 3)) = {1, 2} := by decide

-- The first insertion step, over an arbitrary coefficient ring.
example (R : Type*) [CommRing R] (x y : R) :
    (1 - y) * eulerMahonian R 2 x y = (1 - x * y ^ 2) - y * (1 - x) := by
  simpa only [eulerMahonian_one, mul_one] using eulerMahonian_succ_recursion R 1 le_rfl x y

-- Here 1 - y is a nonzero zero divisor.
example : eulerMahonian (ZMod 8) 3 2 3 = 5 := by decide

-- The last link position is constant beyond the end of the shape.
example : diamondLinkPos [1, 2] 3 = 5 := by decide

-- The triples (0, 1, 2) and (1, 1, 1) both contribute to a * b^2.
example : multifoldDiamondCount [1] 1 2 = 2 := by decide

-- After clearing the three denominator factors, the coefficient of a * b^2 vanishes.
example : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 2)
    ((1 - MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ 2) *
      ((1 - MvPowerSeries.X 0 * MvPowerSeries.X 1) * (1 - MvPowerSeries.X 1)) *
      multifoldDiamondSeries [1]) = 0 := by
  have h : (1 - MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ 2) *
      ((1 - MvPowerSeries.X 0 * MvPowerSeries.X 1) * (1 - MvPowerSeries.X 1)) *
      multifoldDiamondSeries [1] = 1 := by
    simpa [Finset.Icc_self, Finset.prod_range_succ, eulerMahonian_one, mul_comm, mul_left_comm]
      using partitionDiamond_genFun 1 1 le_rfl le_rfl
  rw [h, MvPowerSeries.coeff_one]
  apply ite_eq_right
  intro he
  have h1 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) he
  simp at h1
