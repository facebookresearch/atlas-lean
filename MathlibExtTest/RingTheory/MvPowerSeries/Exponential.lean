/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.MvPowerSeries.Exponential

import Mathlib.Algebra.CharP.Algebra

@[expose] public section

open MvPowerSeries

-- Ordinary one-variable coefficients of the new API.
example (n : ℕ) :
    coeff (Finsupp.single () n)
      (expOfConstantCoeffZero (X () : MvPowerSeries Unit ℚ) (by simp)) =
      (n.factorial : ℚ)⁻¹ := by
  rw [expOfConstantCoeffZero_eq_subst, PowerSeries.coeff_subst_single]
  simp

example : coeff (Finsupp.single () 0)
    (expOfConstantCoeffZero (X () : MvPowerSeries Unit ℚ) (by simp)) = 1 := by
  rw [expOfConstantCoeffZero_eq_subst, PowerSeries.coeff_subst_single]
  norm_num [Nat.factorial]

example : coeff (Finsupp.single () 1)
    (expOfConstantCoeffZero (X () : MvPowerSeries Unit ℚ) (by simp)) = 1 := by
  rw [expOfConstantCoeffZero_eq_subst, PowerSeries.coeff_subst_single]
  norm_num [Nat.factorial]

example : coeff (Finsupp.single () 2)
    (expOfConstantCoeffZero (X () : MvPowerSeries Unit ℚ) (by simp)) = 1 / 2 := by
  rw [expOfConstantCoeffZero_eq_subst, PowerSeries.coeff_subst_single]
  norm_num [Nat.factorial]

example : coeff (Finsupp.single () 3)
    (expOfConstantCoeffZero (X () : MvPowerSeries Unit ℚ) (by simp)) = 1 / 6 := by
  rw [expOfConstantCoeffZero_eq_subst, PowerSeries.coeff_subst_single]
  norm_num [Nat.factorial]

-- Zero and an empty variable set are both allowed.
example : expOfConstantCoeffZero (0 : MvPowerSeries Unit ℚ) (by simp) = 1 := by
  simp

example : expOfConstantCoeffZero (0 : MvPowerSeries Empty ℚ) (by simp) = 1 := by
  simp

-- The finite sum also accepts a nonzero constant series, unlike the exponential API.
example : expTrunc 0 (C (1 : ℚ) : MvPowerSeries Unit ℚ) = 0 := by
  simp [expTrunc]

example : expTrunc 2 (C (1 : ℚ) : MvPowerSeries Unit ℚ) = C 2 := by
  have hc : (C (2 : ℚ) : MvPowerSeries Unit ℚ) = 1 + 1 := by
    rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one]
  simpa [expTrunc, Finset.sum_range_succ] using hc.symm

example : ¬ constantCoeff (C (1 : ℚ) : MvPowerSeries Unit ℚ) = 0 := by
  simp

-- The canonical variable bridge is visible from an importing client.
example {σ R : Type*} [CommRing R] [Algebra ℚ R] (i : σ) :
    expOfConstantCoeffZero (X i : MvPowerSeries σ R) (by simp) =
      (PowerSeries.exp R).toMvPowerSeries i := by
  exact expOfConstantCoeffZero_X i

-- Finite coefficient stabilization is usable at the exact degree boundary and beyond it.
example : coeff (Finsupp.single () 3)
    (expOfConstantCoeffZero (X () : MvPowerSeries Unit ℚ) (by simp)) =
      coeff (Finsupp.single () 3) (expTrunc 4 (X ())) := by
  simpa using coeff_expOfConstantCoeffZero_degree
    (X () : MvPowerSeries Unit ℚ) (by simp) (Finsupp.single () 3)

example : coeff (Finsupp.single () 3)
    (expOfConstantCoeffZero (X () : MvPowerSeries Unit ℚ) (by simp)) =
      coeff (Finsupp.single () 3) (expTrunc 8 (X ())) := by
  apply coeff_expOfConstantCoeffZero
  simp

-- Mixed coefficients exercise the addition law on independent variables.
example : coeff (Finsupp.single (0 : Fin 2) 2 + Finsupp.single 1 1)
    (expOfConstantCoeffZero (X 0 + X 1 : MvPowerSeries (Fin 2) ℚ) (by simp)) = 1 / 2 := by
  rw [expOfConstantCoeffZero_add (by simp) (by simp),
    expOfConstantCoeffZero_eq_subst, expOfConstantCoeffZero_eq_subst,
    PowerSeries.coeff_subst_X_zero_subst_mul_X_one]
  norm_num [Nat.factorial]

-- A nonlinear substituted series has both supported and unsupported degrees.
example : PowerSeries.coeff 4
    (expOfConstantCoeffZero (PowerSeries.X ^ 2 : PowerSeries ℚ)
      (by simp [PowerSeries.X_apply])) = 1 / 2 := by
  rw [expOfConstantCoeffZero_eq_subst, PowerSeries.coeff_subst_X_pow (by decide)]
  norm_num [Nat.factorial]

example : PowerSeries.coeff 3
    (expOfConstantCoeffZero (PowerSeries.X ^ 2 : PowerSeries ℚ)
      (by simp [PowerSeries.X_apply])) = 0 := by
  rw [expOfConstantCoeffZero_eq_subst, PowerSeries.coeff_subst_X_pow (by decide)]
  norm_num

-- Coefficient maps transport the new exponential, here into a ring with zero divisors.
example : coeff (Finsupp.single () 2)
    (expOfConstantCoeffZero
      (map (algebraMap ℚ (ℚ × ℚ)) (X () : MvPowerSeries Unit ℚ)) (by simp)) =
      (1 / 2, 1 / 2) := by
  rw [← map_expOfConstantCoeffZero (algebraMap ℚ (ℚ × ℚ)) (X ()) (by simp),
    coeff_map, expOfConstantCoeffZero_eq_subst, PowerSeries.coeff_subst_single]
  norm_num [Nat.factorial, Prod.algebraMap_apply]

-- Nontrivial coefficient rings satisfying the API's ℚ-algebra hypothesis have characteristic zero.
example {R : Type*} [CommRing R] [Algebra ℚ R] [Nontrivial R] : CharZero R :=
  algebraRat.charZero R

-- Transitive trusted-axiom audit of every public declaration added in the source module.
#print axioms MvPowerSeries.expTrunc
#print axioms MvPowerSeries.expOfConstantCoeffZero
#print axioms MvPowerSeries.expOfConstantCoeffZero_eq_subst
#print axioms MvPowerSeries.coeff_expOfConstantCoeffZero
#print axioms MvPowerSeries.coeff_expOfConstantCoeffZero_degree
#print axioms MvPowerSeries.constantCoeff_expOfConstantCoeffZero
#print axioms MvPowerSeries.expOfConstantCoeffZero_zero
#print axioms MvPowerSeries.map_expOfConstantCoeffZero
#print axioms MvPowerSeries.expOfConstantCoeffZero_X
#print axioms MvPowerSeries.expOfConstantCoeffZero_add
