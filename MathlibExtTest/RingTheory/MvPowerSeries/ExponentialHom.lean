/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.MvPowerSeries.ExponentialHom

@[expose] public section

open MvPowerSeries

-- The boundary truncation is preserved without assumptions on its input.
example : expTrunc 0 (C (7 : ℚ) : MvPowerSeries Unit ℚ) = 0 := by
  simp [expTrunc]

-- A genuine coefficient homomorphism preserves a truncation with nonzero constant input.
example :
    map (algebraMap ℚ (ℚ × ℚ)) (expTrunc 2 (C (1 : ℚ) : MvPowerSeries Unit ℚ)) =
      expTrunc 2 (map (algebraMap ℚ (ℚ × ℚ)) (C 1)) := by
  exact map_expTrunc (map (algebraMap ℚ (ℚ × ℚ))) 2 (C 1)

-- The same example has a populated, explicitly computed output coefficient.
example : coeff 0
    (map (algebraMap ℚ (ℚ × ℚ))
      (expTrunc 2 (C (1 : ℚ) : MvPowerSeries Unit ℚ))) = (2, 2) := by
  rw [map_expTrunc]
  simp [expTrunc, Finset.sum_range_succ]
  apply Prod.ext <;> norm_num

-- Rescaling a variable by two satisfies the degree-filtration premise.
example :
    (rescale (fun _ : Unit => (2 : ℚ)))
        (expOfConstantCoeffZero (X ()) (by simp)) =
      expOfConstantCoeffZero ((rescale (fun _ : Unit => (2 : ℚ))) (X ())) (by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
        simp [coeff_zero_eq_constantCoeff_apply]) := by
  apply hom_expOfConstantCoeffZero
  intro d f g h
  rw [coeff_rescale, coeff_rescale, h d (le_refl _)]

-- Its cubic output coefficient is 2^3/3! = 4/3.
example : coeff (Finsupp.single () 3)
    ((rescale (fun _ : Unit => (2 : ℚ)))
      (expOfConstantCoeffZero (X ()) (by simp))) = 4 / 3 := by
  rw [coeff_rescale, expOfConstantCoeffZero_eq_subst,
    PowerSeries.coeff_subst_single]
  norm_num [Finsupp.prod_single_index, Nat.factorial]

-- The exact source endomorphism clause specializes to the identity.
example {σ R : Type*} [CommRing R] [Algebra ℚ R]
    (w : MvPowerSeries σ R) (hw : constantCoeff w = 0) :
    (RingHom.id (MvPowerSeries σ R)) (expOfConstantCoeffZero w hw) =
      expOfConstantCoeffZero ((RingHom.id (MvPowerSeries σ R)) w) (by simpa using hw) := by
  apply hom_expOfConstantCoeffZero
  intro d f g h
  exact h d (le_refl _)

-- The degree-filtered law also covers zero input for a nonidentity endomorphism.
example :
    (rescale (fun _ : Unit => (2 : ℚ)))
        (expOfConstantCoeffZero (0 : MvPowerSeries Unit ℚ) (by simp)) =
      expOfConstantCoeffZero
        ((rescale (fun _ : Unit => (2 : ℚ))) (0 : MvPowerSeries Unit ℚ)) (by simp) := by
  apply hom_expOfConstantCoeffZero
  intro d f g h
  rw [coeff_rescale, coeff_rescale, h d (le_refl _)]

-- Transitive trusted-axiom audit of every public declaration added in the source module.
#print axioms MvPowerSeries.map_expTrunc
#print axioms MvPowerSeries.hom_expOfConstantCoeffZero
