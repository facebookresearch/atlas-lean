/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.MvPowerSeries.WeightedExponential

@[expose] public section

open MvPowerSeries

private noncomputable def weightedDegree : (Fin 2 →₀ ℕ) →+ ℕ :=
  Finsupp.weight fun i => if i = 0 then 1 else 3

private noncomputable def zeroFirstWeight : (Fin 2 →₀ ℕ) →+ ℕ :=
  Finsupp.weight fun i => if i = 0 then 0 else 3

private noncomputable def unitWeight : (Unit →₀ ℕ) →+ ℕ :=
  Finsupp.weight fun _ => 1

private noncomputable def degreeFiveMonomial : Fin 2 →₀ ℕ :=
  Finsupp.single 0 2 + Finsupp.single 1 1

-- Breaking finite weighted commutation must fail for arbitrary inputs and bounds.
example (N : ℕ) (q : MvPowerSeries (Fin 2) ℚ) (ε : ℚ) :
    expTrunc N
        (rescale (fun i => ε ^ weightedDegree (Finsupp.single i 1))
          (map (algebraMap ℚ ℚ) q)) =
      rescale (fun i => ε ^ weightedDegree (Finsupp.single i 1))
        (map (algebraMap ℚ ℚ) (expTrunc N q)) := by
  exact expTrunc_rescale_map_of_weight weightedDegree ε q N

-- Breaking lawful full weighted commutation must fail on zero-constant inputs.
example (q : MvPowerSeries (Fin 2) ℚ) (hq : constantCoeff q = 0) (ε : ℚ) :
    expOfConstantCoeffZero
        (rescale (fun i => ε ^ weightedDegree (Finsupp.single i 1))
          (map (algebraMap ℚ ℚ) q)) (by
            rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale_map_of_weight,
              coeff_zero_eq_constantCoeff_apply, hq]
            simp) =
      rescale (fun i => ε ^ weightedDegree (Finsupp.single i 1))
        (map (algebraMap ℚ ℚ) (expOfConstantCoeffZero q hq)) := by
  exact expOfConstantCoeffZero_rescale_map_of_weight weightedDegree ε q hq

-- The coefficient hypothesis itself must imply the target has zero constant coefficient.
example (q w : MvPowerSeries (Fin 2) ℚ) (hq : constantCoeff q = 0) (ε : ℚ)
    (hw : ∀ d, coeff d w = coeff d q * ε ^ weightedDegree d) :
    constantCoeff w = 0 := by
  exact constantCoeff_eq_zero_of_weight weightedDegree ε q hq hw

-- Breaking reconstruction from weighted coefficients must fail without a separate target premise.
example (q w : MvPowerSeries (Fin 2) ℚ) (hq : constantCoeff q = 0) (ε : ℚ)
    (hw : ∀ d, coeff d w = coeff d q * ε ^ weightedDegree d) (d : Fin 2 →₀ ℕ) :
    coeff d
        (expOfConstantCoeffZero w
          (constantCoeff_eq_zero_of_weight weightedDegree ε q hq hw)) =
      coeff d (expOfConstantCoeffZero q hq) * ε ^ weightedDegree d := by
  exact coeff_expOfConstantCoeffZero_of_weight weightedDegree ε q hq hw d

-- A wrong weighted exponent or factorial changes the hand-computed value `ε ^ 5 / 2`.
example (ε : ℚ) :
    coeff degreeFiveMonomial
        (expOfConstantCoeffZero
          (rescale (fun i => ε ^ weightedDegree (Finsupp.single i 1))
            (map (algebraMap ℚ ℚ) (X 0 + X 1))) (by
              rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale_map_of_weight]
              simp)) =
      ε ^ 5 / 2 := by
  rw [expOfConstantCoeffZero_rescale_map_of_weight (hq := by simp),
    coeff_rescale_map_of_weight,
    expOfConstantCoeffZero_add (by simp) (by simp),
    expOfConstantCoeffZero_eq_subst, expOfConstantCoeffZero_eq_subst,
    PowerSeries.coeff_subst_X_zero_subst_mul_X_one]
  norm_num [degreeFiveMonomial, weightedDegree, Finsupp.weight_single, Nat.factorial]
  ring

-- The mixed coefficient is populated: at `ε = 2`, it is `2 ^ 5 / 2 = 16`.
example :
    coeff degreeFiveMonomial
        (expOfConstantCoeffZero
          (rescale (fun i => (2 : ℚ) ^ weightedDegree (Finsupp.single i 1))
            (map (algebraMap ℚ ℚ) (X 0 + X 1))) (by
              rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale_map_of_weight]
              simp)) = 16 := by
  rw [expOfConstantCoeffZero_rescale_map_of_weight (hq := by simp),
    coeff_rescale_map_of_weight,
    expOfConstantCoeffZero_add (by simp) (by simp),
    expOfConstantCoeffZero_eq_subst, expOfConstantCoeffZero_eq_subst,
    PowerSeries.coeff_subst_X_zero_subst_mul_X_one]
  norm_num [degreeFiveMonomial, weightedDegree, Finsupp.weight_single, Nat.factorial]

-- At `ε = 0`, the exponential constant coefficient remains one because `0 ^ 0 = 1`.
example :
    coeff 0
        (expOfConstantCoeffZero
          (rescale (fun i => (0 : ℚ) ^ weightedDegree (Finsupp.single i 1))
            (map (algebraMap ℚ ℚ) (X 0 + X 1))) (by
              rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale_map_of_weight]
              simp)) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_expOfConstantCoeffZero]

-- At `ε = 0`, a positive-weight coefficient vanishes.
example :
    coeff (Finsupp.single (0 : Fin 2) 1)
        (expOfConstantCoeffZero
          (rescale (fun i => (0 : ℚ) ^ weightedDegree (Finsupp.single i 1))
            (map (algebraMap ℚ ℚ) (X 0 + X 1))) (by
              rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale_map_of_weight]
              simp)) = 0 := by
  rw [expOfConstantCoeffZero_rescale_map_of_weight (hq := by simp),
    coeff_rescale_map_of_weight]
  norm_num [weightedDegree, Finsupp.weight_single]

-- At `ε = 0`, a nonconstant zero-weight monomial survives through `0 ^ 0 = 1`.
example :
    coeff (Finsupp.single (0 : Fin 2) 2)
        (expOfConstantCoeffZero
          (rescale (fun i => (0 : ℚ) ^ zeroFirstWeight (Finsupp.single i 1))
            (map (algebraMap ℚ ℚ) (X 0))) (by
              rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale_map_of_weight]
              simp)) = 1 / 2 := by
  rw [expOfConstantCoeffZero_rescale_map_of_weight (hq := by simp),
    coeff_rescale_map_of_weight,
    expOfConstantCoeffZero_eq_subst, PowerSeries.coeff_subst_single]
  norm_num [zeroFirstWeight, Finsupp.weight_single, Nat.factorial]

-- At `ε = 1`, the result is the mapped original coefficient in `ℚ × ℚ`.
example (d : Fin 2 →₀ ℕ) :
    coeff d
        (expOfConstantCoeffZero
          (rescale (fun i => (1 : ℚ × ℚ) ^ weightedDegree (Finsupp.single i 1))
            (map (algebraMap ℚ (ℚ × ℚ)) (X 0 + X 1))) (by
              rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale_map_of_weight]
              simp)) =
      coeff d
        (map (algebraMap ℚ (ℚ × ℚ))
          (expOfConstantCoeffZero (X 0 + X 1 : MvPowerSeries (Fin 2) ℚ) (by simp))) := by
  rw [expOfConstantCoeffZero_rescale_map_of_weight (hq := by simp),
    coeff_rescale_map_of_weight, coeff_map]
  simp

-- The exact source degreewise specialization is the finite law at `N = degree + 1`.
example (q : MvPowerSeries (Fin 2) ℚ) (ε : ℚ) (d : Fin 2 →₀ ℕ) :
    coeff d
        (expTrunc (d.degree + 1)
          (rescale (fun i => ε ^ weightedDegree (Finsupp.single i 1))
            (map (algebraMap ℚ ℚ) q))) =
      coeff d (expTrunc (d.degree + 1) q) * ε ^ weightedDegree d := by
  exact coeff_expTrunc_rescale_map_of_weight weightedDegree ε q (d.degree + 1) d

-- A zero-constant restriction on the finite law would reject this source case.
example (ε : ℚ) :
    coeff (Finsupp.single () 1)
        (expTrunc 3
          (rescale (fun i => ε ^ unitWeight (Finsupp.single i 1))
            (map (algebraMap ℚ ℚ) (C 1 + X ())))) =
      2 * ε := by
  rw [coeff_expTrunc_rescale_map_of_weight]
  have hcoeff : coeff (Finsupp.single () 1)
      (expTrunc 3 (C 1 + X () : MvPowerSeries Unit ℚ)) = 2 := by
    change PowerSeries.coeff 1 (expTrunc 3 (PowerSeries.C 1 + PowerSeries.X)) = 2
    simp [expTrunc, Finset.sum_range_succ, PowerSeries.coeff_X]
    rw [show (1 + PowerSeries.X : PowerSeries ℚ) ^ 2 =
      1 + (2 : ℚ) • PowerSeries.X + PowerSeries.X ^ 2 by
        rw [two_smul ℚ]
        ring]
    simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    norm_num
  rw [hcoeff]
  norm_num [unitWeight, Finsupp.weight_single]

-- Transitive trusted-axiom audit of every public declaration in the source module.
#print axioms MvPowerSeries.expTrunc_rescale_map_of_weight
#print axioms MvPowerSeries.coeff_expTrunc_rescale_map_of_weight
#print axioms MvPowerSeries.expOfConstantCoeffZero_rescale_map_of_weight
#print axioms MvPowerSeries.constantCoeff_eq_zero_of_weight
#print axioms MvPowerSeries.coeff_expOfConstantCoeffZero_of_weight
