/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.MvPowerSeries.WeightedRescale

@[expose] public section

open MvPowerSeries

private noncomputable def weightedDegree : (Fin 2 →₀ ℕ) →+ ℕ :=
  Finsupp.weight fun i => if i = 0 then 1 else 3

private noncomputable def degreeFiveMonomial : Fin 2 →₀ ℕ :=
  Finsupp.single 0 2 + Finsupp.single 1 1

-- At `ε = 0`, the constant monomial keeps its coefficient because `0 ^ 0 = 1`.
example :
    coeff 0
        (rescale (fun i : Fin 2 => (0 : ℚ) ^ Finsupp.degree (Finsupp.single i 1))
          (map (algebraMap ℚ ℚ) (monomial 0 7))) = 7 := by
  rw [coeff_rescale_map_of_weight]
  norm_num

-- At `ε = 0`, every positive-weight monomial vanishes.
example :
    coeff (Finsupp.single (0 : Fin 2) 2)
        (rescale (fun i : Fin 2 => (0 : ℚ) ^ Finsupp.degree (Finsupp.single i 1))
          (map (algebraMap ℚ ℚ) (monomial (Finsupp.single 0 2) 7))) = 0 := by
  rw [coeff_rescale_map_of_weight]
  norm_num

-- At `ε = 1`, weighted rescaling is coefficientwise the ordinary coefficient map.
example {σ R : Type*} [CommRing R] [Algebra ℚ R] (wt : (σ →₀ ℕ) →+ ℕ)
    (q : MvPowerSeries σ ℚ) (d : σ →₀ ℕ) :
    coeff d
        (rescale (fun i => (1 : R) ^ wt (Finsupp.single i 1))
          (map (algebraMap ℚ R) q)) =
      coeff d (map (algebraMap ℚ R) q) := by
  rw [coeff_rescale_map_of_weight, coeff_map]
  simp

-- Weights `1, 3` and exponents `2, 1` produce the scalar `ε ^ 5`.
example (ε : ℚ) :
    coeff degreeFiveMonomial
        (rescale (fun i => ε ^ weightedDegree (Finsupp.single i 1))
          (map (algebraMap ℚ ℚ) (monomial degreeFiveMonomial 7))) =
      7 * ε ^ 5 := by
  rw [coeff_rescale_map_of_weight, coeff_monomial_same]
  norm_num [degreeFiveMonomial, weightedDegree, Finsupp.weight_single]

-- The coefficient characterization reconstructs the canonical mapped and rescaled series.
example {σ R : Type*} [CommRing R] [Algebra ℚ R] (wt : (σ →₀ ℕ) →+ ℕ)
    (ε : R) (q : MvPowerSeries σ ℚ) (w : MvPowerSeries σ R)
    (hw : ∀ d, coeff d w = algebraMap ℚ R (coeff d q) * ε ^ wt d) :
    w = rescale (fun i => ε ^ wt (Finsupp.single i 1)) (map (algebraMap ℚ R) q) := by
  exact (eq_rescale_map_of_weight_iff wt ε q w).2 hw

-- Direct source equivalence: the source's coefficient function is this canonical series.
example {σ R : Type*} [CommRing R] [Algebra ℚ R] (wt : (σ →₀ ℕ) →+ ℕ)
    (ε : R) (q : MvPowerSeries σ ℚ) :
    rescale (fun i => ε ^ wt (Finsupp.single i 1)) (map (algebraMap ℚ R) q) =
      (fun d => algebraMap ℚ R (coeff d q) * ε ^ wt d) := by
  ext d
  exact coeff_rescale_map_of_weight wt ε q d

#print axioms MvPowerSeries.coeff_rescale_map_of_weight
#print axioms MvPowerSeries.eq_rescale_map_of_weight_iff
