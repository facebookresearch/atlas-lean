/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Chemistry.VariationalPerturbationHuckel
public import Mathlib.Tactic

@[expose] public section

open scoped Matrix

namespace PhyslibExtTest.Chemistry.VariationalPerturbationHuckel

open PhyslibExt.Chemistry.VariationalPerturbationHuckel

theorem test_rayleigh_value : rayleighQuotient (!![2, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 1] = 1 / 2 := by
  norm_num [rayleighQuotient, Matrix.mulVec, dotProduct]

theorem test_rayleigh_bound (hH : (!![2, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian) : sInf (Set.range hH.eigenvalues) ≤ rayleighQuotient (!![2, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 1] := by
  have hx : (![1, 1] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrArg (fun v : Fin 2 → ℝ => v 0) h
    simp at h0
  exact rayleighQuotient_ge_eigenvalues_min (by norm_num) hH hx

theorem test_generalized_value (hH : (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian) (hS : (1 : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian) (hSpos : ∀ x : Fin 2 → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x) : (2 : ℝ) = generalizedRayleighQuotient (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0] := by
  have hc : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrArg (fun v : Fin 2 → ℝ => v 0) h
    simp at h0
  have hEc : (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 0] = (2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 0]) := by
    ext i
    fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Function.comp_apply]
  exact generalizedEigenvalue_eq_ratio hH hS hSpos hc hEc

theorem test_firstOrder_hd : ∀ j : Fin 2, j ≠ 0 → (![0, 1] : Fin 2 → ℝ) 0 - (![0, 1] : Fin 2 → ℝ) j ≠ 0 := by
  intro j hj
  fin_cases j
  · exact absurd rfl hj
  · simp

theorem test_firstOrder_symbolic (t : ℝ) : (Matrix.diagonal (![0, 1] : Fin 2 → ℝ) + t • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ ((Pi.single 0 1 : Fin 2 → ℝ) + t • pertV1 (![0, 1] : Fin 2 → ℝ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) - (((![0, 1] : Fin 2 → ℝ) 0 + t * pertE1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) • ((Pi.single 0 1 : Fin 2 → ℝ) + t • pertV1 (![0, 1] : Fin 2 → ℝ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ))) = t ^ 2 • (((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ pertV1 (![0, 1] : Fin 2 → ℝ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) - pertE1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) • pertV1 (![0, 1] : Fin 2 → ℝ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) := by
  exact firstOrder_residual (![0, 1] : Fin 2 → ℝ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) test_firstOrder_hd t

theorem test_firstOrder_numeric : (Matrix.diagonal (![0, 1] : Fin 2 → ℝ) + (1 : ℝ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ ((Pi.single 0 1 : Fin 2 → ℝ) + (1 : ℝ) • pertV1 (![0, 1] : Fin 2 → ℝ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) - (((![0, 1] : Fin 2 → ℝ) 0 + (1 : ℝ) * pertE1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) • ((Pi.single 0 1 : Fin 2 → ℝ) + (1 : ℝ) • pertV1 (![0, 1] : Fin 2 → ℝ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ))) = (1 : ℝ) ^ 2 • (((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ pertV1 (![0, 1] : Fin 2 → ℝ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) - pertE1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) • pertV1 (![0, 1] : Fin 2 → ℝ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have h := firstOrder_residual (![0, 1] : Fin 2 → ℝ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) test_firstOrder_hd (1 : ℝ)
  simpa using h

theorem test_path_eigenvector : huckelMatrix (0 : ℝ) (-1) (SimpleGraph.pathGraph 2) *ᵥ (fun j : Fin 2 => Real.sin ((1 * (j.val + 1) : ℕ) * Real.pi / (2 + 1))) = ((0 : ℝ) + 2 * (-1) * Real.cos (1 * Real.pi / (2 + 1))) • (fun j : Fin 2 => Real.sin ((1 * (j.val + 1) : ℕ) * Real.pi / (2 + 1))) := by
  have h := huckel_path_eigenvector (n := 2) (by norm_num) (0 : ℝ) (-1) (k := 1)
    (by norm_num) (by norm_num)
  simpa using h

theorem test_path_eigenvalue : (0 : ℝ) + 2 * (-1) * Real.cos (1 * Real.pi / (2 + 1)) = -1 := by
  norm_num [Real.cos_pi_div_three]

theorem test_cycle_eigenvector_N3 : huckelMatrix (0 : ℝ) 1 (SimpleGraph.cycleGraph (0 + 3)) *ᵥ (fun j : Fin (0 + 3) => Real.cos (2 * Real.pi * 1 * j.val / (0 + 3))) = ((0 : ℝ) + 2 * 1 * Real.cos (2 * Real.pi * 1 / (0 + 3))) • (fun j : Fin (0 + 3) => Real.cos (2 * Real.pi * 1 * j.val / (0 + 3))) := by
  have h := huckel_cycle_eigenvector_cos (n := 0) (0 : ℝ) 1 1
  simpa using h

theorem test_cycle_eigenvalue_N3 : (0 : ℝ) + 2 * 1 * Real.cos (2 * Real.pi * 1 / (0 + 3)) = -1 := by
  have harg : (2 : ℝ) * Real.pi * 1 / (0 + 3) = Real.pi - Real.pi / 3 := by ring
  rw [harg, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

theorem test_cycle_eigenvector_N4 : huckelMatrix (0 : ℝ) 1 (SimpleGraph.cycleGraph (1 + 3)) *ᵥ (fun j : Fin (1 + 3) => Real.cos (2 * Real.pi * 2 * j.val / (1 + 3))) = ((0 : ℝ) + 2 * 1 * Real.cos (2 * Real.pi * 2 / (1 + 3))) • (fun j : Fin (1 + 3) => Real.cos (2 * Real.pi * 2 * j.val / (1 + 3))) := by
  have h := huckel_cycle_eigenvector_cos (n := 1) (0 : ℝ) 1 2
  simpa using h

theorem test_cycle_eigenvalue_N4 : (0 : ℝ) + 2 * 1 * Real.cos (2 * Real.pi * 2 / (1 + 3)) = -2 := by
  have harg : (2 : ℝ) * Real.pi * 2 / (1 + 3) = Real.pi := by ring
  rw [harg, Real.cos_pi]
  norm_num

theorem test_cycle_flip_mulVec_N4 (v : Fin (1 + 3) → ℝ) (hEv : huckelMatrix (0 : ℝ) 1 (SimpleGraph.cycleGraph (1 + 3)) *ᵥ v = (-2 : ℝ) • v) : huckelMatrix (0 : ℝ) 1 (SimpleGraph.cycleGraph (1 + 3)) *ᵥ alternatingFlip v = (2 * (0 : ℝ) - (-2)) • alternatingFlip v := by
  have hN : Even (1 + 3) := ⟨2, by norm_num⟩
  exact huckel_cycle_flip_mulVec hN 0 1 hEv

/-- The constant mode on the 4-cycle (`k = 0`, energy `α + 2β`) pairs with a nonzero
eigenvector of energy `α - 2β`, here with `α = 0`, `β = 1`. -/
theorem test_cycle_pairing_N4 :
    alternatingFlip (fun j : Fin (1 + 3) =>
        Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) * j.val / (((1 : ℕ) : ℝ) + 3))) ≠ 0 ∧
      huckelMatrix (0 : ℝ) 1 (SimpleGraph.cycleGraph (1 + 3)) *ᵥ
        alternatingFlip (fun j : Fin (1 + 3) =>
          Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) * j.val / (((1 : ℕ) : ℝ) + 3))) =
        (-2 : ℝ) • alternatingFlip (fun j : Fin (1 + 3) =>
          Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) * j.val / (((1 : ℕ) : ℝ) + 3))) := by
  have hN : Even (1 + 3) := ⟨2, by norm_num⟩
  have h := huckel_cycle_pairing hN (0 : ℝ) 1 (huckel_cycle_cosMode_ne_zero (n := 1) 0)
    (huckel_cycle_eigenvector_cos (n := 1) (0 : ℝ) 1 0)
  have hE : 2 * (0 : ℝ) - ((0 : ℝ) + 2 * 1 *
      Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) + 3))) = -2 := by
    norm_num
  rw [hE] at h
  exact h

/-- The path sine mode `k = 1` on two vertices is nonzero. -/
theorem test_path_sineMode_ne_zero :
    (fun j : Fin 2 => Real.sin ((1 * (j.val + 1) : ℕ) * Real.pi / (2 + 1))) ≠ 0 :=
  huckel_path_sineMode_ne_zero (n := 2) (by norm_num) (k := 1) (by norm_num) (by norm_num)

/-- The cycle cosine mode `k = 1` on three vertices is nonzero. -/
theorem test_cycle_cosMode_ne_zero :
    (fun j : Fin (0 + 3) =>
      Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * j.val / (((0 : ℕ) : ℝ) + 3))) ≠ 0 :=
  huckel_cycle_cosMode_ne_zero (n := 0) 1

/-- Why `huckel_cycle_sinMode_mulVec` is only an action identity: at `k = 0` the sine vector is
zero. -/
theorem test_cycle_sinMode_zero :
    (fun j : Fin (0 + 3) => Real.sin (2 * Real.pi * (0 : ℕ) * j.val / (0 + 3))) = 0 := by
  funext j
  simp

theorem test_cycle_sinMode_mulVec_N3 : huckelMatrix (0 : ℝ) 1 (SimpleGraph.cycleGraph (0 + 3)) *ᵥ (fun j : Fin (0 + 3) => Real.sin (2 * Real.pi * 1 * j.val / (0 + 3))) = ((0 : ℝ) + 2 * 1 * Real.cos (2 * Real.pi * 1 / (0 + 3))) • (fun j : Fin (0 + 3) => Real.sin (2 * Real.pi * 1 * j.val / (0 + 3))) := by
  have h := huckel_cycle_sinMode_mulVec (n := 0) (0 : ℝ) 1 1
  simpa using h

theorem test_pairing_value : (2 : ℝ) * 0 - (-2) = 2 := by norm_num

theorem test_lcao_numeric1 : ((0 : ℝ) + -1) / (1 + 1 / 2) = -2 / 3 := by norm_num
theorem test_lcao_numeric2 : ((0 : ℝ) - -1) / (1 - 1 / 2) = 2 := by norm_num
theorem test_lcao_roots :
    ((!![0, -1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) -
      (((0 : ℝ) + -1) / (1 + 1 / 2)) • (!![1, 1 / 2; 1 / 2, 1] : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 ∧
    ((!![0, -1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) -
      (((0 : ℝ) - -1) / (1 - 1 / 2)) • (!![1, 1 / 2; 1 / 2, 1] : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 :=
  lcao_energies_are_roots (0 : ℝ) (-1) (1 / 2) (by norm_num) (by norm_num)

theorem test_pos_count : (Finset.univ.filter (fun k : Fin (4 * 1 + 2) => 0 < Real.cos (2 * Real.pi * k.val / (4 * 1 + 2)))).card = 3 := by
  have h := cycle_cos_pos_count_4m2 1
  norm_num at h ⊢
  exact h

theorem test_zero_count : (Finset.univ.filter (fun k : Fin (4 * 1) => Real.cos (2 * Real.pi * k.val / (4 * 1)) = 0)).card = 2 := by
  have h := cycle_cos_zero_count_4m (m := 1) (by norm_num)
  norm_num at h ⊢
  exact h

theorem test_closedForm_count_lt_alpha : (Finset.univ.filter (fun k : Fin (4 * 1 + 2) => (0 : ℝ) + 2 * (-1) * Real.cos (2 * Real.pi * k.val / (4 * 1 + 2)) < 0)).card = 3 := by
  have h := huckel_cycle_closedForm_count_lt_alpha_4m2 1 (0 : ℝ) (β := (-1 : ℝ)) (by norm_num)
  norm_num at h ⊢
  exact h

theorem test_closedForm_count_eq_alpha : (Finset.univ.filter (fun k : Fin (4 * 1) => (0 : ℝ) + 2 * (-1) * Real.cos (2 * Real.pi * k.val / (4 * 1)) = 0)).card = 2 := by
  have h := huckel_cycle_closedForm_count_eq_alpha_4m (m := 1) (by norm_num) 0 (-1) (by norm_num)
  norm_num at h ⊢
  exact h


/-! ### Second-order perturbation on a `3 × 3` example

`d = (0, 1, 2)`, a symmetric `H₁` and an `H₂` with nonzero off-diagonal entries. By hand:
`E₁ = 1`, `v₁ = (0, -1, -1/2)`, `E₂ = 1 - 1 - 1/2 = -1/2`, `v₂ = (0, -3/2, -3/4)`, and the full
residual is `t³ (-17/4, -1/4, -2) + t⁴ (-3, -3/2, -15/8)`: its `t²` coefficient vanishes in every
component. Both sides of `secondOrder_projected_residual` are reduced independently to
`-(17/4) t³ - 3 t⁴`. -/

/-- Unperturbed levels `(0, 1, 2)`. -/
abbrev tD : Fin 3 → ℝ := ![0, 1, 2]

/-- First-order perturbation (symmetric, nonzero off-diagonal entries). -/
abbrev tH1 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 1; 1, 0, 1; 1, 1, 0]

/-- Second-order perturbation (nonzero off-diagonal entries). -/
abbrev tH2 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 2; 1, 0, 1; 2, 1, 0]

private theorem erase_zero_fin3 : (Finset.univ.erase (0 : Fin 3)) = {1, 2} := by decide

private theorem single_zero_fin3 : (Pi.single 0 1 : Fin 3 → ℝ) = ![1, 0, 0] := by
  funext j
  fin_cases j <;> simp

private theorem tH1_isHermitian : tH1.IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

private theorem tD_gap : ∀ j : Fin 3, j ≠ 0 → tD 0 - tD j ≠ 0 := by
  intro j hj
  fin_cases j <;> simp_all

theorem test_pertE1_value : pertE1 tH1 = 1 := by
  simp [pertE1]

theorem test_pertV1_value : pertV1 tD tH1 = ![0, -1, -1 / 2] := by
  funext j
  fin_cases j <;> norm_num [pertV1]

theorem test_pertE2_value : pertE2 tD tH1 tH2 = -1 / 2 := by
  rw [pertE2, erase_zero_fin3, Finset.sum_pair (by decide)]
  norm_num

theorem test_pertV2_value : pertV2 tD tH1 tH2 = ![0, -3 / 2, -3 / 4] := by
  funext j
  fin_cases j <;> norm_num [pertV2, pertE1, erase_zero_fin3, Finset.sum_pair]

/-- The full second-order residual, from the definitions: no `t ^ 2` term in any component. -/
theorem test_secondOrder_full_residual (t : ℝ) :
    (Matrix.diagonal tD + t • tH1 + t ^ 2 • tH2) *ᵥ
        ((Pi.single 0 1 : Fin 3 → ℝ) + t • pertV1 tD tH1 + t ^ 2 • pertV2 tD tH1 tH2) -
      (tD 0 + t * pertE1 tH1 + t ^ 2 * pertE2 tD tH1 tH2) •
        ((Pi.single 0 1 : Fin 3 → ℝ) + t • pertV1 tD tH1 + t ^ 2 • pertV2 tD tH1 tH2) =
      t ^ 3 • ![-17 / 4, -1 / 4, -2] + t ^ 4 • ![-3, -3 / 2, -15 / 8] := by
  rw [test_pertV1_value, test_pertV2_value, test_pertE1_value, test_pertE2_value,
    single_zero_fin3]
  funext j
  fin_cases j <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply] <;>
    simp <;> ring

/-- Left side of `secondOrder_projected_residual`, reduced from the full residual. -/
theorem test_secondOrder_projected_lhs (t : ℝ) :
    (Pi.single 0 1 : Fin 3 → ℝ) ⬝ᵥ
      ((Matrix.diagonal tD + t • tH1 + t ^ 2 • tH2) *ᵥ
          ((Pi.single 0 1 : Fin 3 → ℝ) + t • pertV1 tD tH1 + t ^ 2 • pertV2 tD tH1 tH2) -
        (tD 0 + t * pertE1 tH1 + t ^ 2 * pertE2 tD tH1 tH2) •
          ((Pi.single 0 1 : Fin 3 → ℝ) + t • pertV1 tD tH1 + t ^ 2 • pertV2 tD tH1 tH2)) =
      -(17 / 4) * t ^ 3 - 3 * t ^ 4 := by
  rw [test_secondOrder_full_residual, single_dotProduct]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp
  ring

/-- Right side of `secondOrder_projected_residual`, reduced from the definitions. -/
theorem test_secondOrder_projected_rhs (t : ℝ) :
    t ^ 3 * ((tH1 *ᵥ pertV2 tD tH1 tH2 - pertE1 tH1 • pertV2 tD tH1 tH2 -
        pertE2 tD tH1 tH2 • pertV1 tD tH1 + tH2 *ᵥ pertV1 tD tH1) 0 +
        t * ((tH2 *ᵥ pertV2 tD tH1 tH2 - pertE2 tD tH1 tH2 • pertV2 tD tH1 tH2) 0)) =
      -(17 / 4) * t ^ 3 - 3 * t ^ 4 := by
  rw [test_pertV1_value, test_pertV2_value, test_pertE1_value, test_pertE2_value]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  simp
  ring

/-- `secondOrder_projected_residual` instantiated on the example. -/
theorem test_secondOrder_instance (t : ℝ) :
    (Pi.single 0 1 : Fin 3 → ℝ) ⬝ᵥ
      ((Matrix.diagonal tD + t • tH1 + t ^ 2 • tH2) *ᵥ
          ((Pi.single 0 1 : Fin 3 → ℝ) + t • pertV1 tD tH1 + t ^ 2 • pertV2 tD tH1 tH2) -
        (tD 0 + t * pertE1 tH1 + t ^ 2 * pertE2 tD tH1 tH2) •
          ((Pi.single 0 1 : Fin 3 → ℝ) + t • pertV1 tD tH1 + t ^ 2 • pertV2 tD tH1 tH2)) =
      -(17 / 4) * t ^ 3 - 3 * t ^ 4 := by
  rw [secondOrder_projected_residual tD tH1 tH2 tH1_isHermitian tD_gap t]
  exact test_secondOrder_projected_rhs t

#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.rayleighQuotient_eq_toEuclideanCLM_rayleighQuotient
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.rayleighQuotient_ge_eigenvalues_min
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.rayleighQuotient_le_eigenvalues_max
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.cauchyInterlacing_oneDim
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.generalizedEigenvalue_eq_ratio
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.firstOrder_residual
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.secondOrder_projected_residual
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_path_eigenvector
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_path_sineMode_ne_zero
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_path_eigenvalues_distinct
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_cycle_cosMode_ne_zero
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_cycle_eigenvector_cos
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_cycle_sinMode_mulVec
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.alternatingFlip_ne_zero
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.cycleAdjacency_flip
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_cycle_flip_mulVec
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_cycle_pairing
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.cycle_cos_pos_count_4m2
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.cycle_cos_zero_count_4m
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_cycle_closedForm_count_lt_alpha_4m2
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_cycle_closedForm_count_eq_alpha_4m
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.lcao_det
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.lcao_energies_are_roots

end PhyslibExtTest.Chemistry.VariationalPerturbationHuckel
