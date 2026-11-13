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

theorem test_cycle_pairing_N4 (v : Fin (1 + 3) → ℝ) (hEv : huckelMatrix (0 : ℝ) 1 (SimpleGraph.cycleGraph (1 + 3)) *ᵥ v = (-2 : ℝ) • v) : huckelMatrix (0 : ℝ) 1 (SimpleGraph.cycleGraph (1 + 3)) *ᵥ alternatingFlip v = (2 * (0 : ℝ) - (-2)) • alternatingFlip v := by
  have hN : Even (1 + 3) := ⟨2, by norm_num⟩
  exact huckel_cycle_pairing hN 0 1 hEv

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

theorem test_bonding_count : (Finset.univ.filter (fun k : Fin (4 * 1 + 2) => (0 : ℝ) + 2 * (-1) * Real.cos (2 * Real.pi * k.val / (4 * 1 + 2)) < 0)).card = 3 := by
  have h := huckel_bonding_count_4m2 1 (0 : ℝ) (β := (-1 : ℝ)) (by norm_num)
  norm_num at h ⊢
  exact h

theorem test_degen_count : (Finset.univ.filter (fun k : Fin (4 * 1) => (0 : ℝ) + 2 * (-1) * Real.cos (2 * Real.pi * k.val / (4 * 1)) = 0)).card = 2 := by
  have h := huckel_degenerate_count_4m (m := 1) (by norm_num) 0 (-1) (by norm_num)
  norm_num at h ⊢
  exact h

#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.rayleighQuotient_ge_eigenvalues_min
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.rayleighQuotient_le_eigenvalues_max
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.cauchyInterlacing_oneDim
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.generalizedEigenvalue_eq_ratio
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.firstOrder_residual
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.secondOrder_projected_residual
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_path_eigenvector
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_path_eigenvalues_distinct
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_cycle_eigenvector_cos
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_cycle_eigenvector_sin
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.cycleAdjacency_flip
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_cycle_pairing
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.cycle_cos_pos_count_4m2
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.cycle_cos_zero_count_4m
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_bonding_count_4m2
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.huckel_degenerate_count_4m
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.lcao_det
#print axioms PhyslibExt.Chemistry.VariationalPerturbationHuckel.lcao_energies_are_roots

end PhyslibExtTest.Chemistry.VariationalPerturbationHuckel
