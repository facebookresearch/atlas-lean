/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Ising.HdomNativeWeight
import Code.Ising.TwoCurrentProbBound
import Code.Ising.EnsembleGHS

open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
















noncomputable def gc5_ensembleUrsell (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) (o x y : V) : ℝ :=
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y



theorem gc5_ensembleUrsell_eq_egh (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) (o x y : V) :
    gc5_ensembleUrsell G β J M B o x y = egh_ensembleUrsell G β J M B o x y := rfl





















theorem gc5_three_pairings_collapse (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (B : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hall : hnw_allConn G m o x y) :
    hnw_mass G β J m (B ∆ {x, y}) = hnw_mass G β J m B
      ∧ hnw_mass G β J m (B ∆ {o, y}) = hnw_mass G β J m B
      ∧ hnw_mass G β J m (B ∆ {o, x}) = hnw_mass G β J m B :=
  hnw_allMass_eq_paired G β J m B hox hoy hxy hall










theorem gc5_gap_allConn_eq (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (B : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hall : hnw_allConn G m o x y) :
    hnw_gap G β J m B o x y = -2 * hnw_mass G β J m B := by
  obtain ⟨e1, e2, e3⟩ := gc5_three_pairings_collapse G β J m B hox hoy hxy hall
  unfold hnw_gap
  rw [e1, e2, e3]; ring





















theorem gc5_ensemble_ursell_eq (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V)) (B : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc5_ensembleUrsell G β J M B o x y = -2 * tcp_allConnMass G β J M B o x y := by
  unfold gc5_ensembleUrsell tcp_allConnMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hmem => ?_)
  rw [Finset.mem_filter] at hmem
  exact gc5_gap_allConn_eq G β J m B hox hoy hxy hmem.2










theorem gc5_ensembleUrsell_eq_neg_two_mul (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y)
      = -2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B) :=
  gc5_ensemble_ursell_eq G β J M B hox hoy hxy






theorem gc5_ensemble_ursell_eq_agrees (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc5_ensembleUrsell G β J M B o x y = egh_ensembleUrsell G β J M B o x y
      ∧ gc5_ensembleUrsell G β J M B o x y = -2 * tcp_allConnMass G β J M B o x y :=
  ⟨gc5_ensembleUrsell_eq_egh G β J M B o x y,
   gc5_ensemble_ursell_eq G β J M B hox hoy hxy⟩













theorem gc5_ensemble_ursell_sign (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y)
    (hxy : x ≠ y) :
    gc5_ensembleUrsell G β J M B o x y ≤ 0 := by
  rw [gc5_ensemble_ursell_eq G β J M B hox hoy hxy]
  have := tcp_allConnMass_nonneg G β J hβ hJ M B o x y
  linarith








theorem gc5_ursell_empty (β : ℝ) (J : Sym2 V → ℝ) (B : Finset V) (o x y : V) :
    gc5_ensembleUrsell G β J (∅ : Finset (Current V)) B o x y = 0 := by
  unfold gc5_ensembleUrsell
  simp









theorem gc5_ursell_single_allConn (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (B : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hall : hnw_allConn G m o x y) :
    gc5_ensembleUrsell G β J ({m} : Finset (Current V)) B o x y = -2 * hnw_mass G β J m B := by
  unfold gc5_ensembleUrsell
  rw [Finset.filter_singleton, if_pos hall, Finset.sum_singleton]
  exact gc5_gap_allConn_eq G β J m B hox hoy hxy hall





theorem gc5_ursell_single_noneConn (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (B : Finset V)
    (o x y : V) (hnall : ¬ hnw_allConn G m o x y) :
    gc5_ensembleUrsell G β J ({m} : Finset (Current V)) B o x y = 0 := by
  unfold gc5_ensembleUrsell
  rw [Finset.filter_singleton, if_neg hnall, Finset.sum_empty]

end StatMech.Walls
