/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Ising.GKS
import Code.Lattice.HypercubicLattice
import Code.Percolation.Theta
import Code.Percolation.TildePc

open MeasureTheory
open scoped BigOperators NNReal
open Finset

namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising

variable {d : ℕ}










noncomputable def bondParam (β : ℝ) : ℝ≥0 := Real.toNNReal (1 - Real.exp (-β))



theorem bondParam_le_one (β : ℝ) : bondParam β ≤ 1 := by
  unfold bondParam
  rw [Real.toNNReal_le_one]
  have h1 : (0 : ℝ) < Real.exp (-β) := Real.exp_pos _
  linarith






noncomputable def phiBeta (d : ℕ) (β : ℝ) (S : Finset (Site d)) : ℝ :=
  Percolation.phi d (bondParam β) (bondParam_le_one β) S


theorem phiBeta_nonneg (d : ℕ) (β : ℝ) (S : Finset (Site d)) :
    0 ≤ phiBeta d β S :=
  Percolation.phi_nonneg d (bondParam β) (bondParam_le_one β) S



def tildeBetaCPercoSet (d : ℕ) : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ ∃ S : Finset (Site d), origin d ∈ S ∧ phiBeta d β S < 1}

@[simp]
theorem mem_tildeBetaCPercoSet {d : ℕ} {β : ℝ} :
    β ∈ tildeBetaCPercoSet d ↔
      0 ≤ β ∧ ∃ S : Finset (Site d), origin d ∈ S ∧ phiBeta d β S < 1 :=
  Iff.rfl




noncomputable def tildeBetaCPerco (d : ℕ) : ℝ :=
  sSup (tildeBetaCPercoSet d)










noncomputable def graphS (d : ℕ) (S : Finset (Site d)) : SimpleGraph {v // v ∈ S} :=
  (hypercubicLattice d).comap (fun v : {v // v ∈ S} => (v : Site d))

noncomputable instance instDecidableAdjGraphS (d : ℕ) (S : Finset (Site d)) :
    DecidableRel (graphS d S).Adj := by
  classical
  intro a b
  unfold graphS
  simp only [SimpleGraph.comap_adj]
  infer_instance





noncomputable def freeCorr (d : ℕ) (β : ℝ) (S : Finset (Site d))
    (a b : {v // v ∈ S}) : ℝ :=
  if a = b then 1 else
    isingExpectation (graphS d S) β 0 (spinProd {a, b})

@[simp]
theorem freeCorr_self (d : ℕ) (β : ℝ) (S : Finset (Site d))
    (a : {v // v ∈ S}) : freeCorr d β S a a = 1 := by
  simp [freeCorr]




theorem abs_freeCorr_le_one (d : ℕ) (β : ℝ) (S : Finset (Site d))
    (a b : {v // v ∈ S}) : |freeCorr d β S a b| ≤ 1 := by
  classical
  by_cases hab : a = b
  · simp [freeCorr, hab]
  rw [freeCorr, if_neg hab]
  unfold isingExpectation
  have hbound : ∀ s : ConfigSpace {v // v ∈ S}, |spinProd ({a, b} : Finset _) s| ≤ 1 := by
    intro s
    unfold spinProd
    rw [Finset.abs_prod]
    apply Finset.prod_le_one
    · intro x _; positivity
    · intro x _; exact abs_spin_le_one s x
  calc |∑ s : ConfigSpace {v // v ∈ S},
            isingProb (graphS d S) β 0 s * spinProd ({a, b} : Finset _) s|
      ≤ ∑ s : ConfigSpace {v // v ∈ S},
            |isingProb (graphS d S) β 0 s * spinProd ({a, b} : Finset _) s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : ConfigSpace {v // v ∈ S}, isingProb (graphS d S) β 0 s * 1 := by
        apply Finset.sum_le_sum
        intro s _
        rw [abs_mul, abs_of_nonneg (isingProb_nonneg (graphS d S) β 0 s)]
        exact mul_le_mul_of_nonneg_left (hbound s) (isingProb_nonneg (graphS d S) β 0 s)
    _ = ∑ s : ConfigSpace {v // v ∈ S}, isingProb (graphS d S) β 0 s := by simp
    _ = 1 := isingProb_sum_eq_one (graphS d S) β 0



theorem freeCorr_nonneg (d : ℕ) {β : ℝ} (hβ : 0 ≤ β) (S : Finset (Site d))
    (a b : {v // v ∈ S}) : 0 ≤ freeCorr d β S a b := by
  by_cases hab : a = b
  · simp [freeCorr, hab]
  rw [freeCorr, if_neg hab]
  exact gks_first (graphS d S) β 0 hβ le_rfl {a, b}






noncomputable def corrOriginInner (d : ℕ) (β : ℝ) (S : Finset (Site d))
    (x : Site d) : ℝ := by
  classical
  exact
    if h0 : origin d ∈ S then
      if hx : x ∈ S then
        freeCorr d β S ⟨origin d, h0⟩ ⟨x, hx⟩
      else 0
    else 0


theorem corrOriginInner_nonneg (d : ℕ) {β : ℝ} (hβ : 0 ≤ β) (S : Finset (Site d))
    (x : Site d) : 0 ≤ corrOriginInner d β S x := by
  classical
  unfold corrOriginInner
  split
  · split
    · exact freeCorr_nonneg d hβ S _ _
    · exact le_refl 0
  · exact le_refl 0






noncomputable def phiIsing (d : ℕ) (β : ℝ) (S : Finset (Site d)) : ℝ :=
  Real.tanh β * ∑ e ∈ Percolation.boundaryEdges d S, corrOriginInner d β S e.1



theorem phiIsing_nonneg (d : ℕ) {β : ℝ} (hβ : 0 ≤ β) (S : Finset (Site d)) :
    0 ≤ phiIsing d β S := by
  unfold phiIsing
  refine mul_nonneg ?_ (Finset.sum_nonneg ?_)
  · rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (Real.cosh_pos _).le
  · intro e _
    exact corrOriginInner_nonneg d hβ S e.1



def tildeBetaCIsingSet (d : ℕ) : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ ∃ S : Finset (Site d), origin d ∈ S ∧ phiIsing d β S < 1}

@[simp]
theorem mem_tildeBetaCIsingSet {d : ℕ} {β : ℝ} :
    β ∈ tildeBetaCIsingSet d ↔
      0 ≤ β ∧ ∃ S : Finset (Site d), origin d ∈ S ∧ phiIsing d β S < 1 :=
  Iff.rfl




noncomputable def tildeBetaCIsing (d : ℕ) : ℝ :=
  sSup (tildeBetaCIsingSet d)

end Sharpness

end StatMech
