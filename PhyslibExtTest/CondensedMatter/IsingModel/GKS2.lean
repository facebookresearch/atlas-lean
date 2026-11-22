/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.GKS2

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.GKS2`

On the single edge `⊤ : SimpleGraph (Fin 2)`:
* `gks_second` applies at `β = 1`, `h = 0` with `A = {0}`, `B = {1}` and gives
  `⟨σ_0⟩ ⟨σ_1⟩ ≤ ⟨σ_0 σ_1⟩`;
* the symmetric difference in the conclusion: `{0} ∆ {0, 1} = {1}`;
* the hypothesis `0 ≤ β` cannot be dropped: at `β = -1`, `h = 0` the one-point functions vanish by
  spin-flip symmetry while `⟨σ_0 σ_1⟩ < 0`, so the conclusion of GKS II fails.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.GKS2

open _root_.StatMech _root_.StatMech.Ising
open scoped symmDiff

/-- The single edge, the complete graph on two vertices. -/
abbrev edge : SimpleGraph (Fin 2) := ⊤

/-- A sum over the four configurations on two sites, written out. -/
lemma sum_config_two (f : ConfigSpace (Fin 2) → ℝ) :
    ∑ s, f s = f ![true, true] + f ![true, false] + f ![false, true] + f ![false, false] := by
  rw [← Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Bool)).symm f, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, piFinTwoEquiv_symm_apply]
  rw [← add_assoc]
  rfl

/-- The edge set of the single edge is `{s(0, 1)}`. -/
lemma edgeFinset_edge : edge.edgeFinset = {s(0, 1)} := by
  decide

-- GKS II at `β = 1`, `h = 0`, `A = {0}`, `B = {1}`.
example : isingExpectation edge 1 0 (spinProd {0}) * isingExpectation edge 1 0 (spinProd {1})
    ≤ isingExpectation edge 1 0 (spinProd ({0} ∆ {1})) :=
  gks_second edge 1 0 zero_le_one le_rfl {0} {1}

-- The symmetric difference in GKS II: `{0} ∆ {0, 1} = {1}`, so GKS II bounds `⟨σ_0⟩ ⟨σ_0 σ_1⟩`
-- by `⟨σ_1⟩`.
example : isingExpectation edge 1 1 (spinProd {0}) * isingExpectation edge 1 1 (spinProd {0, 1})
    ≤ isingExpectation edge 1 1 (spinProd {1}) := by
  have h := gks_second edge 1 1 zero_le_one zero_le_one {0} {0, 1}
  have hs : ({0} : Finset (Fin 2)) ∆ {0, 1} = {1} := by decide
  rwa [hs] at h

/-- At zero field the one-point function vanishes, for any `β`, by spin-flip symmetry. -/
lemma isingExpectation_spin_zero (β : ℝ) (i : Fin 2) :
    isingExpectation edge β 0 (spinProd {i}) = 0 := by
  unfold isingExpectation isingProb
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [sum_config_two]
  rw [div_eq_zero_iff]
  left
  simp only [isingWeight, hamiltonian, edgeFinset_edge, Finset.sum_singleton, bond_mk]
  fin_cases i <;> simp [spinProd, spin]

-- Without `0 ≤ β` GKS II fails: at `β = -1`, `h = 0`, `⟨σ_0⟩ ⟨σ_1⟩ = 0 > ⟨σ_0 σ_1⟩`.
example : ¬ isingExpectation edge (-1) 0 (spinProd {0}) * isingExpectation edge (-1) 0 (spinProd {1})
    ≤ isingExpectation edge (-1) 0 (spinProd ({0} ∆ {1})) := by
  have hs : ({0} : Finset (Fin 2)) ∆ {1} = {0, 1} := by decide
  rw [hs, isingExpectation_spin_zero, isingExpectation_spin_zero, mul_zero, not_le]
  unfold isingExpectation isingProb
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  apply div_neg_of_neg_of_pos _ (isingZ_pos edge (-1) 0)
  rw [sum_config_two]
  simp only [isingWeight, hamiltonian, edgeFinset_edge, Finset.sum_singleton, bond_mk,
    spinProd, spin]
  simp
  have := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 1 by norm_num)
  linarith

end PhyslibExtTest.CondensedMatter.IsingModel.GKS2
