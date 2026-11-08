/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.GKS

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.GKS`

On the single edge `⊤ : SimpleGraph (Fin 2)`:
* `spinProd` of the empty set is `1`, and `spinProd {0, 1}` is the bond variable;
* `gks_first` applies at `β = 1`, `h = 0` and gives `0 ≤ ⟨σ_0 σ_1⟩`;
* the hypothesis `0 ≤ β` cannot be dropped: at `β = -1`, `h = 0` (antiferromagnet) the nearest
  neighbour correlation `⟨σ_0 σ_1⟩` is negative, computed from the four configurations;
* `isingExpectation` of the constant observable `1` is `1`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.GKS

open _root_.StatMech _root_.StatMech.Ising

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

-- The empty spin product is `1`.
example (s : ConfigSpace (Fin 2)) : spinProd (∅ : Finset (Fin 2)) s = 1 := by simp

-- The spin product over both sites is the bond variable of the edge.
example (s : ConfigSpace (Fin 2)) : spinProd ({0, 1} : Finset (Fin 2)) s = bond s s(0, 1) := by
  simp [spinProd]

-- The expectation of the constant observable `1` is `1`.
example (β h : ℝ) : isingExpectation edge β h (fun _ => 1) = 1 := by
  simp [isingExpectation, isingProb_sum_eq_one]

-- GKS I at `β = 1`, `h = 0`: the nearest-neighbour correlation is nonnegative.
example : 0 ≤ isingExpectation edge 1 0 (spinProd {0, 1}) :=
  gks_first edge 1 0 zero_le_one le_rfl {0, 1}

-- GKS I for every subset at once, on the single edge with a positive field.
example (A : Finset (Fin 2)) : 0 ≤ isingExpectation edge 2 (1 / 2) (spinProd A) :=
  gks_first edge 2 (1 / 2) (by norm_num) (by norm_num) A

-- The hypothesis `0 ≤ β` is needed: at `β = -1`, `⟨σ_0 σ_1⟩ < 0`.
example : isingExpectation edge (-1) 0 (spinProd {0, 1}) < 0 := by
  unfold isingExpectation isingProb
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  apply div_neg_of_neg_of_pos _ (isingZ_pos edge (-1) 0)
  rw [sum_config_two]
  simp only [isingWeight, hamiltonian, edgeFinset_edge, Finset.sum_singleton, bond_mk,
    spinProd, spin]
  simp
  have := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 1 by norm_num)
  linarith

end PhyslibExtTest.CondensedMatter.IsingModel.GKS
