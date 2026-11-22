/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.IsingFKGLayer

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.IsingFKGLayer`

On the single edge `⊤ : SimpleGraph (Fin 2)`:
* the spin observables `s ↦ σ_x` are monotone, so they are admissible in the FKG inequality;
* `ifk_isingProb_positively_associated` at `β = 1` and negative field `h = -1` (outside the range
  of GKS) gives `⟨σ_0⟩ ⟨σ_1⟩ ≤ ⟨σ_0 σ_1⟩`;
* the event form `ifk_isingProb_positively_associated_events` applies to the increasing events
  "site `0` is plus" and "site `1` is plus";
* the hypothesis `0 ≤ β` cannot be dropped: at `β = -1`, `h = 0` the two spins are negatively
  correlated, by an explicit computation over the four configurations.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.IsingFKGLayer

open _root_.StatMech _root_.StatMech.Ising

/-- The single edge, the complete graph on two vertices. -/
abbrev edge : SimpleGraph (Fin 2) := ⊤

/-- The edge set of the single edge is `{s(0, 1)}`. -/
lemma edgeFinset_edge : edge.edgeFinset = {s(0, 1)} := by
  decide

/-- A sum over the four configurations on two sites, written out. -/
lemma sum_config_two (f : ConfigSpace (Fin 2) → ℝ) :
    ∑ s, f s = f ![true, true] + f ![true, false] + f ![false, true] + f ![false, false] := by
  rw [← Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Bool)).symm f, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, piFinTwoEquiv_symm_apply]
  rw [← add_assoc]
  rfl

/-- The spin at a site is a monotone observable. -/
lemma monotone_spin (x : Fin 2) : Monotone (fun s : ConfigSpace (Fin 2) => spin s x) :=
  fun _ _ hab => ifk_spin_mono hab x

-- FKG at negative field: `⟨σ_0⟩ ⟨σ_1⟩ ≤ ⟨σ_0 σ_1⟩` for `β = 1`, `h = -1`.
example : (∑ s, isingProb edge 1 (-1) s * spin s 0) * (∑ s, isingProb edge 1 (-1) s * spin s 1)
    ≤ ∑ s, isingProb edge 1 (-1) s * (spin s 0 * spin s 1) :=
  ifk_isingProb_positively_associated edge zero_le_one (-1) (monotone_spin 0) (monotone_spin 1)

/-- The event "site `x` is plus" is increasing. -/
lemma isIncreasing_plusAt (x : Fin 2) : IsIncreasing {s : ConfigSpace (Fin 2) | s x = true} := by
  intro a b hab ha
  have h := hab x
  simp only [Set.mem_ofPred_eq] at ha ⊢
  rw [ha] at h
  exact top_le_iff.mp h

-- The event form of FKG for "site `0` is plus" and "site `1` is plus".
example : (∑ s, isingProb edge 2 (-3) s * {s : ConfigSpace (Fin 2) | s 0 = true}.indicator
        (fun _ => (1 : ℝ)) s)
      * (∑ s, isingProb edge 2 (-3) s * {s : ConfigSpace (Fin 2) | s 1 = true}.indicator
        (fun _ => (1 : ℝ)) s)
    ≤ ∑ s, isingProb edge 2 (-3) s * ({s : ConfigSpace (Fin 2) | s 0 = true}
        ∩ {s | s 1 = true}).indicator (fun _ => (1 : ℝ)) s :=
  ifk_isingProb_positively_associated_events edge (by norm_num) (-3)
    (isIncreasing_plusAt 0) (isIncreasing_plusAt 1)

-- Without `0 ≤ β` the FKG conclusion fails: at `β = -1`, `h = 0`.
example : ¬ (∑ s, isingProb edge (-1) 0 s * spin s 0) * (∑ s, isingProb edge (-1) 0 s * spin s 1)
    ≤ ∑ s, isingProb edge (-1) 0 s * (spin s 0 * spin s 1) := by
  simp only [isingProb, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [sum_config_two, sum_config_two, sum_config_two]
  simp only [isingWeight, hamiltonian, edgeFinset_edge, Finset.sum_singleton, bond_mk]
  simp [spin]
  have hZ := isingZ_pos edge (-1) 0
  have := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 1 by norm_num)
  apply div_neg_of_neg_of_pos _ hZ
  linarith

end PhyslibExtTest.CondensedMatter.IsingModel.IsingFKGLayer
