/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.EsCorrelations

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.EsCorrelations`

On the one-edge graph `⊤ : SimpleGraph (Fin 2)`:
* `isingSpin` maps the colors `0, 1` to `1, -1`;
* `Connected` holds for `0, 1` when the edge is open and fails when every edge is closed;
* `connProb` is `1` on the diagonal and positive off it (at `p = 1/2`, `q = 2`);
* `esTwoPoint_eq_connProb`: the Ising two-point function `⟨σ₀ σ₁⟩` equals `φ_{p,2}(0 ↔ 1)`, so it
  is positive at `p = 1/2`;
* `one_le_numClusters` on `⊤`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.EsCorrelations

open _root_.StatMech _root_.StatMech.FK

/-- The configuration with every coordinate open. -/
def allOpen : ConfigSpace (Sym2 (Fin 2)) := fun _ => true

/-- The configuration with every coordinate closed. -/
def allClosed : ConfigSpace (Sym2 (Fin 2)) := fun _ => false

-- The Ising spin values of the two colors.
example : isingSpin 0 = 1 ∧ isingSpin 1 = -1 := by norm_num [isingSpin]

/-- With every edge open, `0` and `1` are connected. -/
theorem connected_allOpen : Connected (⊤ : SimpleGraph (Fin 2)) allOpen 0 1 :=
  SimpleGraph.Adj.reachable (by simp [allOpen])

-- With every edge closed, `0` and `1` are not connected.
example : ¬ Connected (⊤ : SimpleGraph (Fin 2)) allClosed 0 1 := by
  intro h
  obtain ⟨w⟩ := h
  cases w with
  | cons hadj _ => simp [allClosed] at hadj

/-- The connection probability of `0` and `1` at `p = 1/2`, `q = 2` is positive. -/
theorem connProb_pos : 0 < connProb (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 0 1 := by
  unfold connProb
  refine lt_of_lt_of_le
    (fkProb_pos (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
      (by norm_num) allOpen) ?_
  exact Finset.single_le_sum
    (fun ω _ => fkProb_nonneg (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2) (by norm_num)
      (by norm_num) (by norm_num) ω)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, connected_allOpen⟩)

-- On the diagonal the connection probability is `1`.
example (x : Fin 2) : connProb (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 x x = 1 := by
  have h : ∀ ω, Connected (⊤ : SimpleGraph (Fin 2)) ω x x := fun _ => SimpleGraph.Reachable.refl x
  simpa [connProb, h] using
    fkProb_sum_eq_one (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
      (by norm_num)

-- The Ising two-point function is the `q = 2` connection probability, hence positive.
example : 0 < esTwoPoint (⊤ : SimpleGraph (Fin 2)) (1 / 2) 0 1 := by
  rw [esTwoPoint_eq_connProb]
  exact connProb_pos

-- Every configuration has at least one cluster.
example (ω : ConfigSpace (Sym2 (Fin 2))) : 1 ≤ numClusters (⊤ : SimpleGraph (Fin 2)) ω :=
  one_le_numClusters _ ω 0

end PhyslibExtTest.StatisticalMechanics.RandomCluster.EsCorrelations
