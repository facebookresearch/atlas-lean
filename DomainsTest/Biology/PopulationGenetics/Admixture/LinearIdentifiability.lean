/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Admixture.LinearIdentifiability

/-!
# Tests for linear identifiability of edge lengths

The examples check a graph with more edges than `n choose 2`, a full-rank tree, the
one-population and no-edge endpoints, and the positive-orthant construction.
-/

@[expose] public section

open MeasureTheory Matrix MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.QpGraph

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.LinearIdentifiability

open MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel
open MathlibExt.Biology.PopulationGenetics.QpGraph

/-- Acceptance 1: `E > n choose 2`. Two populations hanging from the root on their own edges:
`2` edges, `2 choose 2 = 1` statistic. -/
noncomputable def wTwo : Fin 2 → Fin 2 → ℝ := fun X e => if e = X then 1 else 0

example : ¬ Function.Injective
    (designMatrix wTwo (fun _ : Unit => 0) (fun _ => 1) (fun _ => 0) (fun _ => 1)).mulVec :=
  not_injective_of_choose_two_lt wTwo (by decide) _ _ _ _

/-- Concretely: lengths `(1, 2)` and `(2, 1)` give the same `f2 = 3` (only the root-to-root
path length is seen). -/
example : f2 Measure.count (ofLen wTwo ![1, 2] (by intro e; fin_cases e <;> norm_num)).freq 0 1 =
    f2 Measure.count (ofLen wTwo ![2, 1] (by intro e; fin_cases e <;> norm_num)).freq 0 1 := by
  rw [f2_freq, f2_freq]
  simp [ofLen, wTwo, Fin.sum_univ_two]
  norm_num

/-- Acceptance 2: a full-rank (Buneman-consistent) tree. The unrooted 4-leaf tree
`((A, B), (C, D))`, rooted at the internal node `u`, edges `0 = uA`, `1 = uB`, `2 = uv`,
`3 = vC`, `4 = vD`; basis: the six `f2` pairs. `5 ≤ 6`, and the design has full column rank. -/
def linTree : Fin 4 → Finset (Fin 5) := ![{0}, {1}, {2, 3}, {2, 4}]

noncomputable def wTree : Fin 4 → Fin 5 → ℝ := fun X e => if e ∈ linTree X then 1 else 0

def pairA : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
def pairB : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

theorem tree_injective :
    Function.Injective (designMatrix wTree pairA pairB pairA pairB).mulVec := by
  intro x y hxy
  have h := fun i => congrFun hxy i
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  simp [designMatrix, mulVec, dotProduct, wTree, linTree, pairA, pairB, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5
  funext e
  fin_cases e <;> simp <;> linarith

theorem tree_rank : (designMatrix wTree pairA pairB pairA pairB).rank = 5 := by
  have h : Function.Injective (designMatrix wTree pairA pairB pairA pairB).mulVec ↔
      (designMatrix wTree pairA pairB pairA pairB).rank = Fintype.card (Fin 5) := by
    rw [Matrix.mulVec_injective_iff, Matrix.rank_eq_finrank_span_cols,
      linearIndependent_iff_card_eq_finrank_span, Set.finrank]
    exact eq_comm
  exact (h.mp tree_injective).trans (Fintype.card_fin 5)

/-- Endpoint: one population (`1 choose 2 = 0`) and one edge: never identifiable. -/
example : ¬ Function.Injective
    (designMatrix (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) (fun _ : Unit => ()) (fun _ => ())
      (fun _ => ()) (fun _ => ())).mulVec :=
  not_injective_of_choose_two_lt _ (by decide) _ _ _ _

/-- Endpoint: no edges (rank zero): trivially identifiable. -/
example {ι P : Type*} (w : P → Empty → ℝ) (A B C D : ι → P) :
    Function.Injective (designMatrix w A B C D).mulVec :=
  fun _ _ _ => funext fun e => e.elim

/-- Positive-orthant statement on the two-edge example: a concrete second positive length vector
exists for `(1, 2)`. -/
example : ∃ M' : DriftModel (Measure.count : Measure (Fin 2)) (Fin 2) (Fin 2),
    M'.weight = wTwo ∧ (∀ e, 0 < M'.len e) ∧
      M'.len ≠ ![1, 2] ∧ ∀ A B C D : Fin 2, f4 Measure.count M'.freq A B C D =
        f4 Measure.count (ofLen wTwo ![1, 2] (by intro e; fin_cases e <;> norm_num)).freq A B C D :=
  exists_driftModel_pos_len_ne (ofLen wTwo ![1, 2] (by intro e; fin_cases e <;> norm_num))
    (by decide) (by intro e; fin_cases e <;> simp [ofLen])


#print axioms MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel.ofLen
#print axioms MathlibExt.Biology.PopulationGenetics.QpGraph.len_identifiable_iff_rank_eq_card
#print axioms MathlibExt.Biology.PopulationGenetics.QpGraph.exists_driftModel_pos_len_ne

end MathlibExtTest.Biology.PopulationGenetics.Admixture.LinearIdentifiability
