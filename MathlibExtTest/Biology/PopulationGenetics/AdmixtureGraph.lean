/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.AdmixtureGraph

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics
open MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExtTest.Biology.PopulationGenetics.AdmixtureGraph

/-! ### A non-vacuous admixture graph

Root `0`; populations `1` and `2` descend from the root; population `3` is an admixture node
with parents `1` (proportion `1/3`) and `2` (proportion `2/3`). -/

/-- Parent sets of the witness graph. -/
def par : Fin 4 → Finset (Fin 4) := ![∅, {0}, {0}, {1, 2}]

/-- Admixture proportions of the witness graph. -/
noncomputable def pr : Fin 4 → Fin 4 → ℝ :=
  ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 1/3, 2/3, 0]]

/-- The witness admixture graph. -/
noncomputable def G : AdmixtureGraph (Fin 4) where
  root := 0
  parents := par
  prop := pr
  parents_root := rfl
  card_parents := by decide
  prop_nonneg := by
    intro X Y
    fin_cases X <;> fin_cases Y <;> norm_num [pr]
  prop_eq_zero := by
    intro X Y h
    fin_cases X <;> fin_cases Y <;> simp_all [par, pr]
  sum_prop := by
    intro X hX
    fin_cases X <;> simp_all [par, pr]
    norm_num
  wf := Subrelation.wf (r := fun Y X : Fin 4 => (Y : ℕ) < X)
    (fun {Y X} h => by fin_cases X <;> fin_cases Y <;> simp_all [par])
    (measure fun x : Fin 4 => (x : ℕ)).wf

/-- The root's lineage visits no other node. -/
theorem visit_0_1 : G.visit 0 1 = 0 := by
  rw [G.visit_eq]
  simp [G, par]

/-- The lineage of `2` does not pass through its sibling `1`. -/
theorem visit_2_1 : G.visit 2 1 = 0 := by
  rw [G.visit_eq]
  simpa [G, par, pr] using visit_0_1

/-- The admixed lineage passes through population `1` with probability `1/3`. -/
theorem visit_3_1 : G.visit 3 1 = 1 / 3 := by
  rw [G.visit_eq, show G.parents 3 = {1, 2} from rfl, Finset.sum_pair (by decide),
    G.visit_self, visit_2_1]
  simp [G, pr]

/-- The edge `(1, 0)` is traversed by the admixed lineage with probability `1/3`. -/
example : G.weight 3 ⟨(1, 0), by simp [G, par]⟩ = 1 / 3 := by
  rw [AdmixtureGraph.weight, visit_3_1]
  simp [G, pr]

/-- Every lineage reaches the root. -/
example : G.visit 3 0 = 1 := G.visit_root 3

/-- The recursion at the admixture node. -/
example : G.weight 3 = G.prop 3 1 • G.weight 1 + (1 - G.prop 3 1) • G.weight 2 +
    fun e => if e.1.1 = 3 then G.prop 3 e.1.2 else 0 :=
  G.weight_admixture (X := 3) rfl (by decide)

/-- The graph is not a tree. -/
example : ¬ G.IsTree := fun h => by simpa [G, par] using h 3

/-- Every graph induces a drift model; here with zero increments. -/
noncomputable def M0 : DriftModel (Measure.dirac ()) G.Edge (Fin 4) :=
  G.driftModel (fun _ => 1 / 2) (fun _ _ => 0) MemLp.of_discrete (fun _ => MemLp.of_discrete)
    (fun _ _ _ => by simp)

example : M0.weight = G.weight := rfl

/-- With no drift on the admixture edges, `f3 3 1 2 = -(1/3) (2/3) f2 1 2`. -/
example : f3 (Measure.dirac ()) M0.freq 3 1 2 =
    -(G.prop 3 1 * (1 - G.prop 3 1)) * f2 (Measure.dirac ()) M0.freq 1 2 :=
  G.f3_admixture_of_len_eq_zero rfl (X := 3) rfl (by decide)
    (by simp [M0, AdmixtureGraph.driftModel]) (by simp [M0, AdmixtureGraph.driftModel])

/-! ### A tree -/

/-- Parent sets of a three-node tree: `1` and `2` descend from the root `0`. -/
def parT : Fin 3 → Finset (Fin 3) := ![∅, {0}, {0}]

/-- The tree as an admixture graph (all proportions `1`). -/
noncomputable def T : AdmixtureGraph (Fin 3) where
  root := 0
  parents := parT
  prop := fun X Y => if Y ∈ parT X then 1 else 0
  parents_root := rfl
  card_parents := by decide
  prop_nonneg := fun _ _ => by split_ifs <;> norm_num
  prop_eq_zero := fun _ _ h => ite_eq_right h
  sum_prop := by
    intro X hX
    fin_cases X <;> simp_all [parT]
  wf := Subrelation.wf (r := fun Y X : Fin 3 => (Y : ℕ) < X)
    (fun {Y X} h => by fin_cases X <;> fin_cases Y <;> simp_all [parT])
    (measure fun x : Fin 3 => (x : ℕ)).wf

theorem T_isTree : T.IsTree := by
  intro X
  fin_cases X <;> simp [T, parT]

/-- On a tree weights are `0` or `1`, the induced drift model has binary loadings, and
`f3 ≥ 0`. -/
example (X : Fin 3) (e : T.Edge) : T.weight X e = 0 ∨ T.weight X e = 1 :=
  T.weight_eq_zero_or_one T_isTree X e

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (M : DriftModel μ T.Edge (Fin 3))
    (hM : M.weight = T.weight) : M.HasBinaryLoadings :=
  T.hasBinaryLoadings_of_isTree T_isTree hM

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (M : DriftModel μ T.Edge (Fin 3))
    (hM : M.weight = T.weight) : 0 ≤ f3 μ M.freq 1 2 0 :=
  T.f3_nonneg_of_isTree T_isTree hM 1 2 0

/-- Boundary case: the root's lineage traverses no edge. -/
example (e : T.Edge) : T.weight 0 e = 0 := by
  obtain ⟨⟨c, p⟩, hp⟩ := e
  fin_cases c
  · simp [T, parT] at hp
  all_goals
    rw [AdmixtureGraph.weight, T.visit_eq]
    simp [T, parT]

end MathlibExtTest.Biology.PopulationGenetics.AdmixtureGraph
