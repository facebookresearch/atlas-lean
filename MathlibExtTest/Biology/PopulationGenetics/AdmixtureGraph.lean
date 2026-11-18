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

/-- On a tree, the root-relative second moment is the shared lineage length. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (M : DriftModel μ T.Edge (Fin 3))
    (hM : M.weight = T.weight) (X Y : Fin 3) :
    M.rootSecondMoment X Y = ∑ e ∈ M.lineage X ∩ M.lineage Y, M.len e :=
  T.rootSecondMoment_eq_sum_inter_of_isTree T_isTree hM X Y

#print axioms AdmixtureGraph.rootSecondMoment_eq_sum_inter_of_isTree

/-! ### Admixture f3 with complementary proportions -/

namespace AdmixtureF3Check


def exParents : Fin 5 → Finset (Fin 5)
  | 0 => ∅
  | 1 => {0}
  | 2 => {0}
  | 3 => {1, 2}
  | 4 => {3}

noncomputable def exProp (α : ℝ) : Fin 5 → Fin 5 → ℝ
  | 1, 0 => 1
  | 2, 0 => 1
  | 3, 1 => α
  | 3, 2 => 1 - α
  | 4, 3 => 1
  | _, _ => 0

theorem exParents_lt : ∀ X Y : Fin 5, Y ∈ exParents X → Y < X := by decide

noncomputable def exGraph (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) : AdmixtureGraph (Fin 5) where
  root := 0
  parents := exParents
  prop := exProp α
  parents_root := rfl
  card_parents := by decide
  prop_nonneg := by
    intro X Y
    fin_cases X <;> fin_cases Y <;> simp [exProp] <;> linarith
  prop_eq_zero := by
    intro X Y hY
    fin_cases X <;> fin_cases Y <;> simp_all [exParents, exProp]
  sum_prop := by
    intro X hX
    fin_cases X <;> simp_all [exParents, exProp]
  wf := Subrelation.wf (fun {Y X} h => exParents_lt X Y h) (InvImage.wf (fun x : Fin 5 => x.val)
    Nat.lt_wfRel.wf)

variable (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)

theorem ex_parents_X : (exGraph α h0 h1).parents 3 = {1, 2} := rfl
theorem ex_parents_Y : (exGraph α h0 h1).parents 4 = {3} := rfl
theorem ex_AB : (1 : Fin 5) ≠ 2 := by decide

/-- The complementary-proportion lemma evaluated: `prop X B = 1 - α`. -/
example : (exGraph α h0 h1).prop 3 2 = 1 - (exGraph α h0 h1).prop 3 1 :=
  (exGraph α h0 h1).prop_eq_one_sub_of_parents_eq_pair (ex_parents_X α h0 h1) ex_AB

/-- A drift model with the graph's weights exists (zero increments; any square-integrable,
pairwise-uncorrelated increments would do), so the hypotheses `hM`, `hX`, `hAB`, `hY` of every
Part 2 theorem are simultaneously satisfiable, including at the endpoints `α = 0`, `α = 1`. -/
noncomputable def exModel : DriftModel (Measure.dirac ()) (exGraph α h0 h1).Edge (Fin 5) :=
  (exGraph α h0 h1).driftModel (fun _ => 1 / 2) (fun _ _ => 0) (memLp_const _)
    (fun _ => memLp_const _) (fun _ _ _ => by simp)

example : f3 (Measure.dirac ()) (exModel α h0 h1).freq 4 1 2 =
    α ^ 2 * (exModel α h0 h1).len ⟨(3, 1), by simp [exGraph, exParents]⟩ +
      (1 - α) ^ 2 * (exModel α h0 h1).len ⟨(3, 2), by simp [exGraph, exParents]⟩ -
      α * (1 - α) * f2 (Measure.dirac ()) (exModel α h0 h1).freq 1 2 +
      (exModel α h0 h1).len ⟨(4, 3), by simp [exGraph, exParents]⟩ :=
  (exGraph α h0 h1).f3_admixture_of_parents_eq_singleton rfl (ex_parents_Y α h0 h1)
    (ex_parents_X α h0 h1) ex_AB

/-- Endpoint instances: the `α = 1` and `α = 0` graphs satisfy the endpoint hypotheses. -/
example : f3 (Measure.dirac ()) (exModel 1 zero_le_one le_rfl).freq 3 1 2 =
    (exModel 1 zero_le_one le_rfl).len ⟨(3, 1), by simp [exGraph, exParents]⟩ :=
  (exGraph 1 zero_le_one le_rfl).f3_admixture_of_prop_eq_one rfl rfl ex_AB rfl

example : f3 (Measure.dirac ()) (exModel 0 le_rfl zero_le_one).freq 3 1 2 =
    (exModel 0 le_rfl zero_le_one).len ⟨(3, 2), by simp [exGraph, exParents]⟩ :=
  (exGraph 0 le_rfl zero_le_one).f3_admixture_of_prop_eq_zero rfl rfl ex_AB rfl


end AdmixtureF3Check

#print axioms AdmixtureGraph.prop_eq_one_sub_of_parents_eq_pair
#print axioms AdmixtureGraph.f3_admixture_one_sub
#print axioms AdmixtureGraph.f3_admixture_of_prop_eq_one
#print axioms AdmixtureGraph.f3_of_parents_eq_singleton

end MathlibExtTest.Biology.PopulationGenetics.AdmixtureGraph
