/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Admixture.TreeFourPoint
public import Domains.Biology.PopulationGenetics.Admixture.ConditionalNegDef

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics
open MathlibExt.Biology.PopulationGenetics.FStatistics MathlibExt.Biology.Phylogenetics.Buneman

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.TreeFourPoint

/-! ### A tree with an internal edge

Root `0` with children `1` and `2`; node `1` has children `3` and `4`. The quartet
`3, 4, 2, 0` has the split `34 | 20` with internal edge `(1, 0)`. -/

/-- Parent sets of the tree. -/
def par : Fin 5 → Finset (Fin 5) := ![∅, {0}, {0}, {1}, {1}]

/-- The tree as an admixture graph (all proportions `1`). -/
noncomputable def T : AdmixtureGraph (Fin 5) where
  root := 0
  parents := par
  prop := fun X Y => if Y ∈ par X then 1 else 0
  parents_root := rfl
  card_parents := by decide
  prop_nonneg := fun _ _ => by split_ifs <;> norm_num
  prop_eq_zero := fun _ _ h => ite_eq_right h
  sum_prop := by
    intro X hX
    fin_cases X <;> simp_all [par]
  wf := Subrelation.wf (r := fun Y X : Fin 5 => (Y : ℕ) < X)
    (fun {Y X} h => by fin_cases X <;> fin_cases Y <;> simp_all [par])
    (measure fun x : Fin 5 => (x : ℕ)).wf

theorem T_isTree : T.IsTree := by
  intro X
  fin_cases X <;> simp [T, par]

/-- The edge `(3, 1)`. -/
def e31 : T.Edge := ⟨(3, 1), by simp [T, par]⟩

/-- The edge `(4, 1)`. -/
def e41 : T.Edge := ⟨(4, 1), by simp [T, par]⟩

/-- The internal edge `(1, 0)`. -/
def e10 : T.Edge := ⟨(1, 0), by simp [T, par]⟩

/-! ### Ancestor API on the example -/

/-- `1` is an ancestor of `3`, so the lineage of `3` passes through `1`. -/
example : T.visit 3 1 = 1 :=
  (T.visit_eq_one_iff_reflTransGen_of_isTree T_isTree).mpr
    (Relation.ReflTransGen.single (by simp [T, par]))

/-- The sibling `2` is not on the lineage of `3`. -/
example : T.visit 3 2 = 0 := by
  rw [T.visit_eq_visit_of_parents_eq_singleton (Y := 1) rfl (by decide),
    T.visit_eq_visit_of_parents_eq_singleton (Y := 0) rfl (by decide)]
  exact T.visit_root_left (by decide)

/-- Weights are visits of child endpoints: the lineage of `3` traverses `(1, 0)`. -/
example : T.weight 3 e10 = 1 := by
  rw [T.weight_eq_visit_of_isTree T_isTree]
  exact (T.visit_eq_one_iff_reflTransGen_of_isTree T_isTree).mpr
    (Relation.ReflTransGen.single (by simp [T, par, e10]))

/-- Laminarity: `(3, 1)` and `(1, 0)` lie on the lineage of `3`; every lineage through
`(3, 1)` also traverses `(1, 0)`. -/
example (h31 : T.weight 3 e31 = 1) (h10 : T.weight 3 e10 = 1) :
    (∀ Y, T.weight Y e31 = 1 → T.weight Y e10 = 1) ∨
      ∀ Y, T.weight Y e10 = 1 → T.weight Y e31 = 1 :=
  T.weight_laminar_of_isTree T_isTree h31 h10

/-! ### The bridge on the example -/

section Bridge

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {M : DriftModel μ T.Edge (Fin 5)}

/-- The edge `(3, 1)` is the only edge with child endpoint `3`. -/
theorem sum_child_three (g : T.Edge → ℝ) :
    ∑ e : T.Edge, (if e.1.1 = 3 then g e else 0) = g e31 := by
  rw [Finset.sum_eq_single e31]
  · exact ite_eq_left rfl
  · rintro ⟨⟨c, p⟩, hp⟩ _ hne
    by_cases hc : c = 3
    · subst hc
      have hp1 : p = 1 := by simpa [T, par] using hp
      subst hp1
      exact absurd rfl hne
    · exact ite_eq_right hc
  · exact fun h => absurd (Finset.mem_univ _) h

/-- The edge `(4, 1)` is the only edge with child endpoint `4`. -/
theorem sum_child_four (g : T.Edge → ℝ) :
    ∑ e : T.Edge, (if e.1.1 = 4 then g e else 0) = g e41 := by
  rw [Finset.sum_eq_single e41]
  · exact ite_eq_left rfl
  · rintro ⟨⟨c, p⟩, hp⟩ _ hne
    by_cases hc : c = 4
    · subst hc
      have hp1 : p = 1 := by simpa [T, par] using hp
      subst hp1
      exact absurd rfl hne
    · exact ite_eq_right hc
  · exact fun h => absurd (Finset.mem_univ _) h

/-- `f2 3 4` is the drift length of the path `3 – 1 – 4`. -/
theorem f2_three_four (hM : M.weight = T.weight) :
    f2 μ M.freq 3 4 = M.len e31 + M.len e41 := by
  have key : ∀ e : T.Edge,
      ((T.weight 1 + fun e : T.Edge => if e.1.1 = 3 then (1 : ℝ) else 0) e -
        (T.weight 1 + fun e : T.Edge => if e.1.1 = 4 then (1 : ℝ) else 0) e) ^ 2 * M.len e =
        (if e.1.1 = 3 then M.len e else 0) + if e.1.1 = 4 then M.len e else 0 := by
    intro e
    simp only [Pi.add_apply]
    by_cases h3 : e.1.1 = 3 <;> by_cases h4 : e.1.1 = 4
    · exact absurd (h3.symm.trans h4) (by decide)
    all_goals
      simp only [h3, h4, (by decide : ¬ (3 : Fin 5) = 4), (by decide : ¬ (4 : Fin 5) = 3),
        ↓reduceIte]
      ring
  rw [M.f2_freq, hM, T.weight_tree (X := 3) (Y := 1) rfl, T.weight_tree (X := 4) (Y := 1) rfl]
  simp_rw [key, Finset.sum_add_distrib]
  rw [sum_child_three M.len, sum_child_four M.len]

/-- The four-point condition on the tree, at the quartet `3, 4, 2, 0`. -/
example (hM : M.weight = T.weight) :
    f2 μ M.freq 3 2 + f2 μ M.freq 4 0 ≤
      max (f2 μ M.freq 3 4 + f2 μ M.freq 2 0) (f2 μ M.freq 3 0 + f2 μ M.freq 2 4) :=
  T.fourPointCondition_f2_of_isTree T_isTree hM 3 2 4 0

example (hM : M.weight = T.weight) : IsTreeMetric (f2 μ M.freq) :=
  T.isTreeMetric_f2_of_isTree T_isTree hM

end Bridge

/-- Non-vacuity: a drift model with the tree's weights and unit drift lengths exists; its `f2`
satisfies the four-point condition, is a tree metric, and is not degenerate (`f2 3 4 = 2`). -/
example : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (M : DriftModel μ T.Edge (Fin 5)),
    (∀ e, M.len e = 1) ∧ FourPointCondition (f2 μ M.freq) ∧ IsTreeMetric (f2 μ M.freq) ∧
      f2 μ M.freq 3 4 = 2 := by
  obtain ⟨Ω, _, μ, _, M, hw, hl⟩ :=
    Admixture.exists_driftModel (P := Fin 5) T.weight (fun _ => (1 : ℝ)) fun _ => zero_le_one
  refine ⟨Ω, _, μ, M, fun e => by rw [hl], T.fourPointCondition_f2_of_isTree T_isTree hw,
    T.isTreeMetric_f2_of_isTree T_isTree hw, ?_⟩
  rw [f2_three_four hw, hl]
  norm_num

#print axioms AdmixtureGraph.fourPointCondition_f2_of_isTree
#print axioms AdmixtureGraph.isTreeMetric_f2_of_isTree

end MathlibExtTest.Biology.PopulationGenetics.Admixture.TreeFourPoint
