/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.NeighborJoiningRobustness
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Robustness of neighbor joining: tests

* The tree-level cherry lemma instantiated on the quartet tree `01|23` (the fixture of the
  neighbor-joining tests).
* A concrete witness on the split system of the quartet with unit edge lengths (`μ = 1`): the
  hypotheses hold for a dissimilarity `D ≠ d` within `2/5` of the tree metric, a minimizer of
  the Q-criterion exists, and it is a side.
* Boundary: the strict bound is needed. With errors of exactly `μ / 2`, the non-cherry pair
  `0, 2` minimizes the Q-criterion.
-/

namespace Cslib.Bioinformatics.Phylogenetics.NeighborJoining

open Finset

/-! ## The quartet tree -/

/-- Adjacency of the quartet tree `01|23`. -/
def quartetAdj : Fin 6 → Fin 6 → Bool
  | 0, 4 | 4, 0 | 1, 4 | 4, 1 | 2, 5 | 5, 2 | 3, 5 | 5, 3 | 4, 5 | 5, 4 => true
  | _, _ => false

/-- The quartet tree `01|23` on the vertices `Fin 6`. -/
def quartet : SimpleGraph (Fin 6) where
  Adj a b := quartetAdj a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel quartet.Adj := fun a b =>
  inferInstanceAs (Decidable (quartetAdj a b = true))

/-- The taxa `0, 1, 2, 3` sit on the vertices `0, 1, 2, 3`. -/
def quartetLeaf : Fin 4 → Fin 6 := Fin.castLE (by norm_num)

/-- Every vertex of the quartet reaches vertex `4`. -/
lemma quartet_reachable_four (v : Fin 6) : quartet.Reachable v 4 := by
  have a04 : quartet.Adj 0 4 := by decide
  have a14 : quartet.Adj 1 4 := by decide
  have a25 : quartet.Adj 2 5 := by decide
  have a35 : quartet.Adj 3 5 := by decide
  have a54 : quartet.Adj 5 4 := by decide
  fin_cases v
  · exact a04.reachable
  · exact a14.reachable
  · exact a25.reachable.trans a54.reachable
  · exact a35.reachable.trans a54.reachable
  · exact .rfl
  · exact a54.reachable

/-- The quartet tree is a binary phylogenetic tree. -/
theorem quartet_isBinaryPhylogeneticTree : IsBinaryPhylogeneticTree quartet quartetLeaf := by
  refine ⟨?_, Fin.castLE_injective _, fun v => ?_, fun v hv => ?_⟩
  · rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨⟨fun u v => (quartet_reachable_four u).trans (quartet_reachable_four v).symm⟩, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    decide
  · fin_cases v
    · exact ⟨fun _ => ⟨0, rfl⟩, fun _ => by decide⟩
    · exact ⟨fun _ => ⟨1, rfl⟩, fun _ => by decide⟩
    · exact ⟨fun _ => ⟨2, rfl⟩, fun _ => by decide⟩
    · exact ⟨fun _ => ⟨3, rfl⟩, fun _ => by decide⟩
    · refine ⟨fun h => absurd h (by decide), ?_⟩
      rintro ⟨i, hi⟩
      fin_cases i <;> simp [quartetLeaf, Fin.ext_iff] at hi
    · refine ⟨fun h => absurd h (by decide), ?_⟩
      rintro ⟨i, hi⟩
      fin_cases i <;> simp [quartetLeaf, Fin.ext_iff] at hi
  · fin_cases v
    · exact absurd ⟨0, rfl⟩ hv
    · exact absurd ⟨1, rfl⟩ hv
    · exact absurd ⟨2, rfl⟩ hv
    · exact absurd ⟨3, rfl⟩ hv
    · decide
    · decide

/-- The robust cherry lemma on the quartet: for every dissimilarity within half the internal
edge length of a path-length metric, a pair minimizing the Q-criterion has a common
neighbor. -/
example {w : Sym2 (Fin 6) → ℝ} (hw : ∀ e ∈ quartet.edgeSet, 0 < w e) {d : Fin 4 → Fin 4 → ℝ}
    (hd : ∀ x y (p : quartet.Walk (quartetLeaf x) (quartetLeaf y)), p.IsPath →
      d x y = (p.edges.map w).sum) {D : Fin 4 → Fin 4 → ℝ} (hDsymm : ∀ x y, D x y = D y x)
    (hD0 : ∀ x, D x x = 0) (hDd : ∀ x y, x ≠ y → |D x y - d x y| < w s(4, 5) / 2)
    {x y : Fin 4} (hxy : x ≠ y)
    (hmin : ∀ a' ∈ univ.image (fun x => ({x} : Finset (Fin 4))),
      ∀ b' ∈ univ.image (fun x => ({x} : Finset (Fin 4))), a' ≠ b' →
        qCriterion (univ.image fun x => ({x} : Finset (Fin 4))) (initialDist D) {x} {y} ≤
          qCriterion (univ.image fun x => ({x} : Finset (Fin 4))) (initialDist D) a' b') :
    ∃ u, quartet.Adj (quartetLeaf x) u ∧ quartet.Adj (quartetLeaf y) u := by
  refine exists_adj_adj_of_qCriterion_min_of_abs_sub_lt quartet_isBinaryPhylogeneticTree hw hd
    (fun a b hab ha hb => ?_) hDsymm hD0 hDd (by simp) hxy hmin
  -- the only internal edge of the quartet is `{4, 5}`
  have ha' : a = 4 ∨ a = 5 := by
    fin_cases a
    · exact absurd ⟨0, rfl⟩ ha
    · exact absurd ⟨1, rfl⟩ ha
    · exact absurd ⟨2, rfl⟩ ha
    · exact absurd ⟨3, rfl⟩ ha
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hb' : b = 4 ∨ b = 5 := by
    fin_cases b
    · exact absurd ⟨0, rfl⟩ hb
    · exact absurd ⟨1, rfl⟩ hb
    · exact absurd ⟨2, rfl⟩ hb
    · exact absurd ⟨3, rfl⟩ hb
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact absurd hab (by decide)
  · exact le_rfl
  · rw [Sym2.eq_swap]
  · exact absurd hab (by decide)

/-! ## A concrete split system -/

/-- The splits of the quartet tree `01|23`, one per dart: the four pendant edges and the
internal edge, each in both orientations. -/
def quartetSplit : Fin 10 → Finset (Fin 4)
  | 0 => {0} | 1 => {1, 2, 3} | 2 => {1} | 3 => {0, 2, 3} | 4 => {2} | 5 => {0, 1, 3}
  | 6 => {3} | 7 => {0, 1, 2} | 8 => {0, 1} | 9 => {2, 3}

lemma quartetSplit_nonempty : ∀ e, (quartetSplit e).Nonempty := by decide

lemma quartetSplit_compl : ∀ e, ∃ e', quartetSplit e' = univ \ quartetSplit e := by decide

lemma quartetSplit_compat : ∀ e e', Disjoint (quartetSplit e) (quartetSplit e') ∨
    quartetSplit e ⊆ quartetSplit e' ∨ quartetSplit e' ⊆ quartetSplit e ∨
      quartetSplit e ∪ quartetSplit e' = univ := by decide

lemma quartetSplit_bin : ∀ e, 2 ≤ (quartetSplit e).card → ∃ e₁ e₂,
    Disjoint (quartetSplit e₁) (quartetSplit e₂) ∧
      quartetSplit e₁ ∪ quartetSplit e₂ = quartetSplit e := by decide

lemma quartetSplit_single : ∀ z, ∃ e, quartetSplit e = {z} := by decide

/-- The tree metric of the quartet with unit edge lengths: `2` within a cherry, `3` across. -/
noncomputable def quartetDist (x y : Fin 4) : ℝ :=
  if x = y then 0 else if (x.val < 2 ↔ y.val < 2) then 2 else 3

lemma quartetDist_eq (x y : Fin 4) : quartetDist x y = (1 / 2) * ∑ e, (1 : ℝ) *
    (if (x ∈ quartetSplit e ↔ y ∈ quartetSplit e) then 0 else 1) := by
  fin_cases x <;> fin_cases y <;> simp [quartetDist, quartetSplit, Fin.sum_univ_succ] <;>
    norm_num

/-- A perturbation of the quartet metric: `D 0 2 = D 2 0 = 3 + 2/5`. -/
noncomputable def quartetNoisy (x y : Fin 4) : ℝ :=
  quartetDist x y + if (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) then 2 / 5 else 0

/-- **Non-vacuity witness.** For the noisy quartet dissimilarity (within `2/5` of the tree
metric, whose internal split has weight `μ = 1`), some pair minimizes the Q-criterion, and
every such pair is a side of the split system. -/
theorem quartetNoisy_witness : ∃ x y : Fin 4, x ≠ y ∧
    (∀ x' y', x' ≠ y' →
      ((Fintype.card (Fin 4) : ℝ) - 2) * quartetNoisy x y - ∑ z, quartetNoisy x z -
          ∑ z, quartetNoisy y z ≤
        ((Fintype.card (Fin 4) : ℝ) - 2) * quartetNoisy x' y' - ∑ z, quartetNoisy x' z -
          ∑ z, quartetNoisy y' z) ∧
    ∃ e, quartetSplit e = {x, y} := by
  have hne : ((univ : Finset (Fin 4 × Fin 4)).filter fun p => p.1 ≠ p.2).Nonempty :=
    ⟨(0, 1), by simp⟩
  obtain ⟨p, hp, hmin⟩ := exists_min_image _ (fun p : Fin 4 × Fin 4 =>
    ((Fintype.card (Fin 4) : ℝ) - 2) * quartetNoisy p.1 p.2 - ∑ z, quartetNoisy p.1 z -
      ∑ z, quartetNoisy p.2 z) hne
  have hp' : p.1 ≠ p.2 := (mem_filter.mp hp).2
  have hmin' : ∀ x' y', x' ≠ y' →
      ((Fintype.card (Fin 4) : ℝ) - 2) * quartetNoisy p.1 p.2 - ∑ z, quartetNoisy p.1 z -
          ∑ z, quartetNoisy p.2 z ≤
        ((Fintype.card (Fin 4) : ℝ) - 2) * quartetNoisy x' y' - ∑ z, quartetNoisy x' z -
          ∑ z, quartetNoisy y' z :=
    fun x' y' h => hmin (x', y') (by simp [h])
  refine ⟨p.1, p.2, hp', hmin', ?_⟩
  refine exists_eq_pair_of_qCriterion_min_of_abs_sub_lt quartetSplit (fun _ => 1)
    (fun _ => one_pos) quartetSplit_nonempty quartetSplit_compl quartetSplit_compat
    quartetSplit_bin quartetSplit_single (by simp) (μ := 1) (fun _ _ _ => le_rfl)
    quartetDist_eq ?_ ?_ ?_ hp' hmin'
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [quartetNoisy, quartetDist]
  · intro x
    fin_cases x <;> simp [quartetNoisy, quartetDist]
  · intro x y _
    fin_cases x <;> fin_cases y <;> simp [quartetNoisy, quartetDist] <;> norm_num [abs_of_pos]

/-! ## Boundary: the strict bound is needed -/

/-- A dissimilarity at distance exactly `1/2 = μ / 2` from the quartet metric: `3` on the pairs
`03` and `12`, `5/2` on the other distinct pairs (the cherries `01`, `23` are lengthened and the
across pairs `02`, `13` are shortened). -/
noncomputable def quartetTie (x y : Fin 4) : ℝ :=
  if x = y then 0 else if x.val + y.val = 3 then 3 else 5 / 2

/-- With errors of exactly `μ / 2`, the non-cherry pair `0, 2` minimizes the Q-criterion, so the
strict inequality in `exists_eq_pair_of_qCriterion_min_of_abs_sub_lt` cannot be relaxed. -/
example : (∀ x y : Fin 4, x ≠ y → |quartetTie x y - quartetDist x y| ≤ 1 / 2) ∧
    (∀ x' y' : Fin 4, x' ≠ y' →
      ((Fintype.card (Fin 4) : ℝ) - 2) * quartetTie 0 2 - ∑ z, quartetTie 0 z -
          ∑ z, quartetTie 2 z ≤
        ((Fintype.card (Fin 4) : ℝ) - 2) * quartetTie x' y' - ∑ z, quartetTie x' z -
          ∑ z, quartetTie y' z) ∧
    ¬ ∃ e, quartetSplit e = {0, 2} := by
  refine ⟨fun x y _ => ?_, fun x' y' h => ?_, by decide⟩
  · fin_cases x <;> fin_cases y <;> norm_num [quartetTie, quartetDist, abs_of_nonneg]
  · fin_cases x' <;> fin_cases y' <;>
      first | exact absurd rfl h | norm_num [quartetTie, Fin.sum_univ_four]

end Cslib.Bioinformatics.Phylogenetics.NeighborJoining
