/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.BranchLengthScore
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Branch Length Score tests

On the star tree on three taxa with edge lengths `1, 2, 4` (total length `7`): the side of
a pendant edge is the singleton of its leaf; the BLS values are `bls {0, 1} = 3` (the two
sister branches, counted once each, via the two darts of each pendant edge),
`bls {2} = 0`, `bls` of all leaves `= 7`, and the normalized score of `{0, 1}` is `3 / 7`.
Duplicate species labels cannot be expressed: the tree's `label` is a bijection between the
taxa and the leaves, so the old duplicate-label disagreement has no public API analogue.
-/

namespace Cslib.Bioinformatics.Phylogenetics.BranchLengthScore

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open Cslib.Bioinformatics.Phylogenetics.Splits

/-- The star with center `3` and leaves `0, 1, 2`. -/
def starGraph : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun i _ => i = 3

theorem starGraph_adj (i j : Fin 4) :
    starGraph.Adj i j ↔ i ≠ j ∧ (i = 3 ∨ j = 3) := by
  rw [starGraph, SimpleGraph.fromRel_adj]

instance : DecidableRel starGraph.Adj := fun i j =>
  decidable_of_iff _ (starGraph_adj i j).symm

theorem starGraph_degree :
    ∀ v : Fin 4, starGraph.degree v = if v = 3 then 3 else 1 := by
  decide

theorem starGraph_card : starGraph.edgeFinset.card = 3 := by decide

theorem starGraph_connected : starGraph.Connected := by
  have h : ∀ v, starGraph.Reachable v 3 := by
    intro v
    by_cases hv : v = 3
    · subst hv; rfl
    · exact SimpleGraph.Adj.reachable ((starGraph_adj _ _).2 ⟨hv, Or.inr rfl⟩)
  exact ⟨fun u v => (h u).trans (h v).symm⟩

theorem starGraph_isTree : starGraph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨starGraph_connected, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, starGraph_card]
  simp

theorem starGraph_degree_castSucc :
    ∀ i : Fin 3, starGraph.degree i.castSucc = 1 := by
  decide

/-- The labeling of the leaves of the star. -/
def starLabel : Fin 3 → {v : Fin 4 // starGraph.degree v = 1} :=
  fun i => ⟨i.castSucc, starGraph_degree_castSucc i⟩

theorem starLabel_bijective : Function.Bijective starLabel := by decide

/-- Non-vacuity: the star with three leaves is an unrooted binary phylogenetic tree on three
taxa. `abbrev` (reducible) so that `star.V` unfolds to `Fin 4` for type-class search and
rewriting in the proofs below. -/
noncomputable abbrev star : UnrootedBinaryTree (Fin 3) where
  V := Fin 4
  G := starGraph
  isTree := starGraph_isTree
  label := Equiv.ofBijective _ starLabel_bijective
  degree_eq_three v hv := by
    rw [starGraph_degree] at hv ⊢
    split_ifs at hv ⊢ <;> simp_all

theorem star_label_coe (i : Fin 3) : (star.label i : Fin 4) = i.castSucc := rfl

/-- The center is adjacent to every leaf. -/
theorem star_adj_center (i : Fin 3) : star.G.Adj (3 : Fin 4) (star.label i) := by
  rw [star_label_coe]
  exact (starGraph_adj _ _).2 ⟨by fin_cases i <;> decide, Or.inl rfl⟩

/-- Every leaf is adjacent to the center. -/
theorem star_adj_leaf (i : Fin 3) : star.G.Adj (star.label i) (3 : Fin 4) := by
  rw [star_label_coe]
  exact (starGraph_adj _ _).2 ⟨by fin_cases i <;> decide, Or.inr rfl⟩

/-- The side of a pendant edge of the star is the singleton of its leaf. -/
theorem star_edgeSide_leaf (i : Fin 3) :
    edgeSide star (3 : Fin 4) (star.label i) = {i} :=
  edgeSide_of_leaf star (star_adj_center i)

/-- The side of a pendant edge seen from the leaf is the complement of the singleton. -/
theorem star_edgeSide_leaf_rev (i : Fin 3) :
    edgeSide star (star.label i) (3 : Fin 4) = ({i} : Finset (Fin 3))ᶜ := by
  have h := compl_edgeSide star (star_adj_leaf i)
  rw [star_edgeSide_leaf i] at h
  rw [← h, compl_compl]

/-- Edge lengths on the star: `1, 2, 4` on the three pendant edges. -/
noncomputable def starW : Sym2 (Fin 4) → ℝ := fun e =>
  if e = s(0, 3) then 1
  else if e = s(1, 3) then 2
  else if e = s(2, 3) then 4 else 0

theorem star_nonneg : NonnegWeights star starW := by
  intro t
  simp only [starW]
  split_ifs <;> norm_num

theorem star_edgeFinset :
    star.G.edgeFinset = {s(0, 3), s(1, 3), s(2, 3)} := by
  decide

/-- The total branch length of the star is `7`. -/
theorem star_total : totalLength star starW = 7 := by
  unfold totalLength
  rw [dart_sum_edge, star_edgeFinset,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [starW, Sym2.eq_iff, Fin.ext_iff]
  norm_num

/-- The six darts of the star, center first in each edge pair. -/
theorem star_dart_univ : (Finset.univ : Finset star.G.Dart) =
    {⟨((3 : Fin 4), (0 : Fin 4)), by decide⟩,
     ⟨((0 : Fin 4), (3 : Fin 4)), by decide⟩,
     ⟨((3 : Fin 4), (1 : Fin 4)), by decide⟩,
     ⟨((1 : Fin 4), (3 : Fin 4)), by decide⟩,
     ⟨((3 : Fin 4), (2 : Fin 4)), by decide⟩,
     ⟨((2 : Fin 4), (3 : Fin 4)), by decide⟩} := by
  ext ⟨⟨a, b⟩, h⟩
  constructor
  · intro _
    have h' : starGraph.Adj a b := h
    rw [starGraph_adj] at h'
    fin_cases a <;> fin_cases b <;>
      simp_all [SimpleGraph.Dart.ext_iff]
  · intro _; exact Finset.mem_univ _

/-- Two sister species: only their two branches, each counted once. -/
theorem star_bls_01 : bls {0, 1} star starW = 3 := by
  have e0 : edgeSide star (3 : Fin 4) (0 : Fin 4) = ({0} : Finset (Fin 3)) :=
    star_edgeSide_leaf 0
  have e0r : edgeSide star (0 : Fin 4) (3 : Fin 4) = ({1, 2} : Finset (Fin 3)) := by
    have h := star_edgeSide_leaf_rev 0
    rwa [show (({0} : Finset (Fin 3))ᶜ) = ({1, 2} : Finset (Fin 3)) from by decide] at h
  have e1 : edgeSide star (3 : Fin 4) (1 : Fin 4) = ({1} : Finset (Fin 3)) :=
    star_edgeSide_leaf 1
  have e1r : edgeSide star (1 : Fin 4) (3 : Fin 4) = ({0, 2} : Finset (Fin 3)) := by
    have h := star_edgeSide_leaf_rev 1
    rwa [show (({1} : Finset (Fin 3))ᶜ) = ({0, 2} : Finset (Fin 3)) from by decide] at h
  have e2 : edgeSide star (3 : Fin 4) (2 : Fin 4) = ({2} : Finset (Fin 3)) :=
    star_edgeSide_leaf 2
  have e2r : edgeSide star (2 : Fin 4) (3 : Fin 4) = ({0, 1} : Finset (Fin 3)) := by
    have h := star_edgeSide_leaf_rev 2
    rwa [show (({2} : Finset (Fin 3))ᶜ) = ({0, 1} : Finset (Fin 3)) from by decide] at h
  unfold bls
  rw [star_dart_univ,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [SimpleGraph.Dart.edge_mk]
  rw [e0, e0r, e1, e1r, e2, e2r]
  rw [ite_eq_left (by decide :
      Separates Finset.univ ({0, 1} : Finset (Fin 3)) ({0} : Finset (Fin 3))),
    ite_eq_left (by decide :
      Separates Finset.univ ({0, 1} : Finset (Fin 3)) ({1, 2} : Finset (Fin 3))),
    ite_eq_left (by decide :
      Separates Finset.univ ({0, 1} : Finset (Fin 3)) ({1} : Finset (Fin 3))),
    ite_eq_left (by decide :
      Separates Finset.univ ({0, 1} : Finset (Fin 3)) ({0, 2} : Finset (Fin 3))),
    ite_eq_right (by decide :
      ¬ Separates Finset.univ ({0, 1} : Finset (Fin 3)) ({2} : Finset (Fin 3))),
    ite_eq_right (by decide :
      ¬ Separates Finset.univ ({0, 1} : Finset (Fin 3)) ({0, 1} : Finset (Fin 3)))]
  norm_num [starW, Sym2.eq_iff, Fin.ext_iff]

/-- A single species has BLS `0`. -/
example : bls {2} star starW = 0 := bls_singleton 2 star starW

/-- All species give the whole tree. -/
example : bls Finset.univ star starW = 7 := by
  rw [bls_leaves 0 star starW, star_total]

/-- Monotonicity on the star. -/
example : bls {0, 1} star starW ≤ bls {0, 1, 2} star starW :=
  bls_mono (by decide) star starW star_nonneg

/-- The normalized score of `{0, 1}` is `3 / 7`. -/
example : blsFrac {0, 1} star starW = 3 / 7 := by
  unfold blsFrac
  rw [star_bls_01, star_total]

/-- Duplicate labels cannot be expressed: the labeling is bijective. -/
example : Function.Bijective star.label := star.label.bijective

end Cslib.Bioinformatics.Phylogenetics.BranchLengthScore
