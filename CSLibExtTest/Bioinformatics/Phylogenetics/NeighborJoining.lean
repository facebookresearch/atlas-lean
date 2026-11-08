/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.NeighborJoining
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Neighbor joining tests

* A non-vacuity witness: the quartet tree `01|23` (leaves `0, 1` on vertex `4`, leaves `2, 3`
  on vertex `5`) is a binary phylogenetic tree, and every edge-length function has a path-length
  metric satisfying the path hypothesis of `njRun_splits`.
* The theorems instantiated on the quartet: sides of pendant edges, the cherry lemma, and the
  split system induced on a partition into sides.
* Small evaluations of `initialDist`, `joinDist`, `qCriterion` and `splitGain`, including the
  values the definitions take outside their intended use.
* Boundary: with three taxa no join is allowed, so a run stops at once.
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

/-- **Non-vacuity witness.** The quartet tree is a binary phylogenetic tree. -/
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

/-- **Non-vacuity of the path hypothesis.** On any tree, the length of the unique path between
two taxa satisfies the path hypothesis of `njRun_splits`. -/
theorem exists_pathLength {X V : Type*} {G : SimpleGraph V} (hG : G.IsTree) (ι : X → V)
    (w : Sym2 V → ℝ) : ∃ d : X → X → ℝ,
      ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum := by
  refine ⟨fun x y => ((hG.existsUnique_path (ι x) (ι y)).exists.choose.edges.map w).sum,
    fun x y p hp => ?_⟩
  have h := (hG.existsUnique_path (ι x) (ι y)).unique
    (hG.existsUnique_path (ι x) (ι y)).exists.choose_spec hp
  simp only [h]

/-- The leaf side of the pendant edge `{0, 4}` holds only taxon `0`. -/
example : side quartet quartetLeaf 0 4 = {0} :=
  side_leaf (z := 0) quartet_isBinaryPhylogeneticTree (by decide)

/-- The two sides of the internal edge `{4, 5}` are complementary. -/
example : side quartet quartetLeaf 4 5 = univ \ side quartet quartetLeaf 5 4 :=
  (side_swap quartet_isBinaryPhylogeneticTree.1 (by decide : quartet.Adj 5 4))

/-- The cherry lemma on the quartet: for every path-length metric with positive edge lengths, a
pair of taxa minimizing the Q-criterion has a common neighbor. -/
example {w : Sym2 (Fin 6) → ℝ} (hw : ∀ e ∈ quartet.edgeSet, 0 < w e) {d : Fin 4 → Fin 4 → ℝ}
    (hd : ∀ x y (p : quartet.Walk (quartetLeaf x) (quartetLeaf y)), p.IsPath →
      d x y = (p.edges.map w).sum) {x y : Fin 4} (hxy : x ≠ y)
    (hmin : ∀ a' ∈ univ.image (fun x => ({x} : Finset (Fin 4))),
      ∀ b' ∈ univ.image (fun x => ({x} : Finset (Fin 4))), a' ≠ b' →
        qCriterion (univ.image fun x => ({x} : Finset (Fin 4))) (initialDist d) {x} {y} ≤
          qCriterion (univ.image fun x => ({x} : Finset (Fin 4))) (initialDist d) a' b') :
    ∃ u, quartet.Adj (quartetLeaf x) u ∧ quartet.Adj (quartetLeaf y) u :=
  exists_adj_adj_of_qCriterion_min quartet_isBinaryPhylogeneticTree hw hd (by simp) hxy hmin

/-- `njRun_splits` on the quartet: a complete run forms `{0, 1}` or `{2, 3}` exactly when it is
the side of an internal edge. -/
example {w : Sym2 (Fin 6) → ℝ} (hw : ∀ e ∈ quartet.edgeSet, 0 < w e) {d : Fin 4 → Fin 4 → ℝ}
    (hd : ∀ x y (p : quartet.Walk (quartetLeaf x) (quartetLeaf y)), p.IsPath →
      d x y = (p.edges.map w).sum) {S D C} (hrun : NJRun d S D C) (hS : S.card ≤ 3) :
    ({0, 1} ∈ C ∨ univ \ {0, 1} ∈ C) ↔ ∃ a b, quartet.Adj a b ∧ a ∉ Set.range quartetLeaf ∧
      b ∉ Set.range quartetLeaf ∧ ∀ x, x ∈ ({0, 1} : Finset (Fin 4)) ↔
        (quartet.deleteEdges {s(a, b)}).Reachable (quartetLeaf x) a :=
  njRun_splits quartet_isBinaryPhylogeneticTree hw hd hrun hS _

/-- The singletons of the quartet are sides of edges, so `exists_splitSystem_of_partition`
applies: the edges cutting no singleton (all of them) induce a split system on the clusters
containing every trivial split. -/
example {w : Sym2 (Fin 6) → ℝ} (hw : ∀ e ∈ quartet.edgeSet, 0 < w e) {d : Fin 4 → Fin 4 → ℝ}
    (hd : ∀ x y (p : quartet.Walk (quartetLeaf x) (quartetLeaf y)), p.IsPath →
      d x y = (p.edges.map w).sum) :
    ∃ (E : Type) (_ : Fintype E)
      (A : E → Finset {s // s ∈ univ.image fun x : Fin 4 => ({x} : Finset (Fin 4))}),
      ∀ s, ∃ e, A e = {s} := by
  have hT := quartet_isBinaryPhylogeneticTree
  have hside : ∀ s ∈ univ.image fun x : Fin 4 => ({x} : Finset (Fin 4)),
      ∃ u v, quartet.Adj u v ∧ side quartet quartetLeaf u v = s := by
    intro s hs
    obtain ⟨x, -, rfl⟩ := mem_image.mp hs
    have h1 : quartet.degree (quartetLeaf x) = 1 := (hT.2.2.1 _).mpr ⟨x, rfl⟩
    obtain ⟨b, hb, -⟩ := (quartet.degree_eq_one_iff_existsUnique_adj).mp h1
    exact ⟨quartetLeaf x, b, hb, side_leaf hT hb⟩
  obtain ⟨E, hE, A, -, -, -, -, -, -, -, hsingle, -⟩ := exists_splitSystem_of_partition hT hw hd
    hside (fun s hs t ht hst => by
      obtain ⟨x, -, rfl⟩ := mem_image.mp hs
      obtain ⟨y, -, rfl⟩ := mem_image.mp ht
      exact disjoint_singleton.mpr fun h => hst (h ▸ rfl))
    (fun x => ⟨{x}, mem_image_of_mem _ (mem_univ x), mem_singleton_self x⟩)
  exact ⟨E, hE, A, hsingle⟩

/-! ## Small evaluations -/

/-- On singletons the initial cluster dissimilarity is `d`. -/
example (d : Fin 3 → Fin 3 → ℝ) (x y : Fin 3) : initialDist d {x} {y} = d x y := by
  simp [initialDist]

/-- Outside singletons `initialDist` is the sum of the pairwise values; the algorithm never
reads these values. -/
example (d : Fin 3 → Fin 3 → ℝ) : initialDist d {0, 1} {2} = d 0 2 + d 1 2 := by
  simp [initialDist]

/-- The new cluster is at distance `0` from itself. -/
example (D : Finset (Fin 3) → Finset (Fin 3) → ℝ) :
    joinDist D {0} {1} ({0} ∪ {1}) ({0} ∪ {1}) = 0 := by
  simp [joinDist]

/-- The neighbor-joining distance update. -/
example (D : Finset (Fin 3) → Finset (Fin 3) → ℝ) :
    joinDist D {0} {1} ({0} ∪ {1}) {2} = (D {0} {2} + D {1} {2} - D {0} {1}) / 2 := by
  simp [joinDist, show ({2} : Finset (Fin 3)) ≠ {0, 1} by decide]

/-- The Q-criterion of singletons on four taxa with all distances `1` off the diagonal. -/
example : qCriterion (univ.image fun x : Fin 4 => ({x} : Finset (Fin 4)))
    (initialDist fun x y => if x = y then 0 else 1) {0} {1} = -4 := by
  rw [qCriterion_singleton]
  simp [Fin.sum_univ_four]
  norm_num

/-- `splitGain`: `1` on a separating split, the far-side count otherwise. -/
example : splitGain ({0, 1} : Finset (Fin 4)) 0 2 = 1 ∧
    splitGain ({0, 1} : Finset (Fin 4)) 0 1 = 2 ∧
    splitGain ({0, 1} : Finset (Fin 4)) 2 3 = 2 := by
  have h : (univ \ ({0, 1} : Finset (Fin 4))).card = 2 := by decide
  refine ⟨by simp [splitGain], ?_, ?_⟩ <;> simp [splitGain, h]

/-! ## Boundary: three taxa -/

/-- With three taxa no join is allowed: every run stays at the singletons, with no cluster
formed. -/
example {d : Fin 3 → Fin 3 → ℝ} {S : Finset (Finset (Fin 3))} {D} {C} (h : NJRun d S D C) :
    C = ∅ := by
  cases h with
  | init => rfl
  | join h' h4 _ _ _ _ =>
    exfalso
    -- every cluster set reachable from the singletons has at most three clusters
    have : ∀ {S D C}, NJRun d S D C → S.card ≤ 3 := by
      intro S D C hr
      induction hr with
      | init => exact (Finset.card_image_le).trans (by simp)
      | join _ h4' ha hb hab _ ih =>
        exfalso
        omega
    have := this h'
    omega

end Cslib.Bioinformatics.Phylogenetics.NeighborJoining
