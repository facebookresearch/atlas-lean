/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.FK.Tilt
import Code.Lattice.EulerFaces2

open scoped BigOperators
open SimpleGraph

namespace StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def spanningClusterCount (A : Finset (Sym2 V)) : ℕ :=
  Nat.card (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).ConnectedComponent



noncomputable def tutteEval (G : SimpleGraph V) [DecidableRel G.Adj] (x y : ℝ) : ℝ :=
  ∑ A ∈ G.edgeFinset.powerset,
    (x - 1) ^ (spanningClusterCount A - Nat.card G.ConnectedComponent) *
      (y - 1) ^ (A.card + spanningClusterCount A - Fintype.card V)



noncomputable def randomClusterPartition (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : ℝ) : ℝ :=
  ∑ A ∈ G.edgeFinset.powerset,
    p ^ A.card * (1 - p) ^ (G.edgeFinset.card - A.card) *
      q ^ spanningClusterCount A


def edgeSetConfig (A : Finset (Sym2 V)) : ConfigSpace (Sym2 V) :=
  fun e => decide (e ∈ A)

omit [Fintype V] in
@[simp] theorem edgeSetConfig_apply (A : Finset (Sym2 V)) (e : Sym2 V) :
    edgeSetConfig A e = true ↔ e ∈ A := by
  simp [edgeSetConfig]

private theorem openSub_edgeSetConfig (G : SimpleGraph V) [DecidableRel G.Adj]
    {A : Finset (Sym2 V)} (hA : A ⊆ G.edgeFinset) :
    openSub G (edgeSetConfig A) = SimpleGraph.fromEdgeSet (A : Set (Sym2 V)) := by
  ext x y
  simp only [openSub_adj, edgeSetConfig_apply, SimpleGraph.fromEdgeSet_adj,
    Finset.mem_coe]
  constructor
  · exact fun h => ⟨h.2, h.1.ne⟩
  · rintro ⟨hxy, hne⟩
    have he : s(x, y) ∈ G.edgeFinset := hA hxy
    exact ⟨SimpleGraph.mem_edgeSet G |>.mp (SimpleGraph.mem_edgeFinset.mp he), hxy⟩

private theorem openCount_edgeSetConfig (G : SimpleGraph V) [DecidableRel G.Adj]
    {A : Finset (Sym2 V)} (hA : A ⊆ G.edgeFinset) :
    openCount G (edgeSetConfig A) = A.card := by
  unfold openCount
  congr 1
  ext e
  simp only [Finset.mem_filter, edgeSetConfig_apply]
  constructor
  · exact fun he => he.2
  · exact fun he => ⟨hA he, he⟩

private theorem closedCount_edgeSetConfig (G : SimpleGraph V) [DecidableRel G.Adj]
    {A : Finset (Sym2 V)} (hA : A ⊆ G.edgeFinset) :
    closedCount G (edgeSetConfig A) = G.edgeFinset.card - A.card := by
  have hcount := openCount_add_closedCount G (edgeSetConfig A)
  rw [openCount_edgeSetConfig G hA] at hcount
  omega

private theorem numClusters_edgeSetConfig (G : SimpleGraph V) [DecidableRel G.Adj]
    {A : Finset (Sym2 V)} (hA : A ⊆ G.edgeFinset) :
    numClusters G (edgeSetConfig A) = spanningClusterCount A := by
  unfold numClusters spanningClusterCount
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_congr (by rw [openSub_edgeSetConfig G hA])



theorem fkWeight_edgeSetConfig (G : SimpleGraph V) [DecidableRel G.Adj]
    {A : Finset (Sym2 V)} (hA : A ⊆ G.edgeFinset) (p q : ℝ) :
    fkWeight G p q (edgeSetConfig A) =
      p ^ A.card * (1 - p) ^ (G.edgeFinset.card - A.card) *
        q ^ spanningClusterCount A := by
  unfold fkWeight
  rw [edgeProduct_eq_pow, openCount_edgeSetConfig G hA,
    closedCount_edgeSetConfig G hA, numClusters_edgeSetConfig G hA]



theorem randomClusterPartition_eq_sum_fkWeight
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ℝ) :
    randomClusterPartition G p q =
      ∑ A ∈ G.edgeFinset.powerset, fkWeight G p q (edgeSetConfig A) := by
  classical
  unfold randomClusterPartition
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.mem_powerset] at hA
  exact (fkWeight_edgeSetConfig G hA p q).symm

private lemma tutte_term_algebra {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {m a n kG kA : ℕ} (ha : a ≤ m) (hkGn : kG ≤ n) (hk : kG ≤ kA)
    (hn : n ≤ a + kA) :
    (1 - p) ^ m * q ^ kG * (p / (1 - p)) ^ (n - kG) *
        ((q / (p / (1 - p))) ^ (kA - kG) *
          (p / (1 - p)) ^ (a + kA - n)) =
      p ^ a * (1 - p) ^ (m - a) * q ^ kA := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have h1p0 : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  have hv0 : p / (1 - p) ≠ 0 := div_ne_zero hp0 h1p0
  have hqexp : kG + (kA - kG) = kA := Nat.add_sub_of_le hk
  have hvexp : (n - kG) + (a + kA - n) = a + (kA - kG) := by omega
  have hqpow : q ^ kG * q ^ (kA - kG) = q ^ kA := by
    rw [← pow_add, hqexp]
  have hvpow :
      (p / (1 - p)) ^ (n - kG) * (p / (1 - p)) ^ (a + kA - n) =
        (p / (1 - p)) ^ a * (p / (1 - p)) ^ (kA - kG) := by
    rw [← pow_add, hvexp, pow_add]
  rw [div_pow]
  calc
    _ = (1 - p) ^ m * (q ^ kG * q ^ (kA - kG)) *
          ((p / (1 - p)) ^ (n - kG) * (p / (1 - p)) ^ (a + kA - n)) /
            (p / (1 - p)) ^ (kA - kG) := by ring
    _ = (1 - p) ^ m * q ^ kA *
          ((p / (1 - p)) ^ a * (p / (1 - p)) ^ (kA - kG)) /
            (p / (1 - p)) ^ (kA - kG) := by rw [hqpow, hvpow]
    _ = (1 - p) ^ m * q ^ kA * (p / (1 - p)) ^ a := by
      field_simp
    _ = p ^ a * (1 - p) ^ (m - a) * q ^ kA := by
      calc
        _ = ((1 - p) ^ (m - a) * (1 - p) ^ a) * q ^ kA *
              (p / (1 - p)) ^ a := by
            rw [← pow_add, Nat.sub_add_cancel ha]
        _ = p ^ a * (1 - p) ^ (m - a) * q ^ kA := by
          rw [div_pow]
          field_simp






theorem randomClusterPartition_eq_tutte (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    randomClusterPartition G p q =
      (1 - p) ^ G.edgeFinset.card * q ^ Nat.card G.ConnectedComponent *
        (p / (1 - p)) ^ (Fintype.card V - Nat.card G.ConnectedComponent) *
        tutteEval G (1 + q / (p / (1 - p))) (1 + p / (1 - p)) := by
  classical
  unfold randomClusterPartition tutteEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.mem_powerset] at hA
  have hgraph : SimpleGraph.fromEdgeSet (A : Set (Sym2 V)) ≤ G := by
    rw [← SimpleGraph.fromEdgeSet_edgeSet G, ← SimpleGraph.coe_edgeFinset]
    exact SimpleGraph.fromEdgeSet_mono (by exact_mod_cast hA)
  have hk : Nat.card G.ConnectedComponent ≤ spanningClusterCount A := by
    exact SimpleGraph.ConnectedComponent.card_le_card_of_le hgraph
  have hn : Fintype.card V ≤ A.card + spanningClusterCount A := by
    have h := StatMech.Lattice.card_le_edgeSet_add_components
      (SimpleGraph.fromEdgeSet (A : Set (Sym2 V)))
    have hsub : (A : Set (Sym2 V)) ⊆ G.edgeSet := by
      simpa [← SimpleGraph.coe_edgeFinset] using hA
    have hedge : (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).edgeSet = A := by
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      ext e
      constructor
      · exact fun he => he.1
      · intro he
        exact ⟨he, fun hdiag => G.edgeSet_subset_compl_diagSet (hsub he) hdiag⟩
    rw [Nat.card_eq_fintype_card, hedge, Set.ncard_coe_finset] at h
    simpa only [spanningClusterCount, Nat.card_eq_fintype_card] using h
  have hkGn : Nat.card G.ConnectedComponent ≤ Fintype.card V := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_surjective G.connectedComponentMk (by
      intro c
      refine SimpleGraph.ConnectedComponent.ind ?_ c
      intro v
      exact ⟨v, rfl⟩)
  simp only [add_sub_cancel_left]
  symm
  exact tutte_term_algebra hp hp1 (Finset.card_le_card hA) hkGn hk hn

end StatMech.FK
