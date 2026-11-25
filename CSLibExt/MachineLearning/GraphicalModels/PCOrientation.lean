/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.GraphicalModels.PCSkeleton
public import CSLibExt.MachineLearning.GraphicalModels.VermaPearlForward

/-!
# The PC orientation phase: v-structures from separating sets

The v-structure orientation step of the PC algorithm (Spirtes-Glymour-Scheines;
MIT 6.S091 Lecture 5, Algorithm 2 and Theorem 5.1; Kalisch and Bühlmann 2007),
on top of the adjacency phase in `PCSkeleton.lean`: an unshielded triple
`a - c - b` of the estimated skeleton is oriented `a → c ← b` exactly when `c`
is not in the separating set recorded for `a` and `b`.

Correctness needs one hypothesis beyond the adjacency phase's Markov and
adjacency-faithfulness assumptions: orientation-faithfulness, the per-separator
collider criterion of Verma-Pearl Lemma 2. It cannot be dropped: an oracle for
the chain `0 → 1 → 2` that also declares `0` and `2` independent given the
empty set is Markov and adjacency-faithful, yet makes PC orient a false
collider (the test file exhibits this table). Faithfulness of a law implies
orientation-faithfulness, and the assembled theorem recovers the skeleton and
the v-structures of the true graph from any faithful law.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset MetaMathlibExt.FiniteWeight BayesianDirichlet

variable {α β : Type*} {n : ℕ}

namespace BayesNet

variable (b : BayesNet α n)

/-- **Orientation-faithfulness** of an oracle (MIT 6.S091 Lecture 5, Definition 5.3, with the
endpoint-free convention): for every unshielded triple `i - c - j` of the graph and every set `S`
of other vertices the oracle declares to separate `i` from `j`, `c` is a collider `i → c ← j`
exactly when `c ∉ S`. Both endpoint orders are quantified. -/
def OrientationFaithful (O : CIOracle n) : Prop :=
  ∀ (i c j : Fin n) (S : Finset (Fin n)), b.Adj i c → b.Adj c j → i ≠ j → ¬ b.Adj i j →
    i ∉ S → j ∉ S → O.Indep i j S → (b.Edge i c ∧ b.Edge j c ↔ c ∉ S)

end BayesNet

namespace PCResult

/-- **The PC collider rule** (MIT 6.S091 Lecture 5, Algorithm 2 PC-Orient, lines 3-5;
Kalisch and Bühlmann 2007, Algorithm 2, first loop): `a - c - b` is an unshielded triple of the
estimated skeleton whose middle vertex is not in the recorded separating set of `a` and `b`;
PC orients it `a → c ← b`. -/
def IsCollider (r : PCResult n) (a c b : Fin n) : Prop :=
  r.skeleton.Adj a c ∧ r.skeleton.Adj c b ∧ a ≠ b ∧ ¬ r.skeleton.Adj a b ∧ c ∉ r.sepset a b

instance instDecidableIsCollider (r : PCResult n) (a c b : Fin n) :
    Decidable (r.IsCollider a c b) := by
  unfold IsCollider
  infer_instance

end PCResult

/-- **V-structure orientation theorem** (MIT 6.S091 Lecture 5, Theorem 5.1, orientation phase):
for a Markov, adjacency-faithful and orientation-faithful oracle, the collider rule on the
adjacency-phase output orients exactly the v-structures of the graph of `b`. -/
theorem pcAdjacency_isCollider_iff {b : BayesNet α n} {O : CIOracle n} (hM : b.MarkovOracle O)
    (hA : b.AdjacencyFaithful O) (hOr : b.OrientationFaithful O) (a c d : Fin n) :
    (pcAdjacency O).IsCollider a c d ↔ IsVStructure b.toPa a c d := by
  have hskel : (pcAdjacency O).skeleton = b.skeleton :=
    pcAdjacency_skeleton_eq hM hA
  have adj_iff : ∀ {i j : Fin n}, (pcAdjacency O).skeleton.Adj i j ↔ b.Adj i j := by
    intro i j
    rw [hskel]
    exact BayesNet.skeleton_adj b
  have bAdj_symm : ∀ {i j : Fin n}, b.Adj i j → b.Adj j i := by
    intro i j h
    have hsk : (pcAdjacency O).skeleton.Adj i j := adj_iff.mpr h
    have hsks : (pcAdjacency O).skeleton.Adj j i := SimpleGraph.adj_symm _ hsk
    exact adj_iff.mp hsks
  unfold PCResult.IsCollider IsVStructure
  constructor
  · intro h
    obtain ⟨h_ac_sk, h_cd_sk, h_ne, h_nadj_sk, h_c_notmem⟩ := h
    have h_ac : b.Adj a c := adj_iff.mp h_ac_sk
    have h_cd : b.Adj c d := adj_iff.mp h_cd_sk
    have h_nadj : ¬ b.Adj a d := fun hh => h_nadj_sk (adj_iff.mpr hh)
    have h_nadj_toPa : ¬ Adjacent b.toPa a d :=
      fun hh => h_nadj ((adjacent_toPa_iff b).mp hh)
    rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
    · obtain ⟨h_indep, h_a_nm, h_d_nm⟩ := pcAdjacency_sepset O h_lt h_nadj_sk
      have h_iff := hOr a c d ((pcAdjacency O).sepset a d) h_ac h_cd h_ne h_nadj h_a_nm h_d_nm h_indep
      have h_edges := h_iff.mpr h_c_notmem
      have h_mem_a : a ∈ b.toPa c := (BayesNet.mem_toPa b).mpr h_edges.1
      have h_mem_d : d ∈ b.toPa c := (BayesNet.mem_toPa b).mpr h_edges.2
      exact ⟨h_ne, h_mem_a, h_mem_d, h_nadj_toPa⟩
    · have h_nadj_sk_rev : ¬ (pcAdjacency O).skeleton.Adj d a :=
        fun hh => h_nadj_sk (SimpleGraph.adj_symm _ hh)
      obtain ⟨h_indep_rev, h_d_nm, h_a_nm⟩ := pcAdjacency_sepset O h_gt h_nadj_sk_rev
      have h_dc : b.Adj d c := bAdj_symm h_cd
      have h_ca : b.Adj c a := bAdj_symm h_ac
      have h_ne_rev : d ≠ a := Ne.symm h_ne
      have h_nadj_rev : ¬ b.Adj d a := fun hh => h_nadj (bAdj_symm hh)
      have h_iff_rev := hOr d c a ((pcAdjacency O).sepset d a) h_dc h_ca h_ne_rev h_nadj_rev h_d_nm h_a_nm h_indep_rev
      have h_symm_eq : (pcAdjacency O).sepset d a = (pcAdjacency O).sepset a d :=
        pcAdjacency_sepset_symm O d a
      have h_c_nm_rev : c ∉ (pcAdjacency O).sepset d a := by
        rw [h_symm_eq]
        exact h_c_notmem
      have h_edges_rev := h_iff_rev.mpr h_c_nm_rev
      have h_mem_a : a ∈ b.toPa c := (BayesNet.mem_toPa b).mpr h_edges_rev.2
      have h_mem_d : d ∈ b.toPa c := (BayesNet.mem_toPa b).mpr h_edges_rev.1
      exact ⟨h_ne, h_mem_a, h_mem_d, h_nadj_toPa⟩
  · intro h
    obtain ⟨h_ne, h_mem_a, h_mem_d, h_nadj_toPa⟩ := h
    have h_eac : b.Edge a c := (BayesNet.mem_toPa b).mp h_mem_a
    have h_edc : b.Edge d c := (BayesNet.mem_toPa b).mp h_mem_d
    have h_nadj : ¬ b.Adj a d := fun hh => h_nadj_toPa ((adjacent_toPa_iff b).mpr hh)
    have h_ac : b.Adj a c := by
      unfold BayesNet.Adj
      exact Or.inl h_eac
    have h_cd : b.Adj c d := by
      unfold BayesNet.Adj
      exact Or.inr h_edc
    have h_ac_sk : (pcAdjacency O).skeleton.Adj a c := adj_iff.mpr h_ac
    have h_cd_sk : (pcAdjacency O).skeleton.Adj c d := adj_iff.mpr h_cd
    have h_nadj_sk : ¬ (pcAdjacency O).skeleton.Adj a d := fun hh => h_nadj (adj_iff.mp hh)
    rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
    · obtain ⟨h_indep, h_a_nm, h_d_nm⟩ := pcAdjacency_sepset O h_lt h_nadj_sk
      have h_iff := hOr a c d ((pcAdjacency O).sepset a d) h_ac h_cd h_ne h_nadj h_a_nm h_d_nm h_indep
      have h_c_nm : c ∉ (pcAdjacency O).sepset a d := h_iff.mp ⟨h_eac, h_edc⟩
      exact ⟨h_ac_sk, h_cd_sk, h_ne, h_nadj_sk, h_c_nm⟩
    · have h_nadj_sk_rev : ¬ (pcAdjacency O).skeleton.Adj d a :=
        fun hh => h_nadj_sk (SimpleGraph.adj_symm _ hh)
      obtain ⟨h_indep_rev, h_d_nm, h_a_nm⟩ := pcAdjacency_sepset O h_gt h_nadj_sk_rev
      have h_dc : b.Adj d c := bAdj_symm h_cd
      have h_ca : b.Adj c a := bAdj_symm h_ac
      have h_ne_rev : d ≠ a := Ne.symm h_ne
      have h_nadj_rev : ¬ b.Adj d a := fun hh => h_nadj (bAdj_symm hh)
      have h_iff_rev := hOr d c a ((pcAdjacency O).sepset d a) h_dc h_ca h_ne_rev h_nadj_rev h_d_nm h_a_nm h_indep_rev
      have h_c_nm_rev : c ∉ (pcAdjacency O).sepset d a := h_iff_rev.mp ⟨h_edc, h_eac⟩
      have h_symm_eq : (pcAdjacency O).sepset d a = (pcAdjacency O).sepset a d :=
        pcAdjacency_sepset_symm O d a
      have h_c_nm : c ∉ (pcAdjacency O).sepset a d := by
        rw [← h_symm_eq]
        exact h_c_nm_rev
      exact ⟨h_ac_sk, h_cd_sk, h_ne, h_nadj_sk, h_c_nm⟩

/-- Faithfulness implies orientation-faithfulness. -/
theorem BayesNet.Faithful.orientationFaithful [Fintype β] {b : BayesNet α n}
    {P : (Fin n → β) → ℝ} (h : b.Faithful P) : b.OrientationFaithful (lawOracle P) := by
  unfold BayesNet.OrientationFaithful
  intro i c j S hic hcj hij _hnadj hiS hjS hindep
  have d1 : Disjoint ({i} : Finset (Fin n)) {j} := Finset.disjoint_singleton.mpr hij
  have d2 : Disjoint ({i} : Finset (Fin n)) S := Finset.disjoint_singleton_left.mpr hiS
  have d3 : Disjoint ({j} : Finset (Fin n)) S := Finset.disjoint_singleton_left.mpr hjS
  have hiff := h {i} {j} S d1 d2 d3
  simp only [Finset.coe_singleton] at hiff
  have hsep : b.DSeparated {i} {j} ↑S := hiff.mp hindep
  have hsepPa : DSeparatedPa b.toPa {i} {j} ↑S :=
    (BayesNet.dSeparated_iff_dSeparatedPa_toPa b).mp hsep
  have hac : Adjacent b.toPa i c := (adjacent_toPa_iff b).mpr hic
  have hcb : Adjacent b.toPa c j := (adjacent_toPa_iff b).mpr hcj
  have hcoll := collider_iff_not_mem_of_dSeparatedPa (isAcyclic_toPa b) hac hcb hij hsepPa
  have e1 : b.Edge i c ↔ i ∈ b.toPa c := (BayesNet.mem_toPa b).symm
  have e2 : b.Edge j c ↔ j ∈ b.toPa c := (BayesNet.mem_toPa b).symm
  rw [← Finset.mem_coe, e1, e2]
  exact hcoll

/-- **PC recovers the skeleton and the v-structures** for any law `P` faithful to the graph
of `b`. -/
theorem pc_skeleton_vstructures_of_faithful [Fintype β] {b : BayesNet α n}
    {P : (Fin n → β) → ℝ} (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) (h : b.Faithful P) :
    (pcAdjacency (lawOracle P)).skeleton = b.skeleton ∧
      ∀ a c d, (pcAdjacency (lawOracle P)).IsCollider a c d ↔ IsVStructure b.toPa a c d := by
  exact ⟨pcAdjacency_lawOracle_of_faithful hP0 hP1 h,
    fun a c d => pcAdjacency_isCollider_iff h.markovOracle h.adjacencyFaithful
      h.orientationFaithful a c d⟩

/-- An oracle whose endpoint-free independences are d-separations is orientation-faithful
(Verma–Pearl Lemma 2, per separator). -/
theorem BayesNet.orientationFaithful_of_indep_dSeparated (b : BayesNet α n) {O : CIOracle n}
    (h : ∀ (i j : Fin n) (S : Finset (Fin n)), i ≠ j → i ∉ S → j ∉ S → O.Indep i j S →
      b.DSeparated {i} {j} ↑S) :
    b.OrientationFaithful O := by
  unfold BayesNet.OrientationFaithful
  intro i c j S hic hcj hij _hnadj hiS hjS hindep
  have hsep : b.DSeparated {i} {j} ↑S := h i j S hij hiS hjS hindep
  have hsepPa : DSeparatedPa b.toPa {i} {j} ↑S :=
    (BayesNet.dSeparated_iff_dSeparatedPa_toPa b).mp hsep
  have hac : Adjacent b.toPa i c := (adjacent_toPa_iff b).mpr hic
  have hcb : Adjacent b.toPa c j := (adjacent_toPa_iff b).mpr hcj
  have hcoll := collider_iff_not_mem_of_dSeparatedPa (isAcyclic_toPa b) hac hcb hij hsepPa
  have e1 : b.Edge i c ↔ i ∈ b.toPa c := (BayesNet.mem_toPa b).symm
  have e2 : b.Edge j c ↔ j ∈ b.toPa c := (BayesNet.mem_toPa b).symm
  rw [← Finset.mem_coe, e1, e2]
  exact hcoll

/-- The d-separation oracle is orientation-faithful. -/
theorem BayesNet.orientationFaithful_dsepOracle (b : BayesNet α n) :
    b.OrientationFaithful b.dsepOracle := by
  apply BayesNet.orientationFaithful_of_indep_dSeparated
  intro i j S _ _ _ h
  exact h

/-- With the d-separation oracle of the unknown graph, PC orients exactly its v-structures. -/
theorem pcAdjacency_dsepOracle_isCollider_iff (b : BayesNet α n) (a c d : Fin n) :
    (pcAdjacency b.dsepOracle).IsCollider a c d ↔ IsVStructure b.toPa a c d := by
  exact pcAdjacency_isCollider_iff b.markovOracle_dsepOracle b.adjacencyFaithful_dsepOracle
    b.orientationFaithful_dsepOracle a c d

end Cslib.MachineLearning.GraphicalModels
