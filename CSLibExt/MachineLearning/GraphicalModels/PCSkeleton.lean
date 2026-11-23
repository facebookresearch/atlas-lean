/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.GraphicalModels.BayesianNetwork
public import CSLibExt.MachineLearning.GraphicalModels.CausalBayesNet
public import CSLibExt.MachineLearning.GraphicalModels.GlobalMarkov
public import CSLibExt.MachineLearning.GraphicalModels.Junctions
public import CSLibExt.MachineLearning.GraphicalModels.MarkovBlanket
public import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.FinCases
public import MathlibExt.Probability.FiniteWeight

/-!
# The PC adjacency phase over an abstract independence oracle

The deterministic population PC adjacency phase (Spirtes–Glymour–Scheines; Pearl)
run against an abstract conditional-independence oracle: starting from the complete
graph, delete the edge between `i` and `j` at the first conditioning set, drawn from
the current estimated neighbourhoods in a fixed order, that the oracle declares
separating, and record that set. Under the Markov and adjacency-faithfulness
hypotheses the returned graph is the skeleton of the true network and every recorded
separating set really separates. The d-separation oracle of a network and the
independence oracle of its joint law (by the global Markov property) instantiate the
interface. An XOR collider network, whose law is Markov to its graph but not
adjacency-faithful, shows the faithfulness hypothesis cannot be dropped: the phase
deletes a true edge.

Conventions: oracle queries are issued only in the fixed endpoint-free order
(`i < j`, endpoints outside the conditioning set); separating sets are stored
symmetrically; the search is deterministic.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset MetaMathlibExt.FiniteWeight

variable {α β : Type*} {n : ℕ}

/-! ### Oracles -/

/-- A conditional-independence oracle on the variables `Fin n`: `Indep i j S` is the oracle's
answer to the query "is `X i` independent of `X j` given `X_S`?", and every query has a
decidable answer. No symmetry and no relation to any graph is assumed. -/
structure CIOracle (n : ℕ) where
  /-- The oracle's answer to the query `X i ⫫ X j | X_S`. -/
  Indep : Fin n → Fin n → Finset (Fin n) → Prop
  /-- Every query has a decidable answer. -/
  decIndep : ∀ i j S, Decidable (Indep i j S)

instance CIOracle.instDecidableIndep (O : CIOracle n) (i j : Fin n) (S : Finset (Fin n)) :
    Decidable (O.Indep i j S) :=
  O.decIndep i j S

/-- A symmetric oracle answers the queries `(i, j, S)` and `(j, i, S)` alike. -/
def CIOracle.Symmetric (O : CIOracle n) : Prop :=
  ∀ i j S, O.Indep i j S → O.Indep j i S

/-- The population oracle of a weight `P`: the actual conditional independence
`X i ⫫ X j | X_S` under `P` (`CondIndep`, cross-multiplied). Its answers are decided
classically, so this oracle is a specification, not an executable tester. -/
noncomputable def lawOracle [Fintype β] (P : (Fin n → β) → ℝ) : CIOracle n where
  Indep i j S := CondIndep P {i} {j} ↑S
  decIndep _ _ _ := Classical.dec _

namespace BayesNet

variable (b : BayesNet α n)

/-- The skeleton of the graph of `b`: `i` and `j` are adjacent exactly when `b.Adj i j`. -/
def skeleton : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel b.Edge

/-- The d-separation oracle of the graph of `b`. -/
noncomputable def dsepOracle : CIOracle n where
  Indep i j S := b.DSeparated {i} {j} ↑S
  decIndep _ _ _ := Classical.dec _

/-- **Markov oracle**: every d-separation of distinct endpoints by an endpoint-free set is
declared an independence. Both endpoint orders are quantified. -/
def MarkovOracle (O : CIOracle n) : Prop :=
  ∀ (i j : Fin n) (S : Finset (Fin n)), i ≠ j → i ∉ S → j ∉ S →
    b.DSeparated {i} {j} ↑S → O.Indep i j S

/-- **Adjacency-faithfulness** of an oracle (MIT 6.S091 Lecture 5, Definition 5.2): every
adjacent pair of the graph is declared dependent given every set of other vertices. Both
endpoint orders are quantified. For `lawOracle P` this is adjacency-faithfulness of `P`. -/
def AdjacencyFaithful (O : CIOracle n) : Prop :=
  ∀ (i j : Fin n) (S : Finset (Fin n)), b.Adj i j → i ∉ S → j ∉ S → ¬ O.Indep i j S

/-- **Faithfulness** of a weight `P` to the graph of `b` (MIT 6.S091 Lecture 5,
Definition 5.1; Kalisch and Bühlmann 2007, Section 2.1), with the pairwise-disjoint convention:
for pairwise disjoint sets of nodes, conditional independence under `P` holds exactly when
d-separation does. -/
def Faithful [Fintype β] (P : (Fin n → β) → ℝ) : Prop :=
  ∀ X Y Z : Finset (Fin n), Disjoint X Y → Disjoint X Z → Disjoint Y Z →
    (CondIndep P ↑X ↑Y ↑Z ↔ b.DSeparated ↑X ↑Y ↑Z)

end BayesNet

/-! ### The deterministic population PC adjacency phase -/

/-- The state and output of the adjacency phase: the estimated adjacency and the recorded
separating sets, both stored symmetrically. -/
structure PCResult (n : ℕ) where
  /-- The estimated adjacency. -/
  adj : Fin n → Fin n → Bool
  /-- The recorded separating set of a removed pair. -/
  sepset : Fin n → Fin n → Finset (Fin n)

namespace PCResult

/-- The complete graph with empty separating sets: the start of the adjacency phase. -/
def complete (n : ℕ) : PCResult n where
  adj i j := decide (i ≠ j)
  sepset _ _ := ∅

/-- The estimated skeleton. -/
def skeleton (r : PCResult n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => r.adj i j = true

instance instDecidableRelSkeletonAdj (r : PCResult n) : DecidableRel r.skeleton.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ (r.adj i j = true ∨ r.adj j i = true)))

/-- The candidate conditioning sets of size `d` drawn from the current neighbours of `u` other
than `i` and `j`: the `d`-element sublists (`List.sublistsLen`) of those neighbours listed in
`List.finRange` order. -/
def sideCandidates (r : PCResult n) (u i j : Fin n) (d : ℕ) : List (Finset (Fin n)) :=
  (((List.finRange n).filter fun k => r.adj u k && decide (k ≠ i) && decide (k ≠ j)).sublistsLen
    d).map List.toFinset

/-- The candidate conditioning sets of size `d` for the pair `(i, j)`, in the frozen order:
those drawn from the neighbours of `i`, then those drawn from the neighbours of `j`. -/
def candidates (r : PCResult n) (i j : Fin n) (d : ℕ) : List (Finset (Fin n)) :=
  r.sideCandidates i i j d ++ r.sideCandidates j i j d

end PCResult

/-- The first candidate, in the frozen order, that the oracle declares a separating set for the
ordered query `(i, j)`. -/
def pcFirstSep (O : CIOracle n) (r : PCResult n) (i j : Fin n) (d : ℕ) :
    Option (Finset (Fin n)) :=
  (r.candidates i j d).find? fun S => decide (O.Indep i j S)

/-- One step of round `d` at the pair `p = (i, j)`, visited with `i < j`: if `i` and `j` are
still adjacent and some candidate of size `d` separates them, delete the edge in both
directions and record that candidate as the separating set of `(i, j)` and of `(j, i)`. -/
def pcStep (O : CIOracle n) (d : ℕ) (r : PCResult n) (p : Fin n × Fin n) : PCResult n :=
  if r.adj p.1 p.2 then
    match pcFirstSep O r p.1 p.2 d with
    | some S =>
      { adj := fun u v => if (u = p.1 ∧ v = p.2) ∨ (u = p.2 ∧ v = p.1) then false else r.adj u v
        sepset := fun u v =>
          if (u = p.1 ∧ v = p.2) ∨ (u = p.2 ∧ v = p.1) then S else r.sepset u v }
    | none => r
  else r

/-- The pairs `(i, j)` with `i < j`, in lexicographic order. -/
def pcPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => decide (i < j)).map fun j => (i, j)

/-- Round `d` of the adjacency phase: one step at every pair, on the current estimate. -/
def pcRound (O : CIOracle n) (r : PCResult n) (d : ℕ) : PCResult n :=
  (pcPairs n).foldl (pcStep O d) r

/-- **The population PC adjacency phase** (MIT 6.S091 Lecture 5, Algorithm 1; Kalisch and
Bühlmann 2007, Algorithm 1), made deterministic: rounds `d = 0, …, n - 1` from the complete
graph; rounds past the largest neighbourhood are no-ops. -/
def pcAdjacency (O : CIOracle n) : PCResult n :=
  (List.range n).foldl (pcRound O) (PCResult.complete n)

/-! ### Targets: graph lemmas and faithfulness -/

/-- The skeleton of a network is its adjacency. -/
theorem BayesNet.skeleton_adj (b : BayesNet α n) {i j : Fin n} :
    b.skeleton.Adj i j ↔ b.Adj i j := by
  rw [BayesNet.skeleton, BayesNet.Adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro (h | h)
    · exact ⟨ne_of_lt (h.lt b), Or.inl h⟩
    · exact ⟨ne_of_gt (h.lt b), Or.inr h⟩

/-- Adjacent nodes are never d-separated, whatever the conditioning set: the two-node path has
no interior triple to block. -/
theorem BayesNet.not_dSeparated_of_adj (b : BayesNet α n) {i j : Fin n} (h : b.Adj i j)
    (Z : Set (Fin n)) : ¬ b.DSeparated {i} {j} Z := by
  have hne : i ≠ j := by
    rcases h with e | e
    · exact ne_of_lt (e.lt b)
    · exact ne_of_gt (e.lt b)
  have hnodup : [i, j].Nodup :=
    List.nodup_cons.2 ⟨by simpa using hne, List.nodup_singleton j⟩
  have hchain : [i, j].IsChain b.Adj := List.isChain_pair.2 h
  have hpath : b.IsPath i j [i, j] := ⟨hnodup, hchain, rfl, rfl⟩
  intro hd
  have hb := hd i (Set.mem_singleton_iff.mpr rfl) j (Set.mem_singleton_iff.mpr rfl)
    [i, j] hpath
  obtain ⟨k, hk, -⟩ := hb
  simp only [List.length_cons, List.length_nil] at hk
  omega

/-- A faithful weight is a Markov oracle (the law corollary for any `P`, not only `b.joint`). -/
theorem BayesNet.Faithful.markovOracle [Fintype β] {b : BayesNet α n}
    {P : (Fin n → β) → ℝ} (h : b.Faithful P) : b.MarkovOracle (lawOracle P) := by
  intro i j S hij hi hj hd
  have hXY : Disjoint ({i} : Finset (Fin n)) {j} := Finset.disjoint_singleton.2 hij
  have hXZ : Disjoint ({i} : Finset (Fin n)) S := by
    rw [Finset.disjoint_left]
    intro a ha
    simp only [Finset.mem_singleton] at ha
    subst ha
    exact hi
  have hYZ : Disjoint ({j} : Finset (Fin n)) S := by
    rw [Finset.disjoint_left]
    intro a ha
    simp only [Finset.mem_singleton] at ha
    subst ha
    exact hj
  have hiff := h {i} {j} S hXY hXZ hYZ
  simp only [Finset.coe_singleton] at hiff
  exact hiff.mpr hd

/-- Faithfulness implies adjacency-faithfulness. -/
theorem BayesNet.Faithful.adjacencyFaithful [Fintype β] {b : BayesNet α n}
    {P : (Fin n → β) → ℝ} (h : b.Faithful P) : b.AdjacencyFaithful (lawOracle P) := by
  intro i j S hadj hi hj hindep
  have hij : i ≠ j := by
    rcases hadj with e | e
    · exact ne_of_lt (e.lt b)
    · exact ne_of_gt (e.lt b)
  have hXY : Disjoint ({i} : Finset (Fin n)) {j} := Finset.disjoint_singleton.2 hij
  have hXZ : Disjoint ({i} : Finset (Fin n)) S := by
    rw [Finset.disjoint_left]
    intro a ha
    simp only [Finset.mem_singleton] at ha
    subst ha
    exact hi
  have hYZ : Disjoint ({j} : Finset (Fin n)) S := by
    rw [Finset.disjoint_left]
    intro a ha
    simp only [Finset.mem_singleton] at ha
    subst ha
    exact hj
  have hiff := h {i} {j} S hXY hXZ hYZ
  simp only [Finset.coe_singleton] at hiff
  exact b.not_dSeparated_of_adj hadj ↑S (hiff.mp hindep)

/-! ### Targets: skeleton recovery and the separating-set interface -/

/-- The output adjacency matrix is symmetric. -/
private theorem adj_symm_pcAdjacency {O : CIOracle n} (i j : Fin n) :
    (pcAdjacency O).adj i j = (pcAdjacency O).adj j i := by
  have step : ∀ (d : ℕ) (r : PCResult n) (p : Fin n × Fin n),
      (∀ a b, r.adj a b = r.adj b a) →
      (∀ a b, (pcStep O d r p).adj a b = (pcStep O d r p).adj b a) := by
    intro d r p hr a b
    unfold pcStep
    by_cases hb : r.adj p.1 p.2 = true
    · rw [ite_eq_left hb]
      cases hm : pcFirstSep O r p.1 p.2 d with
      | some S =>
        dsimp only
        by_cases h : (a = p.1 ∧ b = p.2) ∨ (a = p.2 ∧ b = p.1)
        · have h' : (b = p.1 ∧ a = p.2) ∨ (b = p.2 ∧ a = p.1) :=
            h.elim (fun hh => Or.inr ⟨hh.2, hh.1⟩) (fun hh => Or.inl ⟨hh.2, hh.1⟩)
          simp only [ite_eq_left h, ite_eq_left h']
        · have h' : ¬ ((b = p.1 ∧ a = p.2) ∨ (b = p.2 ∧ a = p.1)) :=
            fun hh => h (hh.elim (fun kk => Or.inr ⟨kk.2, kk.1⟩) (fun kk => Or.inl ⟨kk.2, kk.1⟩))
          simp only [ite_eq_right h, ite_eq_right h']
          exact hr a b
      | none =>
        dsimp only
        exact hr a b
    · rw [ite_eq_right hb]
      exact hr a b
  have round : ∀ (d : ℕ) (r : PCResult n),
      (∀ a b, r.adj a b = r.adj b a) →
      (∀ a b, (pcRound O r d).adj a b = (pcRound O r d).adj b a) := by
    intro d r hr
    unfold pcRound
    have gen : ∀ (l : List (Fin n × Fin n)) (s : PCResult n),
        (∀ a b, s.adj a b = s.adj b a) →
        (∀ a b, (l.foldl (pcStep O d) s).adj a b = (l.foldl (pcStep O d) s).adj b a) := by
      intro l
      induction l with
      | nil => intro s hs a b; exact hs a b
      | cons p ps ih => intro s hs; exact ih _ (step d s p hs)
    exact gen (pcPairs n) r hr
  have outer : ∀ (l : List ℕ) (s : PCResult n),
      (∀ a b, s.adj a b = s.adj b a) →
      (∀ a b, (l.foldl (pcRound O) s).adj a b = (l.foldl (pcRound O) s).adj b a) := by
    intro l
    induction l with
    | nil => intro s hs a b; exact hs a b
    | cons d ds ih => intro s hs; exact ih _ (round d s hs)
  have hbase : ∀ a b, (PCResult.complete n).adj a b = (PCResult.complete n).adj b a := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rfl
    · have h1 : decide (a ≠ b) = true := decide_eq_true hab
      have h2 : decide (b ≠ a) = true := decide_eq_true (Ne.symm hab)
      show decide (a ≠ b) = decide (b ≠ a)
      rw [h1, h2]
  unfold pcAdjacency
  exact outer (List.range n) (PCResult.complete n) hbase i j

private theorem pcPairs_mem_lt {p : Fin n × Fin n} (hm : p ∈ pcPairs n) : p.1 < p.2 := by
  unfold pcPairs at hm
  obtain ⟨i, -, hmem⟩ := List.mem_flatMap.1 hm
  obtain ⟨j, hjF, hp⟩ := List.mem_map.1 hmem
  obtain ⟨-, hpred⟩ := List.mem_filter.1 hjF
  have hij : i < j := of_decide_eq_true hpred
  rw [← hp]
  exact hij

private theorem mem_sideCandidates_endpoint_free {r : PCResult n} {u i j : Fin n} {d : ℕ}
    {S : Finset (Fin n)} (hm : S ∈ r.sideCandidates u i j d) : i ∉ S ∧ j ∉ S := by
  unfold PCResult.sideCandidates at hm
  obtain ⟨t, hmem, hteq⟩ := List.mem_map.1 hm
  have hsub : t.Sublist
      ((List.finRange n).filter fun k => r.adj u k && decide (k ≠ i) && decide (k ≠ j)) :=
    (List.mem_sublistsLen.1 hmem).1
  have hsubset := hsub.subset
  constructor
  · intro hiS
    rw [← hteq] at hiS
    have hiT : i ∈ t := List.mem_toFinset.1 hiS
    have hiF := hsubset hiT
    obtain ⟨-, hpred⟩ := List.mem_filter.1 hiF
    have hdi : decide (i ≠ i) = false := by simp
    rw [hdi] at hpred
    simp at hpred
  · intro hjS
    rw [← hteq] at hjS
    have hjT : j ∈ t := List.mem_toFinset.1 hjS
    have hjF := hsubset hjT
    obtain ⟨-, hpred⟩ := List.mem_filter.1 hjF
    have hdj : decide (j ≠ j) = false := by simp
    rw [hdj] at hpred
    simp at hpred

private theorem mem_candidates_endpoint_free {r : PCResult n} {i j : Fin n} {d : ℕ}
    {S : Finset (Fin n)} (hm : S ∈ r.candidates i j d) : i ∉ S ∧ j ∉ S := by
  unfold PCResult.candidates at hm
  rcases List.mem_append.1 hm with hmem | hmem
  · exact mem_sideCandidates_endpoint_free hmem
  · exact mem_sideCandidates_endpoint_free hmem

private theorem pcStep_pres_valid {O : CIOracle n} {d : ℕ} {r : PCResult n} {p : Fin n × Fin n}
    (hlt : p.1 < p.2)
    (hv : ∀ i j, i < j → (r.adj i j = false) →
      O.Indep i j (r.sepset i j) ∧ i ∉ r.sepset i j ∧ j ∉ r.sepset i j) :
    ∀ i j, i < j → ((pcStep O d r p).adj i j = false) →
      O.Indep i j ((pcStep O d r p).sepset i j) ∧
        i ∉ (pcStep O d r p).sepset i j ∧ j ∉ (pcStep O d r p).sepset i j := by
  intro i j hij hf
  unfold pcStep at hf ⊢
  by_cases hb : r.adj p.1 p.2 = true
  · simp only [ite_eq_left hb] at hf ⊢
    cases hm : pcFirstSep O r p.1 p.2 d with
    | some S =>
      rw [hm] at hf
      dsimp only at hf ⊢
      by_cases h : (i = p.1 ∧ j = p.2) ∨ (i = p.2 ∧ j = p.1)
      · simp only [ite_eq_left h] at hf ⊢
        unfold pcFirstSep at hm
        have hmem : S ∈ r.candidates p.1 p.2 d := List.mem_of_find?_eq_some hm
        have hpred := List.find?_some hm
        have hindep : O.Indep p.1 p.2 S := of_decide_eq_true hpred
        have hfree : p.1 ∉ S ∧ p.2 ∉ S := mem_candidates_endpoint_free hmem
        rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · subst hi
          subst hj
          exact ⟨hindep, hfree.1, hfree.2⟩
        · subst hi
          subst hj
          exact absurd (lt_trans hlt hij) (lt_irrefl _)
      · simp only [ite_eq_right h] at hf ⊢
        exact hv i j hij hf
    | none =>
      rw [hm] at hf
      dsimp only at hf ⊢
      exact hv i j hij hf
  · simp only [ite_eq_right hb] at hf ⊢
    exact hv i j hij hf

private theorem pcRound_pres_valid {O : CIOracle n} {d : ℕ} {r : PCResult n}
    (hv : ∀ i j, i < j → (r.adj i j = false) →
      O.Indep i j (r.sepset i j) ∧ i ∉ r.sepset i j ∧ j ∉ r.sepset i j) :
    ∀ i j, i < j → ((pcRound O r d).adj i j = false) →
      O.Indep i j ((pcRound O r d).sepset i j) ∧
        i ∉ (pcRound O r d).sepset i j ∧ j ∉ (pcRound O r d).sepset i j := by
  unfold pcRound
  have gen : ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, p.1 < p.2) → ∀ (s : PCResult n),
      (∀ i j, i < j → (s.adj i j = false) →
        O.Indep i j (s.sepset i j) ∧ i ∉ s.sepset i j ∧ j ∉ s.sepset i j) →
      (∀ i j, i < j → ((l.foldl (pcStep O d) s).adj i j = false) →
        O.Indep i j ((l.foldl (pcStep O d) s).sepset i j) ∧
          i ∉ (l.foldl (pcStep O d) s).sepset i j ∧ j ∉ (l.foldl (pcStep O d) s).sepset i j) := by
    intro l
    induction l with
    | nil => intro hl s hs i j hij hf; exact hs i j hij hf
    | cons p ps ih =>
      intro hl s hs i j hij hf
      exact ih (fun q hq => hl q (List.mem_cons.2 (Or.inr hq)))
        (pcStep O d s p) (pcStep_pres_valid (hl p (List.mem_cons.2 (Or.inl rfl))) hs)
        i j hij hf
  exact gen (pcPairs n) (fun p hp => pcPairs_mem_lt hp) r hv

private theorem complete_valid (n : ℕ) (O : CIOracle n) (i j : Fin n) (hij : i < j)
    (hf : (PCResult.complete n).adj i j = false) :
    O.Indep i j ((PCResult.complete n).sepset i j) ∧
      i ∉ (PCResult.complete n).sepset i j ∧ j ∉ (PCResult.complete n).sepset i j := by
  have hne : i ≠ j := ne_of_lt hij
  have htrue : decide (i ≠ j) = true := decide_eq_true hne
  have hfalse : decide (i ≠ j) = false := hf
  rw [htrue] at hfalse
  exact absurd hfalse (by decide)

private theorem exists_cons_split_of_mem {α : Type*} (l : List α) (a : α) :
    a ∈ l → ∃ l₁ l₂, l = l₁ ++ a :: l₂ := by
  induction l with
  | nil =>
    intro h
    exact absurd h (by simp)
  | cons b bs ih =>
    intro h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨[], bs, rfl⟩
    · obtain ⟨l₁, l₂, rfl⟩ := ih h
      exact ⟨b :: l₁, l₂, rfl⟩

private theorem mem_pcPairs_of_lt {i j : Fin n} (hij : i < j) : (i, j) ∈ pcPairs n := by
  unfold pcPairs
  exact List.mem_flatMap.2 ⟨i, List.mem_finRange i, List.mem_map.2 ⟨j,
    List.mem_filter.2 ⟨List.mem_finRange j, decide_eq_true hij⟩, rfl⟩⟩

private theorem pcStep_mono_false {O : CIOracle n} {d : ℕ} {r : PCResult n} {p : Fin n × Fin n}
    {a c : Fin n} (hf : r.adj a c = false) : (pcStep O d r p).adj a c = false := by
  unfold pcStep
  by_cases hb : r.adj p.1 p.2 = true
  · simp only [ite_eq_left hb]
    cases hm : pcFirstSep O r p.1 p.2 d with
    | some S =>
      dsimp only
      by_cases h : (a = p.1 ∧ c = p.2) ∨ (a = p.2 ∧ c = p.1)
      · simp only [ite_eq_left h]
      · simp only [ite_eq_right h]
        exact hf
    | none =>
      dsimp only
      exact hf
  · simp only [ite_eq_right hb]
    exact hf

private theorem foldl_steps_mono_false {O : CIOracle n} {d : ℕ} :
    ∀ (l : List (Fin n × Fin n)) (s : PCResult n) {a c : Fin n},
      s.adj a c = false → (l.foldl (pcStep O d) s).adj a c = false := by
  intro l
  induction l with
  | nil =>
    intro s a c hf
    exact hf
  | cons p ps ih =>
    intro s a c hf
    simp only [List.foldl_cons]
    exact ih _ (pcStep_mono_false hf)

private theorem pcRound_mono_false {O : CIOracle n} {d : ℕ} {r : PCResult n} {a c : Fin n}
    (hf : r.adj a c = false) : (pcRound O r d).adj a c = false := by
  unfold pcRound
  exact foldl_steps_mono_false _ _ hf

private theorem foldl_rounds_mono_false {O : CIOracle n} :
    ∀ (l : List ℕ) (s : PCResult n) {a c : Fin n},
      s.adj a c = false → (l.foldl (pcRound O) s).adj a c = false := by
  intro l
  induction l with
  | nil =>
    intro s a c hf
    exact hf
  | cons d ds ih =>
    intro s a c hf
    simp only [List.foldl_cons]
    exact ih _ (pcRound_mono_false hf)

private theorem pcStep_pres_true {b : BayesNet α n} {O : CIOracle n}
    (hA : b.AdjacencyFaithful O) {d : ℕ} {r : PCResult n} {p : Fin n × Fin n}
    (hv : ∀ x y, b.Adj x y → r.adj x y = true) {a c : Fin n} (h : b.Adj a c) :
    (pcStep O d r p).adj a c = true := by
  unfold pcStep
  by_cases hb : r.adj p.1 p.2 = true
  · simp only [ite_eq_left hb]
    cases hm : pcFirstSep O r p.1 p.2 d with
    | some S =>
      dsimp only
      by_cases hcase : (a = p.1 ∧ c = p.2) ∨ (a = p.2 ∧ c = p.1)
      · exfalso
        have hmem : S ∈ r.candidates p.1 p.2 d := List.mem_of_find?_eq_some hm
        have hpred := List.find?_some hm
        have hindep : O.Indep p.1 p.2 S := of_decide_eq_true hpred
        have hfree : p.1 ∉ S ∧ p.2 ∉ S := mem_candidates_endpoint_free hmem
        have hadj : b.Adj p.1 p.2 := by
          rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h
          · unfold BayesNet.Adj at h ⊢
            exact Or.comm.mp h
        exact hA p.1 p.2 S hadj hfree.1 hfree.2 hindep
      · simp only [ite_eq_right hcase]
        exact hv a c h
    | none =>
      dsimp only
      exact hv a c h
  · simp only [ite_eq_right hb]
    exact hv a c h

private theorem foldl_steps_pres_true {b : BayesNet α n} {O : CIOracle n}
    (hA : b.AdjacencyFaithful O) {d : ℕ} :
    ∀ (l : List (Fin n × Fin n)) (s : PCResult n),
      (∀ x y, b.Adj x y → s.adj x y = true) →
      ∀ x y, b.Adj x y → (l.foldl (pcStep O d) s).adj x y = true := by
  intro l
  induction l with
  | nil =>
    intro s hs x y h
    exact hs x y h
  | cons p ps ih =>
    intro s hs x y h
    simp only [List.foldl_cons]
    exact ih _ (fun x y hxy => pcStep_pres_true hA hs hxy) x y h

private theorem pcRound_pres_true {b : BayesNet α n} {O : CIOracle n}
    (hA : b.AdjacencyFaithful O) {d : ℕ} {r : PCResult n}
    (hv : ∀ x y, b.Adj x y → r.adj x y = true) :
    ∀ x y, b.Adj x y → (pcRound O r d).adj x y = true := by
  intro x y h
  unfold pcRound
  exact foldl_steps_pres_true hA _ _ hv x y h

private theorem foldl_rounds_pres_true {b : BayesNet α n} {O : CIOracle n}
    (hA : b.AdjacencyFaithful O) :
    ∀ (l : List ℕ) (s : PCResult n),
      (∀ x y, b.Adj x y → s.adj x y = true) →
      ∀ x y, b.Adj x y → (l.foldl (pcRound O) s).adj x y = true := by
  intro l
  induction l with
  | nil =>
    intro s hs x y h
    exact hs x y h
  | cons d ds ih =>
    intro s hs x y h
    simp only [List.foldl_cons]
    exact ih _ (pcRound_pres_true hA hs) x y h

private theorem complete_pres_true {b : BayesNet α n} {x y : Fin n} (h : b.Adj x y) :
    (PCResult.complete n).adj x y = true := by
  have hne : x ≠ y := by
    rcases h with e | e
    · exact ne_of_lt (e.lt b)
    · exact ne_of_gt (e.lt b)
  show decide (x ≠ y) = true
  exact decide_eq_true hne

private theorem mem_map_toFinset_sublistsLen {L : List (Fin n)} (hnd : L.Nodup)
    {Z : Finset (Fin n)} {d : ℕ} (hsub : ∀ k ∈ Z, k ∈ L) (hcard : Z.card = d) :
    Z ∈ (L.sublistsLen d).map List.toFinset := by
  have htsub : (L.filter (fun k => decide (k ∈ Z))).Sublist L := List.filter_sublist
  have htnd : (L.filter (fun k => decide (k ∈ Z))).Nodup := htsub.nodup hnd
  have hteq : (L.filter (fun k => decide (k ∈ Z))).toFinset = Z := by
    ext k
    simp only [List.mem_toFinset, List.mem_filter]
    constructor
    · intro h
      exact of_decide_eq_true h.2
    · intro hk
      exact ⟨hsub k hk, decide_eq_true hk⟩
  have hlen : (L.filter (fun k => decide (k ∈ Z))).length = d := by
    have h := List.toFinset_card_of_nodup htnd
    rw [hteq, hcard] at h
    exact h.symm
  have hmem : L.filter (fun k => decide (k ∈ Z)) ∈ L.sublistsLen d :=
    List.mem_sublistsLen.2 ⟨htsub, hlen⟩
  exact List.mem_map.2 ⟨_, hmem, hteq⟩

private theorem mem_sideCandidates_of_subset {r : PCResult n} {u i j : Fin n}
    {Z : Finset (Fin n)} {d : ℕ}
    (hadj : ∀ k ∈ Z, r.adj u k = true)
    (hki : ∀ k ∈ Z, k ≠ i) (hkj : ∀ k ∈ Z, k ≠ j)
    (hcard : Z.card = d) : Z ∈ r.sideCandidates u i j d := by
  unfold PCResult.sideCandidates
  refine mem_map_toFinset_sublistsLen ?_ ?_ hcard
  · exact List.filter_sublist.nodup (List.nodup_finRange n)
  · intro k hk
    simp only [List.mem_filter]
    refine ⟨List.mem_finRange k, ?_⟩
    simp [hadj k hk, decide_eq_true (hki k hk), decide_eq_true (hkj k hk)]

private theorem coe_parents (b : BayesNet α n) (w : Fin n) :
    (↑(Finset.univ.filter (fun k => b.Edge k w)) : Set (Fin n)) = {k | b.Edge k w} := by
  ext k
  simp [Finset.coe_filter]

private theorem dsep_parents_left {b : BayesNet α n} {i j : Fin n}
    (hnd : ¬ b.IsDescendant i j) (hne : ¬ b.Edge j i) :
    b.DSeparated {i} {j} ↑(Finset.univ.filter (fun k => b.Edge k i)) := by
  rw [coe_parents b i]
  intro x hx y hy p hp
  simp only [Set.mem_singleton_iff] at hx hy
  rw [hx, hy] at hp
  exact b.dSeparated_localMarkov i i (Set.mem_singleton_iff.mpr rfl) j ⟨hnd, hne⟩ p hp

private theorem dsep_parents_right {b : BayesNet α n} {i j : Fin n}
    (hnd : ¬ b.IsDescendant j i) (hne : ¬ b.Edge i j) :
    b.DSeparated {i} {j} ↑(Finset.univ.filter (fun k => b.Edge k j)) := by
  rw [coe_parents b j]
  have h : b.DSeparated {j} {i} {k | b.Edge k j} := by
    intro x hx y hy p hp
    simp only [Set.mem_singleton_iff] at hx hy
    rw [hx, hy] at hp
    exact b.dSeparated_localMarkov j j (Set.mem_singleton_iff.mpr rfl) i ⟨hnd, hne⟩ p hp
  exact h.symm

private theorem card_filter_parents_lt (b : BayesNet α n) (w v : Fin n)
    (hvw : v ∉ Finset.univ.filter (fun k => b.Edge k w)) :
    (Finset.univ.filter (fun k => b.Edge k w)).card < n := by
  have hsub : Finset.univ.filter (fun k => b.Edge k w) ⊆ Finset.univ.erase v := by
    intro k hk
    obtain ⟨-, hk⟩ := Finset.mem_filter.1 hk
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ k⟩
    intro hkv
    apply hvw
    rw [← hkv]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ k, hk⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin] at hle
  have hnpos : 0 < n := by
    have h2 := v.2
    omega
  omega

private theorem pcStep_visit_false {O : CIOracle n} {d : ℕ} {s : PCResult n} {i j : Fin n}
    (hsep : ∃ Z, O.Indep i j Z ∧ Z ∈ s.candidates i j d) :
    (pcStep O d s (i, j)).adj i j = false := by
  unfold pcStep
  dsimp only
  by_cases hb : s.adj i j = true
  · simp only [ite_eq_left hb]
    obtain ⟨Z, hindep, hmem⟩ := hsep
    cases hm : pcFirstSep O s i j d with
    | some S =>
      dsimp only
      have hcond : True ∧ True ∨ i = j ∧ j = i := Or.inl ⟨trivial, trivial⟩
      simp only [ite_eq_left hcond]
    | none =>
      have hcon := (List.find?_eq_none.1 hm) Z hmem
      simp only [decide_eq_true hindep] at hcon
      exact absurd hcon (by decide)
  · simp only [ite_eq_right hb]
    exact Bool.eq_false_of_ne_true hb

/-- A non-edge `i < j` is deleted by the adjacency phase. -/
private theorem adjFalse_of_not_adj_lt {b : BayesNet α n} {O : CIOracle n}
    (hM : b.MarkovOracle O) (hA : b.AdjacencyFaithful O) {i j : Fin n} (hlt : i < j)
    (h : ¬ b.Adj i j) : (pcAdjacency O).adj i j = false := by
  by_cases hdesc : b.IsDescendant i j
  · have hni : ¬ b.Edge i j := fun e => h (Or.inl e)
    have hnd : ¬ b.IsDescendant j i := fun hd => absurd (hd.le b) (not_le.2 hlt)
    have hdsep : b.DSeparated {i} {j} ↑(Finset.univ.filter (fun k => b.Edge k j)) :=
      dsep_parents_right hnd hni
    have hiZ : i ∉ Finset.univ.filter (fun k => b.Edge k j) := by
      intro hi
      obtain ⟨-, hk⟩ := Finset.mem_filter.1 hi
      exact hni hk
    have hjZ : j ∉ Finset.univ.filter (fun k => b.Edge k j) := by
      intro hj
      obtain ⟨-, hk⟩ := Finset.mem_filter.1 hj
      exact lt_irrefl j (hk.lt b)
    have hindep : O.Indep i j (Finset.univ.filter (fun k => b.Edge k j)) :=
      hM i j _ (ne_of_lt hlt) hiZ hjZ hdsep
    have hcard : (Finset.univ.filter (fun k => b.Edge k j)).card < n :=
      card_filter_parents_lt b j j hjZ
    have hsurv0 : ∀ x y, b.Adj x y → (PCResult.complete n).adj x y = true :=
      fun x y hxy => complete_pres_true hxy
    obtain ⟨rl₁, rl₂, hrfl⟩ :=
      exists_cons_split_of_mem (List.range n) _ (List.mem_range.2 hcard)
    unfold pcAdjacency
    rw [hrfl, List.foldl_append, List.foldl_cons]
    refine foldl_rounds_mono_false _ _ ?_
    obtain ⟨l₁, l₂, hpfl⟩ := exists_cons_split_of_mem (pcPairs n) (i, j) (mem_pcPairs_of_lt hlt)
    show ((pcPairs n).foldl (pcStep O (Finset.univ.filter (fun k => b.Edge k j)).card)
      (rl₁.foldl (pcRound O) (PCResult.complete n))).adj i j = false
    rw [hpfl, List.foldl_append, List.foldl_cons]
    refine foldl_steps_mono_false _ _ ?_
    have hR : ∀ x y, b.Adj x y →
        (rl₁.foldl (pcRound O) (PCResult.complete n)).adj x y = true :=
      foldl_rounds_pres_true hA rl₁ _ hsurv0
    have hs : ∀ x y, b.Adj x y →
        (l₁.foldl (pcStep O (Finset.univ.filter (fun k => b.Edge k j)).card)
          (rl₁.foldl (pcRound O) (PCResult.complete n))).adj x y = true :=
      foldl_steps_pres_true hA l₁ _ hR
    have hside : Finset.univ.filter (fun k => b.Edge k j) ∈ PCResult.sideCandidates
        (l₁.foldl (pcStep O (Finset.univ.filter (fun k => b.Edge k j)).card)
          (rl₁.foldl (pcRound O) (PCResult.complete n))) j i j
        (Finset.univ.filter (fun k => b.Edge k j)).card := by
      refine mem_sideCandidates_of_subset ?_ ?_ ?_ rfl
      · intro k hk
        obtain ⟨-, hke⟩ := Finset.mem_filter.1 hk
        exact hs j k (Or.inr hke)
      · intro k hk hki'
        obtain ⟨-, hke⟩ := Finset.mem_filter.1 hk
        apply hni
        rw [← hki']
        exact hke
      · intro k hk hkj'
        obtain ⟨-, hke⟩ := Finset.mem_filter.1 hk
        have hlt' := hke.lt b
        rw [hkj'] at hlt'
        exact lt_irrefl j hlt'
    have hcand : Finset.univ.filter (fun k => b.Edge k j) ∈ PCResult.candidates
        (l₁.foldl (pcStep O (Finset.univ.filter (fun k => b.Edge k j)).card)
          (rl₁.foldl (pcRound O) (PCResult.complete n))) i j
        (Finset.univ.filter (fun k => b.Edge k j)).card :=
      List.mem_append.2 (Or.inr hside)
    exact pcStep_visit_false ⟨_, hindep, hcand⟩
  · have hne : ¬ b.Edge j i := fun e => h (Or.inr e)
    have hdsep : b.DSeparated {i} {j} ↑(Finset.univ.filter (fun k => b.Edge k i)) :=
      dsep_parents_left hdesc hne
    have hiZ : i ∉ Finset.univ.filter (fun k => b.Edge k i) := by
      intro hi
      obtain ⟨-, hk⟩ := Finset.mem_filter.1 hi
      exact lt_irrefl i (hk.lt b)
    have hjZ : j ∉ Finset.univ.filter (fun k => b.Edge k i) := by
      intro hj
      obtain ⟨-, hk⟩ := Finset.mem_filter.1 hj
      have hlt' := hk.lt b
      exact (not_le.2 hlt) hlt'.le
    have hindep : O.Indep i j (Finset.univ.filter (fun k => b.Edge k i)) :=
      hM i j _ (ne_of_lt hlt) hiZ hjZ hdsep
    have hcard : (Finset.univ.filter (fun k => b.Edge k i)).card < n :=
      card_filter_parents_lt b i i hiZ
    have hsurv0 : ∀ x y, b.Adj x y → (PCResult.complete n).adj x y = true :=
      fun x y hxy => complete_pres_true hxy
    obtain ⟨rl₁, rl₂, hrfl⟩ :=
      exists_cons_split_of_mem (List.range n) _ (List.mem_range.2 hcard)
    unfold pcAdjacency
    rw [hrfl, List.foldl_append, List.foldl_cons]
    refine foldl_rounds_mono_false _ _ ?_
    obtain ⟨l₁, l₂, hpfl⟩ := exists_cons_split_of_mem (pcPairs n) (i, j) (mem_pcPairs_of_lt hlt)
    show ((pcPairs n).foldl (pcStep O (Finset.univ.filter (fun k => b.Edge k i)).card)
      (rl₁.foldl (pcRound O) (PCResult.complete n))).adj i j = false
    rw [hpfl, List.foldl_append, List.foldl_cons]
    refine foldl_steps_mono_false _ _ ?_
    have hR : ∀ x y, b.Adj x y →
        (rl₁.foldl (pcRound O) (PCResult.complete n)).adj x y = true :=
      foldl_rounds_pres_true hA rl₁ _ hsurv0
    have hs : ∀ x y, b.Adj x y →
        (l₁.foldl (pcStep O (Finset.univ.filter (fun k => b.Edge k i)).card)
          (rl₁.foldl (pcRound O) (PCResult.complete n))).adj x y = true :=
      foldl_steps_pres_true hA l₁ _ hR
    have hside : Finset.univ.filter (fun k => b.Edge k i) ∈ PCResult.sideCandidates
        (l₁.foldl (pcStep O (Finset.univ.filter (fun k => b.Edge k i)).card)
          (rl₁.foldl (pcRound O) (PCResult.complete n))) i i j
        (Finset.univ.filter (fun k => b.Edge k i)).card := by
      refine mem_sideCandidates_of_subset ?_ ?_ ?_ rfl
      · intro k hk
        obtain ⟨-, hke⟩ := Finset.mem_filter.1 hk
        exact hs i k (Or.inr hke)
      · intro k hk hki'
        obtain ⟨-, hke⟩ := Finset.mem_filter.1 hk
        have hlt' := hke.lt b
        rw [hki'] at hlt'
        exact lt_irrefl i hlt'
      · intro k hk hkj'
        obtain ⟨-, hke⟩ := Finset.mem_filter.1 hk
        have hlt' := hke.lt b
        rw [hkj'] at hlt'
        exact (not_le.2 hlt) hlt'.le
    have hcand : Finset.univ.filter (fun k => b.Edge k i) ∈ PCResult.candidates
        (l₁.foldl (pcStep O (Finset.univ.filter (fun k => b.Edge k i)).card)
          (rl₁.foldl (pcRound O) (PCResult.complete n))) i j
        (Finset.univ.filter (fun k => b.Edge k i)).card :=
      List.mem_append.2 (Or.inl hside)
    exact pcStep_visit_false ⟨_, hindep, hcand⟩

/-- A true edge survives the adjacency phase. -/
private theorem adjTrue_pcAdjacency {b : BayesNet α n} {O : CIOracle n}
    (hA : b.AdjacencyFaithful O) {i j : Fin n} (h : b.Adj i j) :
    (pcAdjacency O).adj i j = true := by
  unfold pcAdjacency
  exact foldl_rounds_pres_true hA _ _ (fun x y hxy => complete_pres_true hxy) i j h

/-- A deleted pair's recorded separating set is valid. -/
private theorem sepValid_pcAdjacency {O : CIOracle n} (i j : Fin n) (hij : i < j)
    (h : (pcAdjacency O).adj i j = false) :
    O.Indep i j ((pcAdjacency O).sepset i j) ∧ i ∉ (pcAdjacency O).sepset i j ∧
      j ∉ (pcAdjacency O).sepset i j := by
  have outer : ∀ (l : List ℕ) (s : PCResult n),
      (∀ a b, a < b → (s.adj a b = false) →
        O.Indep a b (s.sepset a b) ∧ a ∉ s.sepset a b ∧ b ∉ s.sepset a b) →
      (∀ a b, a < b → ((l.foldl (pcRound O) s).adj a b = false) →
        O.Indep a b ((l.foldl (pcRound O) s).sepset a b) ∧
          a ∉ (l.foldl (pcRound O) s).sepset a b ∧ b ∉ (l.foldl (pcRound O) s).sepset a b) := by
    intro l
    induction l with
    | nil => intro s hs a b hab hf; exact hs a b hab hf
    | cons d ds ih => intro s hs; exact ih (pcRound O s d) (pcRound_pres_valid hs)
  have hbase : ∀ a b, a < b → ((PCResult.complete n).adj a b = false) →
      O.Indep a b ((PCResult.complete n).sepset a b) ∧
        a ∉ (PCResult.complete n).sepset a b ∧ b ∉ (PCResult.complete n).sepset a b :=
    fun a b hab hf => complete_valid n O a b hab hf
  unfold pcAdjacency
  exact outer (List.range n) (PCResult.complete n) hbase i j hij h

/-- Recorded separating sets are stored symmetrically. -/
private theorem sepset_symm_pcAdjacency {O : CIOracle n} (i j : Fin n) :
    (pcAdjacency O).sepset i j = (pcAdjacency O).sepset j i := by
  have step : ∀ (d : ℕ) (r : PCResult n) (p : Fin n × Fin n),
      (∀ a b, r.sepset a b = r.sepset b a) →
      (∀ a b, (pcStep O d r p).sepset a b = (pcStep O d r p).sepset b a) := by
    intro d r p hr a b
    unfold pcStep
    by_cases hb : r.adj p.1 p.2 = true
    · rw [ite_eq_left hb]
      cases hm : pcFirstSep O r p.1 p.2 d with
      | some S =>
        dsimp only
        by_cases h : (a = p.1 ∧ b = p.2) ∨ (a = p.2 ∧ b = p.1)
        · have h' : (b = p.1 ∧ a = p.2) ∨ (b = p.2 ∧ a = p.1) :=
            h.elim (fun hh => Or.inr ⟨hh.2, hh.1⟩) (fun hh => Or.inl ⟨hh.2, hh.1⟩)
          simp only [ite_eq_left h, ite_eq_left h']
        · have h' : ¬ ((b = p.1 ∧ a = p.2) ∨ (b = p.2 ∧ a = p.1)) :=
            fun hh => h (hh.elim (fun kk => Or.inr ⟨kk.2, kk.1⟩) (fun kk => Or.inl ⟨kk.2, kk.1⟩))
          simp only [ite_eq_right h, ite_eq_right h']
          exact hr a b
      | none =>
        dsimp only
        exact hr a b
    · rw [ite_eq_right hb]
      exact hr a b
  have round : ∀ (d : ℕ) (r : PCResult n),
      (∀ a b, r.sepset a b = r.sepset b a) →
      (∀ a b, (pcRound O r d).sepset a b = (pcRound O r d).sepset b a) := by
    intro d r hr
    unfold pcRound
    have gen : ∀ (l : List (Fin n × Fin n)) (s : PCResult n),
        (∀ a b, s.sepset a b = s.sepset b a) →
        (∀ a b, (l.foldl (pcStep O d) s).sepset a b = (l.foldl (pcStep O d) s).sepset b a) := by
      intro l
      induction l with
      | nil => intro s hs a b; exact hs a b
      | cons p ps ih => intro s hs; exact ih _ (step d s p hs)
    exact gen (pcPairs n) r hr
  have outer : ∀ (l : List ℕ) (s : PCResult n),
      (∀ a b, s.sepset a b = s.sepset b a) →
      (∀ a b, (l.foldl (pcRound O) s).sepset a b = (l.foldl (pcRound O) s).sepset b a) := by
    intro l
    induction l with
    | nil => intro s hs a b; exact hs a b
    | cons d ds ih => intro s hs; exact ih _ (round d s hs)
  have hbase : ∀ a b, (PCResult.complete n).sepset a b = (PCResult.complete n).sepset b a := by
    intro a b
    rfl
  unfold pcAdjacency
  exact outer (List.range n) (PCResult.complete n) hbase i j

/-- **Skeleton recovery for an abstract oracle**: if the oracle is a Markov oracle and
adjacency-faithful for the graph of `b`, the adjacency phase returns the skeleton of `b`. -/
theorem pcAdjacency_skeleton_eq {b : BayesNet α n} {O : CIOracle n} (hM : b.MarkovOracle O)
    (hA : b.AdjacencyFaithful O) : (pcAdjacency O).skeleton = b.skeleton := by
  rw [SimpleGraph.ext_iff]
  funext i j
  apply propext
  constructor
  · intro hOut
    simp only [PCResult.skeleton, SimpleGraph.fromRel_adj] at hOut
    obtain ⟨hne, hor⟩ := hOut
    by_contra hnadj
    have hnadj_b : ¬ b.Adj i j := fun h => hnadj ((b.skeleton_adj).mpr h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hfalse := adjFalse_of_not_adj_lt hM hA hlt hnadj_b
      have hsym := adj_symm_pcAdjacency (O := O) i j
      rcases hor with ht | ht
      · exact absurd ht (by rw [hfalse]; decide)
      · have hfalse' : (pcAdjacency O).adj j i = false := by rw [← hsym]; exact hfalse
        exact absurd ht (by rw [hfalse']; decide)
    · have hnadj' : ¬ b.Adj j i := by
        intro hji
        have hij' : b.Adj i j := by
          unfold BayesNet.Adj at hji ⊢
          exact Or.comm.mp hji
        exact hnadj_b hij'
      have hfalse := adjFalse_of_not_adj_lt hM hA hgt hnadj'
      have hsym := adj_symm_pcAdjacency (O := O) j i
      rcases hor with ht | ht
      · have hfalse' : (pcAdjacency O).adj i j = false := by rw [← hsym]; exact hfalse
        exact absurd ht (by rw [hfalse']; decide)
      · exact absurd ht (by rw [hfalse]; decide)
  · intro hTrue
    rw [BayesNet.skeleton_adj] at hTrue
    have hne : i ≠ j := by
      rcases hTrue with e | e
      · exact ne_of_lt (e.lt b)
      · exact ne_of_gt (e.lt b)
    have htrue := adjTrue_pcAdjacency hA hTrue
    simp only [PCResult.skeleton, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl htrue⟩

/-- **Separating-set interface** (consumed by v-structure orientation): for every pair `i < j`
missing from the output, the recorded set separates the actual query `(i, j)` and excludes
both endpoints. No hypothesis on the oracle is needed. -/
theorem pcAdjacency_sepset (O : CIOracle n) {i j : Fin n} (hij : i < j)
    (h : ¬ (pcAdjacency O).skeleton.Adj i j) :
    O.Indep i j ((pcAdjacency O).sepset i j) ∧ i ∉ (pcAdjacency O).sepset i j ∧
      j ∉ (pcAdjacency O).sepset i j := by
  have hne : i ≠ j := ne_of_lt hij
  simp only [PCResult.skeleton, SimpleGraph.fromRel_adj] at h
  have hnot : ¬ ((pcAdjacency O).adj i j = true ∨ (pcAdjacency O).adj j i = true) := by
    intro hor
    exact h ⟨hne, hor⟩
  have hne_true : (pcAdjacency O).adj i j ≠ true := fun ht => hnot (Or.inl ht)
  have hadj_false : (pcAdjacency O).adj i j = false := Bool.eq_false_of_ne_true hne_true
  exact sepValid_pcAdjacency i j hij hadj_false

/-- Separating sets are stored symmetrically. -/
theorem pcAdjacency_sepset_symm (O : CIOracle n) (i j : Fin n) :
    (pcAdjacency O).sepset i j = (pcAdjacency O).sepset j i := by
  exact sepset_symm_pcAdjacency i j

/-- For a symmetric oracle the recorded set separates both query orders. -/
theorem pcAdjacency_sepset_of_symmetric {O : CIOracle n} (hO : O.Symmetric) {i j : Fin n}
    (hij : i ≠ j) (h : ¬ (pcAdjacency O).skeleton.Adj i j) :
    O.Indep i j ((pcAdjacency O).sepset i j) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (pcAdjacency_sepset O hlt h).1
  · have hsym : ¬ (pcAdjacency O).skeleton.Adj j i := fun hh => h hh.symm
    have hsep := (pcAdjacency_sepset O hgt hsym).1
    have hindep : O.Indep i j ((pcAdjacency O).sepset j i) := hO j i _ hsep
    rw [pcAdjacency_sepset_symm O j i] at hindep
    exact hindep

private theorem pcFirstSep_congr {O O' : CIOracle n} {r : PCResult n} {i j : Fin n} {d : ℕ}
    (hlt : i < j)
    (h : ∀ (i j : Fin n) (S : Finset (Fin n)), i < j → i ∉ S → j ∉ S →
      (O.Indep i j S ↔ O'.Indep i j S)) :
    pcFirstSep O r i j d = pcFirstSep O' r i j d := by
  unfold pcFirstSep
  apply List.find?_congr
  intro S hmem
  have hfree := mem_candidates_endpoint_free hmem
  have hiff := h i j S hlt hfree.1 hfree.2
  show decide (O.Indep i j S) = decide (O'.Indep i j S)
  by_cases hp : O.Indep i j S
  · rw [decide_eq_true hp, decide_eq_true (hiff.mp hp)]
  · rw [decide_eq_false hp, decide_eq_false (fun hcon => hp (hiff.mpr hcon))]

private theorem pcStep_congr {O O' : CIOracle n} {d : ℕ} {r : PCResult n} {p : Fin n × Fin n}
    (hlt : p.1 < p.2)
    (h : ∀ (i j : Fin n) (S : Finset (Fin n)), i < j → i ∉ S → j ∉ S →
      (O.Indep i j S ↔ O'.Indep i j S)) :
    pcStep O d r p = pcStep O' d r p := by
  have hsep : pcFirstSep O r p.1 p.2 d = pcFirstSep O' r p.1 p.2 d :=
    pcFirstSep_congr hlt h
  unfold pcStep
  by_cases hb : r.adj p.1 p.2 = true
  · simp only [ite_eq_left hb]
    rw [hsep]
  · simp only [ite_eq_right hb]

private theorem pcRound_congr {O O' : CIOracle n} {r : PCResult n} {d : ℕ}
    (h : ∀ (i j : Fin n) (S : Finset (Fin n)), i < j → i ∉ S → j ∉ S →
      (O.Indep i j S ↔ O'.Indep i j S)) :
    pcRound O r d = pcRound O' r d := by
  unfold pcRound
  have gen : ∀ (l : List (Fin n × Fin n)) (s : PCResult n),
      (∀ p ∈ l, p.1 < p.2) → l.foldl (pcStep O d) s = l.foldl (pcStep O' d) s := by
    intro l
    induction l with
    | nil => intro s _; rfl
    | cons p ps ih =>
      intro s hlt
      have hp : p.1 < p.2 := hlt p List.mem_cons_self
      have hps : ∀ q ∈ ps, q.1 < q.2 := fun q hq => hlt q (List.mem_cons_of_mem p hq)
      have hstep : pcStep O d s p = pcStep O' d s p := pcStep_congr hp h
      rw [List.foldl_cons, List.foldl_cons, hstep]
      exact ih _ hps
  exact gen (pcPairs n) r (fun p hm => pcPairs_mem_lt hm)

/-- The adjacency phase reads the oracle only on endpoint-free queries `(i, j, S)` with
`i < j`. -/
theorem pcAdjacency_congr {O O' : CIOracle n}
    (h : ∀ (i j : Fin n) (S : Finset (Fin n)), i < j → i ∉ S → j ∉ S →
      (O.Indep i j S ↔ O'.Indep i j S)) :
    pcAdjacency O = pcAdjacency O' := by
  unfold pcAdjacency
  have gen : ∀ (l : List ℕ) (s : PCResult n),
      l.foldl (pcRound O) s = l.foldl (pcRound O') s := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons d ds ih =>
      intro s
      rw [List.foldl_cons, List.foldl_cons, pcRound_congr h]
      exact ih _
  exact gen (List.range n) (PCResult.complete n)

/-! ### Targets: the d-separation and law instances -/

/-- The d-separation oracle is a Markov oracle. -/
theorem BayesNet.markovOracle_dsepOracle (b : BayesNet α n) : b.MarkovOracle b.dsepOracle := by
  intro i j S _ _ _ hd
  exact hd

/-- The d-separation oracle is adjacency-faithful. -/
theorem BayesNet.adjacencyFaithful_dsepOracle (b : BayesNet α n) :
    b.AdjacencyFaithful b.dsepOracle := by
  intro i j S hadj _ _ hindep
  exact b.not_dSeparated_of_adj hadj _ hindep

/-- The d-separation oracle is symmetric. -/
theorem BayesNet.symmetric_dsepOracle (b : BayesNet α n) : b.dsepOracle.Symmetric := by
  intro i j S h
  exact BayesNet.DSeparated.symm b h

/-- A law oracle is symmetric. -/
theorem symmetric_lawOracle [Fintype β] (P : (Fin n → β) → ℝ) : (lawOracle P).Symmetric := by
  intro i j S h
  have h' : CondIndep P ({i} : Set (Fin n)) ({j} : Set (Fin n)) ↑S := h
  have h2 : CondIndep P ↑(({i} : Finset (Fin n))) ↑(({j} : Finset (Fin n))) ↑S := by
    simpa only [Finset.coe_singleton] using h'
  have h3 := condIndep_symm h2
  have h4 : CondIndep P ({j} : Set (Fin n)) ({i} : Set (Fin n)) ↑S := by
    simpa only [Finset.coe_singleton] using h3
  exact h4

/-- With the d-separation oracle of the unknown graph, the adjacency phase returns its
skeleton. -/
theorem pcAdjacency_dsepOracle (b : BayesNet α n) :
    (pcAdjacency b.dsepOracle).skeleton = b.skeleton := by
  exact pcAdjacency_skeleton_eq b.markovOracle_dsepOracle b.adjacencyFaithful_dsepOracle

/-- The joint law of a network is a Markov oracle for its own graph (global Markov
soundness). -/
theorem BayesNet.markovOracle_lawOracle_joint [Fintype α] [Nonempty α] (b : BayesNet α n) :
    b.MarkovOracle (lawOracle b.joint) := by
  intro i j S _ _ _ h
  exact b.condIndep_of_dSeparated h

/-- **Skeleton theorem under faithfulness** (Kalisch and Bühlmann 2007, Proposition 1, skeleton
part): for any law `P` faithful to the graph of `b`, the adjacency phase on the population
oracle of `P` returns the skeleton of `b`. -/
theorem pcAdjacency_lawOracle_of_faithful [Fintype β] {b : BayesNet α n}
    {P : (Fin n → β) → ℝ} (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) (h : b.Faithful P) :
    (pcAdjacency (lawOracle P)).skeleton = b.skeleton := by
  exact pcAdjacency_skeleton_eq h.markovOracle h.adjacencyFaithful

/-! ### The unfaithful XOR collider -/

namespace PCSkeleton

open Convexity Junctions

/-- The XOR collider `0 → 2 ← 1`: `X₀` and `X₁` are independent fair coins and `X₂ = X₀ xor X₁`
(node `2` is `true` exactly when an odd number of its parents are). -/
noncomputable def xorNet : BayesNet Bool 3 where
  pa := colliderPa
  cpt k u := if (k : ℕ) = 2 then
      StdSimplex.single (decide ((univ.filter fun i => u i = true).card % 2 = 1))
    else fairCoin

/-- The answer table of the XOR law on endpoint-free queries of distinct nodes: independent
exactly given the empty set. -/
def xorTable : CIOracle 3 where
  Indep _ _ S := S = ∅
  decIndep _ _ S := inferInstanceAs (Decidable (S = ∅))

/-- Kernel-checked: `0 → 2` is an edge of the XOR collider. -/
theorem xorNet_adj_zero_two : xorNet.Adj 0 2 :=
  Or.inl (by decide)

/-- Kernel-checked: on the XOR answer table the adjacency phase deletes every edge. -/
theorem pcAdjacency_xorTable_skeleton_adj (i j : Fin 3) :
    ¬ (pcAdjacency xorTable).skeleton.Adj i j := by
  revert i j
  decide

/-- Kernel-checked: every recorded separating set on the XOR answer table is empty. -/
theorem pcAdjacency_xorTable_sepset (i j : Fin 3) : (pcAdjacency xorTable).sepset i j = ∅ := by
  revert i j
  decide

/-- The XOR joint in closed form: uniform on the parity-even assignments. -/
theorem xorNet_joint_apply (x : Fin 3 → Bool) :
    xorNet.joint x = if x 2 = (x 0 ^^ x 1) then 1 / 4 else 0 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three]
  have h0 : ((0 : Fin 3) : ℕ) ≠ 2 := by decide
  have h1 : ((1 : Fin 3) : ℕ) ≠ 2 := by decide
  have h2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  simp only [xorNet, h0, h1, h2, ite_false, ite_true,
    fairCoin_weights, StdSimplex.weights_single, Finsupp.single_apply]
  have h0lt : 0 < ↑(2 : Fin 3) := by decide
  have h1lt : 1 < ↑(2 : Fin 3) := by decide
  have hpa : colliderPa 2 = {⟨0, h0lt⟩, ⟨1, h1lt⟩} := by
    have hc : colliderPa 2 = {⟨0, Nat.zero_lt_succ 1⟩, ⟨1, Nat.lt_succ_self 1⟩} := by decide
    exact hc
  have m0 : (⟨0, h0lt⟩ : Fin ↑(2 : Fin 3)) ∈ colliderPa 2 := by simp [hpa]
  have m1 : (⟨1, h1lt⟩ : Fin ↑(2 : Fin 3)) ∈ colliderPa 2 := by simp [hpa]
  have huniv : (univ : Finset ↥(colliderPa 2)) = {⟨⟨0, h0lt⟩, m0⟩, ⟨⟨1, h1lt⟩, m1⟩} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have hmem : i.val = ⟨0, h0lt⟩ ∨ i.val = ⟨1, h1lt⟩ := by
      have h := i.2
      simp only [hpa, Finset.mem_insert, Finset.mem_singleton] at h
      exact h
    cases hmem with
    | inl h => exact Or.inl (Subtype.ext h)
    | inr h => exact Or.inr (Subtype.ext h)
  cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hx2 : x 2 <;>
    simp [huniv, Finset.card_filter, Finset.sum_singleton,
      hx0, hx1, -Finset.sum_boole] <;>
    norm_num

/-- Under the XOR law the root `0` is independent of its child `2`. -/
theorem xorNet_condIndep_zero_two : CondIndep xorNet.joint {0} {2} ∅ := by
  intro x
  have agree_on_pair : ∀ (y : Fin 3 → Bool),
      (∀ v ∈ (({0} ∪ {2} : Set (Fin 3))), y v = x v) ↔ (y 0 = x 0 ∧ y 2 = x 2) := by
    intro y
    constructor
    · intro h
      exact ⟨h 0 (by simp), h 2 (by simp)⟩
    · rintro ⟨h0, h2⟩ v hv
      simp only [Set.mem_union, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact h0
      · exact h2
  have agree_on_zero : ∀ (y : Fin 3 → Bool),
      (∀ v ∈ (({0} : Set (Fin 3))), y v = x v) ↔ (y 0 = x 0) := by
    intro y
    constructor
    · intro h
      exact h 0 (by simp)
    · rintro h0 v hv
      simp only [Set.mem_singleton_iff] at hv
      rcases hv with rfl
      exact h0
  have agree_on_two : ∀ (y : Fin 3 → Bool),
      (∀ v ∈ (({2} : Set (Fin 3))), y v = x v) ↔ (y 2 = x 2) := by
    intro y
    constructor
    · intro h
      exact h 2 (by simp)
    · rintro h2 v hv
      simp only [Set.mem_singleton_iff] at hv
      rcases hv with rfl
      exact h2
  have agree_on_empty : ∀ (y : Fin 3 → Bool),
      (∀ v ∈ ((∅ : Set (Fin 3))), y v = x v) ↔ True := by
    intro y
    exact ⟨fun _ => trivial, fun _ _ hv => absurd hv (Set.notMem_empty _)⟩
  let e : (Fin 3 → Bool) ≃ Bool × Bool × Bool :=
    { toFun := fun y => (y 0, y 1, y 2)
      invFun := fun p => ![p.1, p.2.1, p.2.2]
      left_inv := fun y => by
        show ![y 0, y 1, y 2] = y
        funext i
        fin_cases i
        · simp [Matrix.cons_val_zero]
        · simp [Matrix.cons_val_zero, Matrix.cons_val_one]
        · simp [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      right_inv := fun p => by
        obtain ⟨a, b, c⟩ := p
        show ((![a, b, c] : Fin 3 → Bool) 0, (![a, b, c]) 1, (![a, b, c]) 2) = (a, b, c)
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons] }
  have e_symm : ∀ (p : Bool × Bool × Bool), e.symm p = ![p.1, p.2.1, p.2.2] :=
    fun p => rfl
  have sum_trans : ∀ (g : (Fin 3 → Bool) → ℝ),
      (∑ y, g y) = ∑ z : Bool × Bool × Bool, g (e.symm z) :=
    fun g => Fintype.sum_equiv e g _ fun y => by
      show g y = g (e.symm (e y))
      rw [Equiv.symm_apply_apply]
  cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hx2 : x 2 <;> clear hx1 <;>
    simp only [Set.union_empty, marginal, xorNet_joint_apply, Finset.sum_filter,
      sum_trans, agree_on_pair, agree_on_zero, agree_on_two,
      agree_on_empty, Fintype.sum_prod_type, Fintype.sum_bool, e_symm,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hx0, hx2] <;>
    simp <;>
    norm_num

/-- The XOR law answers every endpoint-free query of distinct nodes as `xorTable` does. -/
theorem lawOracle_xorNet_iff {i j : Fin 3} {S : Finset (Fin 3)} (hij : i ≠ j) (hi : i ∉ S)
    (hj : j ∉ S) : (lawOracle xorNet.joint).Indep i j S ↔ xorTable.Indep i j S := by
  have fin3_cases : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have agree_single : ∀ (x y : Fin 3 → Bool) (a : Fin 3),
      (∀ v ∈ (({a} : Set (Fin 3))), y v = x v) ↔ (y a = x a) := by
    intro x y a
    constructor
    · intro h
      exact h a (by simp)
    · rintro h v hv
      simp only [Set.mem_singleton_iff] at hv
      rcases hv with rfl
      exact h
  have agree_pair : ∀ (x y : Fin 3 → Bool) (a b : Fin 3),
      (∀ v ∈ (({a} ∪ {b} : Set (Fin 3))), y v = x v) ↔ (y a = x a ∧ y b = x b) := by
    intro x y a b
    constructor
    · intro h
      exact ⟨h a (by simp), h b (by simp)⟩
    · rintro ⟨ha, hb⟩ v hv
      simp only [Set.mem_union, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact ha
      · exact hb
  have agree_triple : ∀ (x y : Fin 3 → Bool) (a b c : Fin 3),
      (∀ v ∈ (({a} ∪ {b} ∪ {c} : Set (Fin 3))), y v = x v) ↔
        (y a = x a ∧ y b = x b ∧ y c = x c) := by
    intro x y a b c
    constructor
    · intro h
      exact ⟨h a (by simp), h b (by simp), h c (by simp)⟩
    · rintro ⟨ha, hb, hc⟩ v hv
      simp only [Set.mem_union, Set.mem_singleton_iff] at hv
      rcases hv with (rfl | rfl) | rfl
      · exact ha
      · exact hb
      · exact hc
  have agree_empty : ∀ (x y : Fin 3 → Bool),
      (∀ v ∈ ((∅ : Set (Fin 3))), y v = x v) ↔ True :=
    fun x y => ⟨fun _ => trivial, fun _ _ hv => absurd hv (Set.notMem_empty _)⟩
  let e : (Fin 3 → Bool) ≃ Bool × Bool × Bool :=
    { toFun := fun y => (y 0, y 1, y 2)
      invFun := fun p => ![p.1, p.2.1, p.2.2]
      left_inv := fun y => by
        show ![y 0, y 1, y 2] = y
        funext i
        fin_cases i
        · simp [Matrix.cons_val_zero]
        · simp [Matrix.cons_val_zero, Matrix.cons_val_one]
        · simp [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      right_inv := fun p => by
        obtain ⟨a, b, c⟩ := p
        show ((![a, b, c] : Fin 3 → Bool) 0, (![a, b, c]) 1, (![a, b, c]) 2) = (a, b, c)
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons] }
  have e_symm : ∀ (p : Bool × Bool × Bool), e.symm p = ![p.1, p.2.1, p.2.2] :=
    fun p => rfl
  have sum_trans : ∀ (g : (Fin 3 → Bool) → ℝ),
      (∑ y, g y) = ∑ z : Bool × Bool × Bool, g (e.symm z) :=
    fun g => Fintype.sum_equiv e g _ fun y => by
      show g y = g (e.symm (e y))
      rw [Equiv.symm_apply_apply]
  show CondIndep xorNet.joint {i} {j} ↑S ↔ S = ∅
  by_cases hS : S = ∅
  · subst hS
    refine ⟨?_, ?_⟩ <;> intro _
    · rfl
    · simp only [Finset.coe_empty]
      intro x
      simp only [Set.union_empty]
      rcases fin3_cases i with rfl | rfl | rfl <;>
        rcases fin3_cases j with rfl | rfl | rfl <;>
        (first
          | exact (hij rfl).elim
          | (cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hx2 : x 2 <;>
              simp only [marginal, xorNet_joint_apply, Finset.sum_filter, sum_trans,
                agree_pair _ _ _ _, agree_single _ _ _, agree_empty _ _,
                Fintype.sum_prod_type, Fintype.sum_bool, e_symm,
                Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
                Matrix.head_cons, Matrix.tail_cons, hx0, hx1, hx2] <;>
              simp <;>
              norm_num))
  · rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl
    · exact (hij rfl).elim
    · have h2mem : (2 : Fin 3) ∈ S := by
        by_contra hcon
        have hempty : S = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro v hv
          rcases fin3_cases v with rfl | rfl | rfl <;> simp_all
        exact hS hempty
      have hSeq : S = {2} := Finset.Subset.antisymm
        (fun v hv => by rcases fin3_cases v with rfl | rfl | rfl <;> simp_all)
        (Finset.singleton_subset_iff.mpr h2mem)
      subst hSeq
      have hne : (({2} : Finset (Fin 3)) ≠ ∅) := by decide
      refine ⟨?_, ?_⟩
      · intro h
        have heq := h ![false, false, false]
        simp only [Finset.coe_singleton, marginal, xorNet_joint_apply, Finset.sum_filter,
          sum_trans, agree_triple _ _ _ _ _, agree_pair _ _ _ _, agree_single _ _ _,
          Fintype.sum_prod_type, Fintype.sum_bool, e_symm,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons] at heq
        simp at heq
      · intro h
        exact absurd h hne
    · have h1mem : (1 : Fin 3) ∈ S := by
        by_contra hcon
        have hempty : S = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro v hv
          rcases fin3_cases v with rfl | rfl | rfl <;> simp_all
        exact hS hempty
      have hSeq : S = {1} := Finset.Subset.antisymm
        (fun v hv => by rcases fin3_cases v with rfl | rfl | rfl <;> simp_all)
        (Finset.singleton_subset_iff.mpr h1mem)
      subst hSeq
      have hne : (({1} : Finset (Fin 3)) ≠ ∅) := by decide
      refine ⟨?_, ?_⟩
      · intro h
        have heq := h ![false, false, false]
        simp only [Finset.coe_singleton, marginal, xorNet_joint_apply, Finset.sum_filter,
          sum_trans, agree_triple _ _ _ _ _, agree_pair _ _ _ _, agree_single _ _ _,
          Fintype.sum_prod_type, Fintype.sum_bool, e_symm,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons] at heq
        simp at heq
      · intro h
        exact absurd h hne
    · have h2mem : (2 : Fin 3) ∈ S := by
        by_contra hcon
        have hempty : S = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro v hv
          rcases fin3_cases v with rfl | rfl | rfl <;> simp_all
        exact hS hempty
      have hSeq : S = {2} := Finset.Subset.antisymm
        (fun v hv => by rcases fin3_cases v with rfl | rfl | rfl <;> simp_all)
        (Finset.singleton_subset_iff.mpr h2mem)
      subst hSeq
      have hne : (({2} : Finset (Fin 3)) ≠ ∅) := by decide
      refine ⟨?_, ?_⟩
      · intro h
        have heq := h ![false, false, false]
        simp only [Finset.coe_singleton, marginal, xorNet_joint_apply, Finset.sum_filter,
          sum_trans, agree_triple _ _ _ _ _, agree_pair _ _ _ _, agree_single _ _ _,
          Fintype.sum_prod_type, Fintype.sum_bool, e_symm,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons] at heq
        simp at heq
      · intro h
        exact absurd h hne
    · exact (hij rfl).elim
    · have h0mem : (0 : Fin 3) ∈ S := by
        by_contra hcon
        have hempty : S = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro v hv
          rcases fin3_cases v with rfl | rfl | rfl <;> simp_all
        exact hS hempty
      have hSeq : S = {0} := Finset.Subset.antisymm
        (fun v hv => by rcases fin3_cases v with rfl | rfl | rfl <;> simp_all)
        (Finset.singleton_subset_iff.mpr h0mem)
      subst hSeq
      have hne : (({0} : Finset (Fin 3)) ≠ ∅) := by decide
      refine ⟨?_, ?_⟩
      · intro h
        have heq := h ![false, false, false]
        simp only [Finset.coe_singleton, marginal, xorNet_joint_apply, Finset.sum_filter,
          sum_trans, agree_triple _ _ _ _ _, agree_pair _ _ _ _, agree_single _ _ _,
          Fintype.sum_prod_type, Fintype.sum_bool, e_symm,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons] at heq
        simp at heq
      · intro h
        exact absurd h hne
    · have h1mem : (1 : Fin 3) ∈ S := by
        by_contra hcon
        have hempty : S = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro v hv
          rcases fin3_cases v with rfl | rfl | rfl <;> simp_all
        exact hS hempty
      have hSeq : S = {1} := Finset.Subset.antisymm
        (fun v hv => by rcases fin3_cases v with rfl | rfl | rfl <;> simp_all)
        (Finset.singleton_subset_iff.mpr h1mem)
      subst hSeq
      have hne : (({1} : Finset (Fin 3)) ≠ ∅) := by decide
      refine ⟨?_, ?_⟩
      · intro h
        have heq := h ![false, false, false]
        simp only [Finset.coe_singleton, marginal, xorNet_joint_apply, Finset.sum_filter,
          sum_trans, agree_triple _ _ _ _ _, agree_pair _ _ _ _, agree_single _ _ _,
          Fintype.sum_prod_type, Fintype.sum_bool, e_symm,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons] at heq
        simp at heq
      · intro h
        exact absurd h hne
    · have h0mem : (0 : Fin 3) ∈ S := by
        by_contra hcon
        have hempty : S = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro v hv
          rcases fin3_cases v with rfl | rfl | rfl <;> simp_all
        exact hS hempty
      have hSeq : S = {0} := Finset.Subset.antisymm
        (fun v hv => by rcases fin3_cases v with rfl | rfl | rfl <;> simp_all)
        (Finset.singleton_subset_iff.mpr h0mem)
      subst hSeq
      have hne : (({0} : Finset (Fin 3)) ≠ ∅) := by decide
      refine ⟨?_, ?_⟩
      · intro h
        have heq := h ![false, false, false]
        simp only [Finset.coe_singleton, marginal, xorNet_joint_apply, Finset.sum_filter,
          sum_trans, agree_triple _ _ _ _ _, agree_pair _ _ _ _, agree_single _ _ _,
          Fintype.sum_prod_type, Fintype.sum_bool, e_symm,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons] at heq
        simp at heq
      · intro h
        exact absurd h hne
    · exact (hij rfl).elim

/-- The XOR law is a Markov oracle for its graph. -/
theorem xorNet_markovOracle : xorNet.MarkovOracle (lawOracle xorNet.joint) :=
  BayesNet.markovOracle_lawOracle_joint xorNet

/-- The XOR law is not adjacency-faithful to its graph. -/
theorem xorNet_not_adjacencyFaithful : ¬ xorNet.AdjacencyFaithful (lawOracle xorNet.joint) := by
  intro hFaith
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h0mem : (0 : Fin 3) ∉ (∅ : Finset (Fin 3)) := by simp
  have h2mem : (2 : Fin 3) ∉ (∅ : Finset (Fin 3)) := by simp
  have hNot := hFaith 0 2 ∅ xorNet_adj_zero_two h0mem h2mem
  have hIndep : (lawOracle xorNet.joint).Indep 0 2 ∅ :=
    (lawOracle_xorNet_iff h02 h0mem h2mem).mpr rfl
  exact hNot hIndep

/-- The XOR law is not faithful to its graph. -/
theorem xorNet_not_faithful : ¬ xorNet.Faithful xorNet.joint := by
  intro hF
  exact xorNet_not_adjacencyFaithful hF.adjacencyFaithful

/-- **Unfaithful-law counterexample**: on the population oracle of the XOR law the adjacency
phase misses the true edge `0 → 2`. -/
theorem pcAdjacency_xorNet_misses_edge :
    xorNet.Adj 0 2 ∧ ¬ (pcAdjacency (lawOracle xorNet.joint)).skeleton.Adj 0 2 := by
  refine ⟨xorNet_adj_zero_two, ?_⟩
  have hcongr : pcAdjacency (lawOracle xorNet.joint) = pcAdjacency xorTable := by
    apply pcAdjacency_congr
    intro i j S hlt hi hj
    exact lawOracle_xorNet_iff (ne_of_lt hlt) hi hj
  rw [hcongr]
  exact pcAdjacency_xorTable_skeleton_adj 0 2

/-- The adjacency phase on the XOR law does not return the skeleton of its graph. -/
theorem pcAdjacency_xorNet_ne_skeleton :
    (pcAdjacency (lawOracle xorNet.joint)).skeleton ≠ xorNet.skeleton := by
  intro hEq
  have hMiss := pcAdjacency_xorNet_misses_edge
  have hAdj : xorNet.skeleton.Adj 0 2 := (BayesNet.skeleton_adj xorNet).mpr hMiss.1
  rw [hEq] at hMiss
  exact hMiss.2 hAdj

end PCSkeleton

end Cslib.MachineLearning.GraphicalModels
