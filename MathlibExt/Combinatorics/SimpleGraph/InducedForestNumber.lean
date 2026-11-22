/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Induced forest number

For a finite simple graph `G`, the induced forest number `a(G)` is the maximum
number of vertices in an induced forest, that is, the maximum cardinality of a
vertex set whose induced subgraph is acyclic.

Provenance: Heejae Jung, *A 15/31 Counterexample Family to the
Albertson--Berman Conjecture*, <https://arxiv.org/abs/2608.17350v1>.
Definition `a(G)` is in `disproving_albertson_berman_15_31.tex`, line 52.

Verified hashes (SHA-256):
* source bundle: `77e3f71bc75cef0408d82873e1625a059a0721bf24efa1c26d0f5daa034f77be`
* PDF: `af3e123b6a24073934ec014b51ddfcda779898b39169c104f075a299a937a1f8`
* source file `disproving_albertson_berman_15_31.tex`:
  `c1304969249c15dbe92171d3d26b7025a697bbba3a00bddae9428cf8d84c1145`
* line-52 span: `8af6e1d9bd63f3605f2bf89de6ede13e3af6933d9ce904ac181781e73b732d95`
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- **Induced forest number.** For a simple graph $G$ on a finite vertex set $V$, the induced
forest number $a(G)$ is the maximum number of vertices of an induced forest in $G$, that is, the
maximum cardinality of a set $S \subseteq V$ such that the subgraph of $G$ induced on $S$ is
acyclic.

Source: H. Jung, A 15/31 Counterexample Family to the Albertson--Berman Conjecture,
arXiv:2608.17350v1, the definition of $a(G)$. -/
noncomputable def inducedForestNumber (G : SimpleGraph V) : Nat := by
  classical
  exact Finset.sup (Finset.univ.powerset (α := V))
    (fun (s : Finset V) => if (G.induce (↑s : Set V)).IsAcyclic then s.card else 0)

/-- **Induced forests are no larger than the induced forest number.** Let $G$ be a simple graph
on a finite vertex set $V$. For every set $S \subseteq V$ such that the subgraph of $G$ induced
on $S$ is acyclic, $|S|$ is at most the induced forest number of $G$. -/
theorem card_le_inducedForestNumber (G : SimpleGraph V) (s : Finset V)
    (h : (G.induce (↑s : Set V)).IsAcyclic) :
    s.card ≤ G.inducedForestNumber := by
  classical
  unfold inducedForestNumber
  have hmem : s ∈ Finset.univ.powerset (α := V) := by simp
  have hif : (if (G.induce (↑s : Set V)).IsAcyclic then s.card else 0) = s.card :=
    ite_eq_left h
  calc s.card
      = (if (G.induce (↑s : Set V)).IsAcyclic then s.card else 0) := hif.symm
    _ ≤ Finset.sup (Finset.univ.powerset (α := V))
        (fun (t : Finset V) => if (G.induce (↑t : Set V)).IsAcyclic then t.card else 0) :=
      Finset.le_sup (s := Finset.univ.powerset (α := V))
        (f := fun (t : Finset V) => if (G.induce (↑t : Set V)).IsAcyclic then t.card else 0)
        hmem

/-- **The induced forest number is at most the number of vertices.** For every simple graph $G$
on a finite vertex set $V$, the induced forest number of $G$ is at most $|V|$. -/
theorem inducedForestNumber_le_card (G : SimpleGraph V) :
    G.inducedForestNumber ≤ Fintype.card V := by
  classical
  unfold inducedForestNumber
  apply Finset.sup_le
  intro s hs
  by_cases h : (G.induce (↑s : Set V)).IsAcyclic
  · simp only [ite_eq_left h]
    exact Finset.card_le_univ s
  · simp only [ite_eq_right h]
    exact Nat.zero_le _

/-- **The induced forest number is attained.** For every simple graph $G$ on a finite vertex set
$V$, there is a set $S \subseteq V$ such that the subgraph of $G$ induced on $S$ is acyclic and
$|S|$ equals the induced forest number of $G$. -/
theorem exists_isAcyclic_card_eq_inducedForestNumber (G : SimpleGraph V) :
    ∃ s : Finset V, (G.induce (↑s : Set V)).IsAcyclic ∧ s.card = G.inducedForestNumber := by
  classical
  unfold inducedForestNumber
  have hne : (Finset.univ.powerset (α := V)).Nonempty := ⟨∅, by simp⟩
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_sup (Finset.univ.powerset (α := V)) hne
    (fun (t : Finset V) => if (G.induce (↑t : Set V)).IsAcyclic then t.card else 0)
  by_cases h : (G.induce (↑s : Set V)).IsAcyclic
  · refine ⟨s, h, ?_⟩
    have hif : (if (G.induce (↑s : Set V)).IsAcyclic then s.card else 0) = s.card :=
      ite_eq_left h
    exact (heq.trans hif).symm
  · have hif : (if (G.induce (↑s : Set V)).IsAcyclic then s.card else 0) = 0 :=
      ite_eq_right h
    have hsup : (0 : Nat) = Finset.sup (Finset.univ.powerset (α := V))
        (fun (t : Finset V) => if (G.induce (↑t : Set V)).IsAcyclic then t.card else 0) :=
      (heq.trans hif).symm
    have hsub : Subsingleton ↥(((∅ : Finset V) : Set V)) :=
      ⟨fun a _ => False.elim (by simpa using a.property)⟩
    have hempty : (G.induce (((∅ : Finset V) : Set V))).IsAcyclic :=
      @SimpleGraph.IsAcyclic.of_subsingleton _ hsub _
    refine ⟨∅, hempty, ?_⟩
    calc (∅ : Finset V).card = 0 := by simp
      _ = Finset.sup (Finset.univ.powerset (α := V))
          (fun (t : Finset V) => if (G.induce (↑t : Set V)).IsAcyclic then t.card else 0) := hsup

end SimpleGraph

end
