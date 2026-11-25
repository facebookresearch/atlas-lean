/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO PERFECT MATCHINGS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT16] PARTITION INTO
PERFECT MATCHINGS;
T. J. Schaefer, "The complexity of satisfiability problems", Proceedings of the
10th Annual ACM Symposium on Theory of Computing (STOC 1978), 216-226,
doi:10.1145/800133.804350 (already for `K = 2`, by a transformation from
NOT-ALL-EQUAL 3SAT);
see also E. D. Demaine, K. Karntikoon, and N. Pitimanaaree, "2-Colorable
perfect matching is NP-complete in 2-connected 3-regular planar graphs",
Theory of Computing Systems (2025), doi:10.1007/s00224-025-10221-2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Matching

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoPerfectMatchings

/-!
# PARTITION INTO PERFECT MATCHINGS is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: can the vertices of
`G` be partitioned into `k ≤ K` disjoint sets `V₁, ..., Vₖ` such that, for `1 ≤ i ≤ k`, the
subgraph induced by `Vᵢ` is a perfect matching?

The partition is given by the map `c : V → Fin k` sending each vertex to the index of its
block, so `Vⱼ = c⁻¹(j)`. The subgraph induced by `Vⱼ` is
`(⊤ : G.Subgraph).induce Vⱼ`, whose vertex set is `Vⱼ`; it is a perfect matching exactly when
it is a matching in Mathlib's sense (`Subgraph.IsMatching`): every vertex of `Vⱼ` is adjacent
to exactly one other vertex of `Vⱼ`. An empty block is allowed; dropping it gives a partition
with fewer blocks, so this does not change the answer.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev PartitionIntoPerfectMatchingsInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PartitionIntoPerfectMatchingsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and
`0 < K ≤ |V| = n`. -/
def WellFormed (i : PartitionIntoPerfectMatchingsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- The vertices split into at most `K` blocks, each inducing a perfect matching: for some
`k ≤ K` there is a partition into blocks `c⁻¹(j)`, `j : Fin k`, such that the subgraph induced
by each block is a matching on that block. -/
def PartitionIntoPerfectMatchingsFeasible (i : PartitionIntoPerfectMatchingsInstance) : Prop :=
  ∃ k ≤ i.2.2, ∃ c : Fin i.1 → Fin k,
    ∀ j : Fin k, ((⊤ : (Graph i).Subgraph).induce {v | c v = j}).IsMatching

open Classical in
/-- PARTITION INTO PERFECT MATCHINGS as a decision problem over bitstrings. -/
noncomputable def partitionIntoPerfectMatchingsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoPerfectMatchingsInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoPerfectMatchingsFeasible i)
  | none => false

/-- **PARTITION INTO PERFECT MATCHINGS is NP-complete.** Source: Garey and Johnson (1979),
[GT16]; Schaefer (1978). -/
public theorem_wanted partitionIntoPerfectMatchings_npComplete :
    partitionIntoPerfectMatchingsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoPerfectMatchingsDec

-- Regression examples for `PartitionIntoPerfectMatchingsFeasible`: every vertex must have
-- exactly one neighbour in its own block.

-- One isolated vertex with `K = 1` is a no-instance: its block `{0}` has no edge.
private example : ¬ PartitionIntoPerfectMatchingsFeasible (1, [], 1) := by
  rintro ⟨k, -, c, hc⟩
  obtain ⟨w, hw, -⟩ := hc (c 0) (v := 0) rfl
  have h := hw.adj_sub
  rw [Fin.fin_one_eq_zero w] at h
  exact h.ne rfl

-- A single edge with `K = 1` is a yes-instance.
private example : PartitionIntoPerfectMatchingsFeasible (2, [(0, 1)], 1) := by
  refine ⟨1, le_rfl, fun _ => 0, fun j v _ => ⟨v + 1, ?_, ?_⟩⟩
  · simp only [SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.top_adj]
    refine ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, ?_⟩
    fin_cases v <;> simp [Graph, Cslib.Complexity.Karp.edgeGraph]
  · intro w hw
    have h := hw.adj_sub
    fin_cases v <;> fin_cases w <;> simp_all [Graph, Cslib.Complexity.Karp.edgeGraph]

-- The 4-cycle `0-1-2-3-0` with `K = 2` is a yes-instance with blocks `{0, 1}` and `{2, 3}`.
-- Neither block contains all four vertices, so each block's induced subgraph is a perfect
-- matching of its block but not a spanning subgraph of the whole graph.
private example :
    PartitionIntoPerfectMatchingsFeasible (4, [(0, 1), (1, 2), (2, 3), (3, 0)], 2) := by
  refine ⟨2, le_rfl, fun v => if (v : ℕ) < 2 then 0 else 1, fun j v hv => ?_⟩
  simp only [SimpleGraph.Subgraph.induce_verts, Set.mem_ofPred_eq] at hv
  subst hv
  refine ⟨if (v : ℕ) % 2 = 0 then v + 1 else v - 1, ?_, ?_⟩
  · simp only [SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.top_adj]
    fin_cases v <;> simp [Graph, Cslib.Complexity.Karp.edgeGraph]
  · intro w hw
    have h := hw.adj_sub
    have h2 := hw.snd_mem
    simp only [SimpleGraph.Subgraph.induce_verts, Set.mem_ofPred_eq] at h2
    fin_cases v <;> fin_cases w <;> simp_all [Graph, Cslib.Complexity.Karp.edgeGraph]

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoPerfectMatchings
