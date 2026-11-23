/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DCJ MEDIAN (multichromosomal genomes) is NP-complete

Source:
E. Tannier, C. Zheng and D. Sankoff, "Multichromosomal median and halving problems under
different genomic distances", BMC Bioinformatics 10 (2009), 120, doi:10.1186/1471-2105-10-120
(Theorem 5: "The DCJ median problem for multichromosomal genomes is NP-hard, even for circular
genomes").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DCJMedian

/-!
# DCJ MEDIAN (multichromosomal genomes) is NP-complete

INSTANCE: three genomes `Π₁, Π₂, Π₃` on a common set of `n` genes, each given as a set of
adjacencies, and an integer `K`.
QUESTION: is there a genome `M` on the same genes with
`d_DCJ(Π₁, M) + d_DCJ(Π₂, M) + d_DCJ(Π₃, M) ≤ K`?

Definitions, after Tannier, Zheng and Sankoff (following Bergeron, Mixtacki and Stoye): a gene
`A` has a tail `Aᵗ` and a head `Aʰ`, its extremities. An adjacency is an unordered pair of gene
extremities, and a genome is a set of adjacencies in which each extremity is adjacent to zero or
one other extremity; an extremity in no adjacency is a telomere. Chromosomes may be linear or
circular (multichromosomal genomes, the general case of Theorem 5). A double cut and join (DCJ)
acts on two adjacencies `pq` and `rs`, where some of `p, q, r, s` may be the null symbol `∘` of a
telomere (and one adjacency may be `∘∘`), and replaces them by `pr` and `qs` (or `ps` and `qr`).
The DCJ distance `d_DCJ(Π, Γ)` is the least number of DCJs transforming `Π` into `Γ`.

Representation: the genes are `0, ..., n - 1`, with `n` given in unary as a list of `true`s (the
genes are part of the instance even when no adjacency mentions them); gene `g` has tail `2g` and
head `2g + 1`, so the extremities are `Fin (2n)`. A genome is a simple graph on the extremities
whose edges are its adjacencies and in which every vertex has at most one neighbour
(`IsGenome`). The input genomes are adjacency lists, read with `Cslib.Complexity.Karp.edgeGraph`.
Spelling out the null symbols, a DCJ (`IsDCJ`) is one of: deleting an adjacency `pq` (cutting
`pq` and `∘∘` into `p∘` and `q∘`); joining two telomeres `p` and `q` (the reverse); replacing an
adjacency `pq` and a telomere `r` by the adjacency `pr` and the telomere `q`; and replacing two
distinct adjacencies `pq`, `rs` by `pr` and `qs` (the choice `ps`, `qr` is the same move with `r`
and `s` exchanged). `DCJWithin Π Γ k` says that at most `k` DCJs transform `Π` into `Γ`, so
`d_DCJ(Π, Γ) ≤ k`; the question asks for `M` and `k₁ + k₂ + k₃ ≤ K` with `DCJWithin Πᵢ M kᵢ`,
which holds exactly when the three distances sum to at most `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the genes in unary (`n` entries `true`), the adjacency lists of `Π₁`, `Π₂`,
`Π₃` over the extremities `0, …, 2n - 1` (gene `g` has tail `2g` and head `2g + 1`), and
`K`. -/
abbrev DCJMedianInstance :=
  List Bool × List (ℕ × ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- A genome on the vertex set `V` of extremities: a set of adjacencies (the edges) in which each
extremity is adjacent to at most one other extremity. -/
def IsGenome {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ v x y, G.Adj v x → G.Adj v y → x = y

/-- One double cut and join transforms the genome `G` into `H`: deleting an adjacency `pq`;
joining two telomeres `p ≠ q`; replacing an adjacency `pq` and a telomere `r` by the adjacency
`pr` (making `q` a telomere); or replacing two distinct adjacencies `pq`, `rs` by `pr`, `qs`. -/
def IsDCJ {V : Type} (G H : SimpleGraph V) : Prop :=
  (∃ p q, G.Adj p q ∧ H = G.deleteEdges {s(p, q)}) ∨
  (∃ p q, p ≠ q ∧ (∀ x, ¬ G.Adj p x) ∧ (∀ x, ¬ G.Adj q x) ∧ H = G ⊔ SimpleGraph.edge p q) ∨
  (∃ p q r, G.Adj p q ∧ (∀ x, ¬ G.Adj r x) ∧
    H = G.deleteEdges {s(p, q)} ⊔ SimpleGraph.edge p r) ∨
  (∃ p q r s, G.Adj p q ∧ G.Adj r s ∧ s(p, q) ≠ s(r, s) ∧
    H = G.deleteEdges {s(p, q), s(r, s)} ⊔ SimpleGraph.edge p r ⊔ SimpleGraph.edge q s)

/-- At most `k` DCJs transform `G` into `H`: a sequence of at most `k + 1` genomes from `G` to
`H` in which each is obtained from the previous one by a DCJ. -/
def DCJWithin {V : Type} (G H : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ l : List (SimpleGraph V), l.length ≤ k + 1 ∧ l.head? = some G ∧ l.getLast? = some H ∧
    l.IsChain IsDCJ

/-- The number `n` of genes. -/
def numGenes (i : DCJMedianInstance) : ℕ := i.1.length

/-- The genome given by an adjacency list, on the extremities `Fin (2n)`. -/
def genome (i : DCJMedianInstance) (adj : List (ℕ × ℕ)) : SimpleGraph (Fin (2 * numGenes i)) :=
  Cslib.Complexity.Karp.edgeGraph (2 * numGenes i) adj

/-- An adjacency list describes a genome on the extremities `0, …, 2n - 1`: no adjacency is
listed twice in either orientation, both extremities of each are below `2n` and distinct, and
each extremity lies in at most one adjacency. -/
def GenomeList (i : DCJMedianInstance) (adj : List (ℕ × ℕ)) : Prop :=
  adj.Nodup ∧ (∀ e ∈ adj, e.1 < 2 * numGenes i ∧ e.2 < 2 * numGenes i ∧ e.1 ≠ e.2 ∧
    (e.2, e.1) ∉ adj) ∧ IsGenome (genome i adj)

/-- Well-formedness of an instance: the gene list is a unary number (all entries `true`), and
each of the three adjacency lists describes a genome. -/
def WellFormed (i : DCJMedianInstance) : Prop :=
  (∀ b ∈ i.1, b = true) ∧ GenomeList i i.2.1 ∧ GenomeList i i.2.2.1 ∧ GenomeList i i.2.2.2.1

/-- Some genome `M` on the extremities has total DCJ distance at most `K` to the three input
genomes. -/
def DCJMedianFeasible (i : DCJMedianInstance) : Prop :=
  ∃ M : SimpleGraph (Fin (2 * numGenes i)), IsGenome M ∧ ∃ k₁ k₂ k₃, k₁ + k₂ + k₃ ≤ i.2.2.2.2 ∧
    DCJWithin (genome i i.2.1) M k₁ ∧ DCJWithin (genome i i.2.2.1) M k₂ ∧
      DCJWithin (genome i i.2.2.2.1) M k₃

open Classical in
/-- DCJ MEDIAN as a decision problem over bitstrings. -/
noncomputable def dcjMedianDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DCJMedianInstance) x with
  | some i => decide (WellFormed i ∧ DCJMedianFeasible i)
  | none => false

/-- **DCJ MEDIAN for multichromosomal genomes is NP-complete.** Source: Tannier, Zheng and
Sankoff (2009), Theorem 5. -/
public theorem_wanted dcjMedian_npComplete :
    dcjMedianDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dcjMedianDec

end MetaMathlibExt.Complexity.NPComplete.DCJMedian
