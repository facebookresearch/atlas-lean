/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Intron clusters from shared splice sites

The input is a set of distinct introns from one already chosen overlap group and strand. An
intron is represented by its ordered donor–acceptor pair. Edges join introns sharing a donor
or sharing an acceptor; a donor equal to another intron's acceptor does not suffice. The
clusters are the connected components containing at least two introns.

This is the graph definition and singleton rule of Li et al., *Annotation-free quantification
of RNA splicing using LeafCutter*, Nature Genetics 50 (2018), 151–158, Figure 1 and Online
Methods, “Identifying alternatively excised introns” (doi:10.1038/s41588-017-0004-9). It does not
model read alignment, selection of overlap groups, filtering by read counts, or proportions.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.IntronClusters

variable {Site : Type*}

/-- **Junction-sharing graph.** Two distinct observed introns on one strand are adjacent if
their donors coincide or their acceptors coincide. The first and second coordinates correspond
to donor and acceptor respectively; they need not be in increasing coordinate order. -/
def junctionGraph (observed : Set (Site × Site)) : SimpleGraph observed where
  Adj u v := u ≠ v ∧ (u.val.1 = v.val.1 ∨ u.val.2 = v.val.2)
  symm := by
    constructor
    rintro u v ⟨hne, h | h⟩
    · exact ⟨hne.symm, Or.inl h.symm⟩
    · exact ⟨hne.symm, Or.inr h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **Intron clusters.** Retain exactly the connected components of the junction-sharing graph
that have at least two distinct vertices. Paths can connect introns without a common endpoint. -/
def clusters (observed : Set (Site × Site)) : Set (junctionGraph observed).ConnectedComponent :=
  {C | C.supp.Nontrivial}

/-- The component of an intron is retained exactly when that intron has a neighbor. -/
theorem mem_clusters_iff_has_neighbor {observed : Set (Site × Site)} (u : observed) :
    (junctionGraph observed).connectedComponentMk u ∈ clusters observed ↔
      ∃ v, (junctionGraph observed).Adj u v := by
  let G := junctionGraph observed
  let C := G.connectedComponentMk u
  have hu : u ∈ C.supp := rfl
  change C.supp.Nontrivial ↔ ∃ v, G.Adj u v
  constructor
  · intro h
    obtain ⟨v, hv, hne⟩ := h.exists_ne u
    exact (G.mem_support).mp
      (SimpleGraph.mem_support_of_reachable hne.symm (C.reachable_of_mem_supp hu hv))
  · rintro ⟨v, hadj⟩
    exact Set.nontrivial_of_mem_mem_ne hu (C.mem_supp_of_adj_mem_supp hu hadj) hadj.ne

end Cslib.Bioinformatics.IntronClusters
