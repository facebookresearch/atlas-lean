/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Embedding σ-compact TDLC groups into compactly generated ones (Oberwolfach Report 55/2023)

Mini-Workshop: Homological aspects of TDLC-groups, Oberwolfach Report 55/2023, problem session,
Question 5 (I. Leary and I. Castellano): suppose `G` is a `σ`-compact TDLC group. Does `G` embed
into a compactly generated TDLC group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected

@[expose] public section

namespace MathlibExt.GroupTheory.TDLCEmbeddingCompactlyGeneratedOWR14298004Problem014Wanted

/-!
Source: Open problems on TDLC-groups (I. Leary and I. Castellano), in Mini-Workshop: Homological
aspects of TDLC-groups, Oberwolfach Reports 20 (2023), no. 55, p. 3135, Question 5, DOI
10.4171/OWR/2023/55. UnsolvedMath record UM-30005706 (`OWR-14298004-014`), dataset
ulamai/UnsolvedMath v1.8.0.

A TDLC group is a totally disconnected locally compact topological group; compactly generated means
generated as a group by a compact subset. An embedding is a continuous injective homomorphism with
possibly non-closed image, the weakest notion and the one Caprace and Cornulier use (Introduction);
their counterexample excludes every nontrivial continuous homomorphism, so the answer is negative
for closed embeddings too. Leary's own abstract in the same report (Remark 5, p. 3133) asks for a
TDLC version of the Higman-Neumann-Neumann embedding theorem or a counterexample.
-/

/-- Leary and Castellano's Question 5 (Oberwolfach Report 55/2023, p. 3135): every `σ`-compact
totally disconnected locally compact group `G` embeds, by a continuous injective homomorphism,
into a totally disconnected locally compact group `H` that is compactly generated (generated as a
group by a compact subset `K`). The statement follows the convention that TDLC groups are
Hausdorff: Mathlib's `LocallyCompactSpace` and `TotallyDisconnectedSpace` do not imply it, so `G`
and `H` both carry `T2Space`. -/
def sigmaCompactTDLCEmbedsInCompactlyGenerated : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G],
    ∃ (H : Type) (_ : Group H) (_ : TopologicalSpace H) (_ : IsTopologicalGroup H)
      (_ : T2Space H) (_ : LocallyCompactSpace H) (_ : TotallyDisconnectedSpace H),
      (∃ K : Set H, IsCompact K ∧ Subgroup.closure K = ⊤) ∧
        ∃ φ : G →* H, Continuous φ ∧ Function.Injective φ

/--
Resolved false: Caprace and Cornulier constructed a second countable (hence `σ`-compact),
topologically simple totally disconnected locally compact group `S` such that every continuous (or
even abstract) homomorphism from `S` to a compactly generated locally compact group is trivial; `S`
is nontrivial, so it admits no continuous injective homomorphism into a compactly generated TDLC
group. Source: Open problems on TDLC-groups (I. Leary and I. Castellano), in Mini-Workshop:
Homological aspects of TDLC-groups, Oberwolfach Reports 20 (2023), no. 55, p. 3135, Question 5, DOI
10.4171/OWR/2023/55; resolution: P.-E. Caprace and Y. Cornulier, On embeddings into compactly
generated groups, Pacific J. Math. 269 (2014), 305-321, arXiv:1211.5509, Theorem 1.3: there exists a
second countable (hence σ-compact), topologically simple totally disconnected l.c. group S such that
every continuous (or even abstract) homomorphism of S to any compactly generated l.c. group is
trivial; embedding = continuous injective homomorphism (Introduction),
https://arxiv.org/abs/1211.5509.
-/
public theorem_wanted sigmaCompactTDLCEmbedsInCompactlyGenerated_refuted :
    ¬ sigmaCompactTDLCEmbedsInCompactlyGenerated

end MathlibExt.GroupTheory.TDLCEmbeddingCompactlyGeneratedOWR14298004Problem014Wanted
