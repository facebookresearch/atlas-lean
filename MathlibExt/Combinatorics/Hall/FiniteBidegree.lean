/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card

/-!
# Hall's condition from degree bounds

Let `related : Source → Target → Prop` be a relation between finite types. If every source is
related to at least `d` targets and every target to at most `d` sources, with `d > 0`, then the
relation satisfies Hall's condition, so (by Hall's marriage theorem) it has a matching that
saturates the sources. The proof double-counts the related pairs with source in a given set.
The classical special case is König's theorem that a `d`-regular bipartite graph has a perfect
matching.

## Main results

* `finiteRelationHall_of_bidegree`: degree bounds `d ≤ deg(source)`, `deg(target) ≤ d` imply
  Hall's condition.
* `finiteRelationHall_of_certificateEmbeddings`: the same with the degree bounds witnessed by
  embeddings `Fin d ↪ {targets related to source}` and `{sources related to target} ↪ Fin d`.
* `finiteRelation_exists_injective_of_certificateEmbeddings`: under those embeddings, there is
  an injective `Source → Target` choosing a related target for every source.

## References

* D. König, *Über Graphen und ihre Anwendung auf Determinantentheorie und Mengenlehre*,
  Math. Ann. 77 (1916).
* L. Lovász, M. D. Plummer, *Matching Theory* (1986), Chapter 1.
-/

@[expose] public section

open Finset

/-- **Hall's condition from degree bounds.** If every source is related to at least `degree`
targets and every target to at most `degree` sources, with `0 < degree`, then every finite set of
sources is related to at least as many targets. This is the double-counting step behind König's
theorem that regular bipartite graphs have perfect matchings (D. König, 1916). See also
`Fintype.all_card_le_filter_rel_iff_exists_injective` (Hall's marriage theorem) to turn the
conclusion into a matching. -/
theorem finiteRelationHall_of_bidegree
    {Source Target : Type*}
    [Fintype Source] [Fintype Target]
    (related : Source -> Target -> Prop) [DecidableRel related]
    (degree : Nat) (hdegree : 0 < degree)
    (hsource : forall source,
      degree <= (Finset.univ.filter (related source)).card)
    (htarget : forall target,
      (Finset.univ.filter fun source => related source target).card <= degree) :
    forall sources : Finset Source,
      sources.card <=
        (Finset.univ.filter fun target =>
          ∃ source ∈ sources, related source target).card := by
  intro sources
  let targets : Finset Target :=
    Finset.univ.filter fun target =>
      ∃ source ∈ sources, related source target
  have hleft : degree * sources.card <=
      ∑ source ∈ sources,
        (Finset.univ.filter (related source)).card := by
    calc
      degree * sources.card = ∑ _source ∈ sources, degree := by
        simp [Nat.mul_comm]
      _ <= ∑ source ∈ sources,
          (Finset.univ.filter (related source)).card :=
        Finset.sum_le_sum fun source _ => hsource source
  have hcount :
      (∑ source ∈ sources,
          (Finset.univ.filter (related source)).card) =
        ∑ target ∈ targets,
          (sources.filter fun source => related source target).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    rw [show (∑ target : Target,
        ∑ source ∈ sources, if related source target then 1 else 0) =
        ∑ target ∈ targets,
          ∑ source ∈ sources, if related source target then 1 else 0 by
      symm
      apply Finset.sum_subset (Finset.subset_univ targets)
      intro target _ htargetNot
      have hnone : ¬ ∃ source ∈ sources, related source target := by
        simpa [targets] using htargetNot
      apply Finset.sum_eq_zero
      intro source hsourceMem
      exact ite_eq_right_iff.mpr fun hrelated =>
        absurd ⟨source, hsourceMem, hrelated⟩ hnone]
  have hright :
      (∑ target ∈ targets,
          (sources.filter fun source => related source target).card) <=
        degree * targets.card := by
    calc
      (∑ target ∈ targets,
          (sources.filter fun source => related source target).card) <=
          ∑ _target ∈ targets, degree := by
        apply Finset.sum_le_sum
        intro target _
        calc
          (sources.filter fun source => related source target).card <=
              (Finset.univ.filter fun source =>
                related source target).card := by
            apply Finset.card_le_card
            intro source hsourceFiltered
            simp only [Finset.mem_filter] at hsourceFiltered ⊢
            exact ⟨Finset.mem_univ source, hsourceFiltered.2⟩
          _ <= degree := htarget target
      _ = degree * targets.card := by simp [Nat.mul_comm]
  have hmul : degree * sources.card <= degree * targets.card :=
    hleft.trans (hcount ▸ hright)
  exact Nat.le_of_mul_le_mul_left hmul hdegree

/-- Hall's condition from degree bounds given by embeddings: an embedding of `Fin degree` into the
targets related to each source gives the lower degree bound, and an embedding of the sources
related to each target into `Fin degree` gives the upper bound. -/
theorem finiteRelationHall_of_certificateEmbeddings
    {Source Target : Type*}
    [Finite Source] [Fintype Target]
    (related : Source -> Target -> Prop) [DecidableRel related]
    (degree : Nat) (hdegree : 0 < degree)
    (sourceCertificates : forall source,
      Fin degree ↪ {target : Target // related source target})
    (targetCertificateCode : forall target,
      {source : Source // related source target} ↪ Fin degree) :
    forall sources : Finset Source,
      sources.card <=
        (Finset.univ.filter fun target =>
          ∃ source ∈ sources, related source target).card := by
  let := Fintype.ofFinite Source
  apply finiteRelationHall_of_bidegree related degree hdegree
  · intro source
    have hcard := Fintype.card_le_of_embedding
      (sourceCertificates source)
    simpa [Fintype.card_subtype] using hcard
  · intro target
    have hcard := Fintype.card_le_of_embedding
      (targetCertificateCode target)
    simpa [Fintype.card_subtype] using hcard

/-- **Matchings in biregular relations.** If every source has at least `degree` related targets
and every target at most `degree` related sources (witnessed by embeddings), with `0 < degree`,
then some injective map sends each source to a related target. For a `d`-regular bipartite graph
this is König's perfect matching theorem (D. König, 1916). -/
theorem finiteRelation_exists_injective_of_certificateEmbeddings
    {Source Target : Type*}
    [Finite Source] [Finite Target]
    (related : Source -> Target -> Prop)
    (degree : Nat) (hdegree : 0 < degree)
    (sourceCertificates : forall source,
      Fin degree ↪ {target : Target // related source target})
    (targetCertificateCode : forall target,
      {source : Source // related source target} ↪ Fin degree) :
    exists matching : Source -> Target,
      Function.Injective matching ∧
        forall source, related source (matching source) := by
  classical
  let := Fintype.ofFinite Source
  let := Fintype.ofFinite Target
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective related).mp
  exact finiteRelationHall_of_certificateEmbeddings related degree hdegree
    sourceCertificates targetCertificateCode
