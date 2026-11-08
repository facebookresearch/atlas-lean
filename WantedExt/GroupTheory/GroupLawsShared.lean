/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared definitions: consequence and independent bases of laws and quasi-identities

Semantic consequence and independent bases for laws (identities) and quasi-identities of groups.
Shared by the WantedExt statements of Kourovka Notebook Problems 4.64, 5.43, 5.50 and 5.51, so
that they speak about the same notions.

Laws and varieties are `SatisfiesLaws` of the Kourovka 11.21 entry, reused here: a law is a word
`w` of the free group `FreeGroup ℕ` on countably many letters, a group satisfies it when every
homomorphism `FreeGroup ℕ →* G` maps `w` to `1`, the groups satisfying a set `W` of laws form the
variety defined by `W`, and every variety arises this way. Quasi-identities
`∀ x, (u₁ = 1 ∧ ⋯ ∧ uₖ = 1 → w = 1)` and the groups satisfying a set of them are `QuasiIdentity`
and `Models` of the Kourovka 14.25 entry, reused here. Consequence is semantic, over all groups in
`Type`; by the completeness theorem it agrees with derivability, and a law or quasi-identity that
fails in some group fails in a countable subgroup, so the universe does not matter.
-/

module

public import WantedExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted
public import WantedExt.GroupTheory.QuasivarietyMaximalSubquasivarietiesKourovka14Problem25Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.GroupLawsShared

open MathlibExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted (SatisfiesLaws)
open MathlibExt.GroupTheory.QuasivarietyMaximalSubquasivarietiesKourovka14Problem25Wanted
  (QuasiIdentity Models)

/-- The law `w` is a consequence of the laws `W`: it holds in every group satisfying `W`. -/
def LawConsequence (W : Set (FreeGroup ℕ)) (w : FreeGroup ℕ) : Prop :=
  ∀ (G : Type) [Group G], SatisfiesLaws W G → SatisfiesLaws {w} G

/-- The variety defined by `W` has an independent basis of identities: a set `B` of laws with the
same consequences as `W` none of which is a consequence of the others. -/
def HasIndependentLawBasis (W : Set (FreeGroup ℕ)) : Prop :=
  ∃ B : Set (FreeGroup ℕ), (∀ w, LawConsequence B w ↔ LawConsequence W w) ∧
    ∀ b ∈ B, ¬ LawConsequence (B \ {b}) b

/-- The quasi-identity `q` is a consequence of the set `Q` of quasi-identities: it holds in every
group in which all members of `Q` hold. -/
def QuasiIdentityConsequence (Q : Set QuasiIdentity) (q : QuasiIdentity) : Prop :=
  ∀ (G : Type) [Group G], Models Q G → q.HoldsIn G

/-- The quasi-identities of `G` have an independent basis: a set `B` of quasi-identities whose
consequences are exactly the quasi-identities holding in `G`, none of which is a consequence of
the others. -/
def HasIndependentQuasiIdentityBasis (G : Type) [Group G] : Prop :=
  ∃ B : Set QuasiIdentity, (∀ q, QuasiIdentityConsequence B q ↔ q.HoldsIn G) ∧
    ∀ b ∈ B, ¬ QuasiIdentityConsequence (B \ {b}) b

end MathlibExt.GroupTheory.GroupLawsShared
