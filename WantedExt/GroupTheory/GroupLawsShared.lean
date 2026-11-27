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

/-- **Consequence of a set of laws.** Let $F$ be the free group on countably many generators
$x_0, x_1, x_2, \dots$, let $W \subseteq F$ be a set of laws and let $w \in F$. Then $w$ is a
consequence of $W$ if $w$ holds in every group $G$ satisfying all laws in $W$: whenever every
homomorphism $F \to G$ sends each element of $W$ to $1$, every homomorphism $F \to G$ sends $w$
to $1$. -/
def LawConsequence (W : Set (FreeGroup ℕ)) (w : FreeGroup ℕ) : Prop :=
  ∀ (G : Type) [Group G], SatisfiesLaws W G → SatisfiesLaws {w} G

/-- **Independent basis of laws.** Let $F$ be the free group on countably many generators
$x_0, x_1, x_2, \dots$ and let $W \subseteq F$ be a set of laws. The variety defined by $W$ has an
independent basis of identities if there is a set $B \subseteq F$ of laws such that a law is a
consequence of $B$ exactly when it is a consequence of $W$, and no $b \in B$ is a consequence of
$B \setminus \{b\}$. -/
def HasIndependentLawBasis (W : Set (FreeGroup ℕ)) : Prop :=
  ∃ B : Set (FreeGroup ℕ), (∀ w, LawConsequence B w ↔ LawConsequence W w) ∧
    ∀ b ∈ B, ¬ LawConsequence (B \ {b}) b

/-- **Consequence of a set of quasi-identities.** Let $Q$ be a set of quasi-identities and $q$ a
quasi-identity. Then $q$ is a consequence of $Q$ if $q$ holds in every group in which all members
of $Q$ hold. -/
def QuasiIdentityConsequence (Q : Set QuasiIdentity) (q : QuasiIdentity) : Prop :=
  ∀ (G : Type) [Group G], Models Q G → q.HoldsIn G

/-- **Independent basis of quasi-identities.** The quasi-identities of a group $G$ have an
independent basis if there is a set $B$ of quasi-identities such that a quasi-identity is a
consequence of $B$ exactly when it holds in $G$, and no $b \in B$ is a consequence of
$B \setminus \{b\}$. -/
def HasIndependentQuasiIdentityBasis (G : Type) [Group G] : Prop :=
  ∃ B : Set QuasiIdentity, (∀ q, QuasiIdentityConsequence B q ↔ q.HoldsIn G) ∧
    ∀ b ∈ B, ¬ QuasiIdentityConsequence (B \ {b}) b

end MathlibExt.GroupTheory.GroupLawsShared
