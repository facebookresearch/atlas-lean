/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Biology.ComputationalBiology.RootedSPRAgreementForestDefs

/-!
# Tests for the rooted SPR distance definitions

* A tree is at rSPR distance `0` from itself, and has the one-part rooted agreement forest, so
  its maximum agreement forest number with itself is `0` too.
* Any two trees have the agreement forest of singletons: the minimal subtree of one taxon is its
  leaf, so `m(T, T')` is at most the number of labels, `ρ` included, minus one.
* The decision problem accepts a well-formed tree paired with itself for every bound, and
  rejects instances with fewer than two taxa other than the root and malformed trees.
-/

namespace CSLibExtTest.Biology.ComputationalBiology.RootedSPRAgreementForestDefs

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open MetaMathlibExt.Complexity.NPComplete.TBRDistance
open WantedExt.Biology.ComputationalBiology.RootedSPRAgreementForestWanted

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- The rooted restrictions of a tree and itself agree on every set of taxa. -/
theorem rootedRestrictionsAgree_refl (ρ : Y) (T : UnrootedBinaryTree Y) (L : Finset Y) :
    RootedRestrictionsAgree ρ T T L :=
  fun _ _ _ _ _ _ _ => Iff.rfl

/-- A tree is transformed into itself by zero rSPR operations. -/
theorem rsprDist_self (ρ : Y) (T : UnrootedBinaryTree Y) : rsprDist ρ T T = 0 :=
  Nat.eq_zero_of_le_zero <| Nat.sInf_le
    ⟨fun _ => T, rfl, ⟨RelIso.refl _, fun _ => rfl⟩, fun i => i.elim0⟩

/-- The one-part partition is a rooted agreement forest for a tree and itself, so the maximum
agreement forest number of a tree with itself is `0`. -/
theorem rootedMafNumber_self (ρ : Y) (T : UnrootedBinaryTree Y) :
    rootedMafNumber ρ T T = 0 := by
  have hne : (Finset.univ : Finset Y) ≠ ⊥ := (Finset.univ_nonempty_iff.2 ⟨ρ⟩).ne_empty
  refine Nat.eq_zero_of_le_zero <| Nat.sInf_le ⟨Finpartition.indiscrete hne, ⟨?_, ?_⟩, ?_⟩
  · intro L _
    exact rootedRestrictionsAgree_refl ρ T L
  · intro L hL L' hL' hLL'
    simp only [Finpartition.indiscrete_parts, Finset.mem_singleton] at hL hL'
    exact absurd (hL.trans hL'.symm) hLL'
  · simp

omit [Fintype Y] [DecidableEq Y] in
/-- The minimal subtree spanned by one taxon is its leaf: a path from a vertex to itself is
empty. -/
theorem spanVerts_singleton (T : UnrootedBinaryTree Y) (x : Y) :
    spanVerts T {x} = {(T.label x : T.V)} := by
  ext v
  simp only [spanVerts, Finset.mem_singleton, exists_eq_left, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨p, hp, hv⟩
    rw [SimpleGraph.Walk.eq_nil_iff_nil.2 (SimpleGraph.Walk.isPath_iff_nil.1 hp)] at hv
    simpa using hv
  · rintro rfl
    exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by simp⟩

/-- The rooted restrictions to a set of at most two taxa always agree: there are no three
distinct taxa other than the root to compare. -/
theorem rootedRestrictionsAgree_singleton (ρ : Y) (T T' : UnrootedBinaryTree Y) (x : Y) :
    RootedRestrictionsAgree ρ T T' {x} := by
  intro a ha b hb c hc hnd
  simp only [Finset.mem_singleton] at ha hb
  subst ha hb
  simp at hnd

/-- The partition into singletons is a rooted agreement forest for any two trees, so `m(T, T')`
is at most the number of labels, `ρ` included, minus one. -/
theorem rootedMafNumber_le (ρ : Y) (T T' : UnrootedBinaryTree Y) :
    rootedMafNumber ρ T T' ≤ Fintype.card Y - 1 := by
  have hcard : 0 < Fintype.card Y := Fintype.card_pos_iff.2 ⟨ρ⟩
  refine Nat.sInf_le ⟨⊥, ⟨?_, ?_⟩, ?_⟩
  · intro L hL
    obtain ⟨x, -, rfl⟩ := Finpartition.mem_bot_iff.1 hL
    exact rootedRestrictionsAgree_singleton ρ T T' x
  · intro L hL L' hL' hLL'
    obtain ⟨x, -, rfl⟩ := Finpartition.mem_bot_iff.1 hL
    obtain ⟨y, -, rfl⟩ := Finpartition.mem_bot_iff.1 hL'
    have hxy : x ≠ y := fun h => hLL' (h ▸ rfl)
    simp only [spanVerts_singleton, Set.disjoint_singleton]
    exact ⟨fun h => hxy (T.label.injective (Subtype.ext h)),
      fun h => hxy (T'.label.injective (Subtype.ext h))⟩
  · rw [Finpartition.card_bot, Finset.card_univ]
    omega

/-- A well-formed tree on at least three labels, paired with itself, is a yes-instance for
every bound `K`. -/
theorem rsprDistanceDec_self {m : ℕ} (hm : 2 ≤ m) {t : TreeData} (h : IsPhyloTree (m + 1) t)
    (K : ℕ) :
    rsprDistanceDec (MetaMathlibExt.BitstringEncoding.bitEncode
      ((m, t, t, K) : RSPRDistanceInstance)) = true := by
  have hf : RSPRDistanceFeasible (m, t, t, K) :=
    ⟨h, h, by simp only [rsprDist_self]; exact Nat.zero_le K⟩
  simp [rsprDistanceDec, hm, hf]

/-- Instances with fewer than two taxa other than the root are rejected, whatever the trees and
the bound. -/
theorem rsprDistanceDec_lt_two {m : ℕ} (hm : m < 2) (t₁ t₂ : TreeData) (K : ℕ) :
    rsprDistanceDec (MetaMathlibExt.BitstringEncoding.bitEncode
      ((m, t₁, t₂, K) : RSPRDistanceInstance)) = false := by
  have : ¬ 2 ≤ m := by omega
  simp [rsprDistanceDec, this]

/-- Malformed trees are rejected: the empty tree data list no leaf, while three labels need
three leaves. -/
example : rsprDistanceDec (MetaMathlibExt.BitstringEncoding.bitEncode
    ((2, (0, [], []), (0, [], []), 5) : RSPRDistanceInstance)) = false := by
  have : ¬ RSPRDistanceFeasible ((2, (0, [], []), (0, [], []), 5) : RSPRDistanceInstance) :=
    fun ⟨h₁, _, _⟩ => by simpa using h₁.length
  simp [rsprDistanceDec, this]

end CSLibExtTest.Biology.ComputationalBiology.RootedSPRAgreementForestDefs
