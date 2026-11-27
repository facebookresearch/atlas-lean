/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.MatroidIntersection.Augmentation
public import Mathlib.Combinatorics.Matroid.Rank.ENat
import MathlibExt.Combinatorics.Matroid.MatroidIntersection

/-!
# The stopping certificate for matroid intersection

For matroids on a common full finite ground and a common independent set with no joining path,
the vertices that can reach the sink set form the first part of a tight rank cut.
The proof finds bases of both parts from the current set;
Edmonds' weak bound then gives optimality. Successive shortest-path toggles from the empty
set terminate. The run is a relation, not an implementation of an independence oracle or
a shortest-path search.

Source: M. X. Goemans, MIT 18.438, Lecture 11, “Matroid Intersection” (22 October 2009,
scribe Jacob Steinhardt), Definition 3 (p. 11-3) and the augmenting-path proof of Theorem 4
(pp. 11-3–11-4; stopping certificate on p. 11-4; statement on p. 11-2).
-/

@[expose] public section

namespace Matroid.Intersection

open Set Relation
open MathlibExt.Combinatorics.Matroid.MatroidIntersectionWanted (edmonds_matroid_intersection')
open scoped symmDiff

variable {α : Type*} (M N : Matroid α) (I : Set α)

/-- The algorithm stops precisely when there is no walk between the two sets of endpoints. -/
def Terminal : Prop := ¬ ∃ n p, Joins M N I n p

/-- All vertices from which a directed exchange walk reaches an outside vertex addable to `I`
in `N`. Each such addable vertex reaches itself by a walk of length zero. -/
def canReachSink : Set α := {u | ∃ v ∈ addable N I, ReflTransGen (Arc M N I) u v}

/-- A relational augmentation: choose any minimum-length joining walk and toggle its vertices. -/
def Step (J : Set α) : Prop := ∃ n p, Shortest M N I n p ∧ J = I ∆ vertices n p

variable {M N I} {J : Set α}

private theorem exists_walk_of_reaches {u v : α} (h : ReflTransGen (Arc M N I) u v) :
    ∃ n p, Walk M N I n p ∧ p 0 = u ∧ p n = v := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ ↦ _, fun i hi ↦ by omega, rfl, rfl⟩
  | @head u w e _ ih =>
    obtain ⟨n, p, hp, rfl, hend⟩ := ih
    let q : ℕ → α := fun | 0 => u | i + 1 => p i
    refine ⟨n + 1, q, ?_, rfl, hend⟩
    rintro (_ | i) hi
    · exact e
    · exact hp i (by omega)

private theorem basis_on_side {U : Set α} (hI : M.Indep I) (hU : U ⊆ M.E)
    (noSource : ∀ x ∈ U, x ∉ addable M I)
    (backward : ∀ {x y}, Exchange M I y x → x ∈ U → y ∈ U) :
    M.IsBasis (I ∩ U) U := by
  have hIU : M.Indep (I ∩ U) := hI.subset inter_subset_left
  apply hIU.isBasis_of_subset_of_subset_closure inter_subset_right
  intro x hx
  by_cases hxI : x ∈ I
  · exact M.subset_closure _ hIU.subset_ground ⟨hxI, hx⟩
  have hcl := hI.mem_closure_iff'.2 ⟨hU hx, fun hi ↦ (noSource x hx ⟨hxI, hi⟩).elim⟩
  have hC := hI.fundCircuit_isCircuit hcl hxI
  apply M.closure_subset_closure _ (hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit x I))
  rintro y ⟨hyC, hyx⟩
  have hyI := (M.fundCircuit_subset_insert x I hyC).resolve_left hyx
  exact ⟨hyI, backward ⟨hyI, hxI, (hI.mem_fundCircuit_iff hcl hxI).1 hyC⟩ hx⟩

/-- Let `M` and `N` both have the whole finite type as ground set, and let `I` be independent in
both. Suppose there is no directed exchange walk from `addable M I` to `addable N I`. Let `U`
consist of all vertices from which some vertex of `addable N I` can be reached, including the
addable vertices themselves. The rank of `U` in `M` is the size of `I ∩ U`, and the rank of its
complement in `N` is the size of `I ∖ U`. These ranks sum to the size of `I`, so no common
independent set has larger cardinality. -/
theorem Terminal.certificate [Finite α] (stop : Terminal M N I) (hM : M.Indep I) (hN : N.Indep I)
    (groundM : M.E = univ) (groundN : N.E = univ) :
    let U := canReachSink M N I
    M.eRk U = (I ∩ U).encard ∧ N.eRk Uᶜ = (I \ U).encard ∧
      M.eRk U + N.eRk Uᶜ = I.encard ∧ ∀ J, M.Indep J → N.Indep J → J.ncard ≤ I.ncard := by
  classical
  let U := canReachSink M N I
  have pred {y x} (e : Arc M N I y x) (hx : x ∈ U) : y ∈ U := by
    obtain ⟨z, hz, h⟩ := hx
    exact ⟨z, hz, h.head e⟩
  have bM : M.IsBasis (I ∩ U) U := by
    apply basis_on_side hM (groundM ▸ subset_univ _)
    · rintro x ⟨z, hz, h⟩ hs
      obtain ⟨n, p, hp, rfl, rfl⟩ := exists_walk_of_reaches h
      exact stop ⟨n, p, hs, hp, hz⟩
    · exact fun e hx ↦ pred (.inl e) hx
  have bN : N.IsBasis (I ∩ Uᶜ) Uᶜ := by
    apply basis_on_side hN (groundN ▸ subset_univ _)
    · exact fun x hx hs ↦ hx ⟨x, hs, .refl⟩
    · exact fun e hx hy ↦ hx (pred (.inr e) hy)
  have rM := bM.eRk_eq_encard
  have rN : N.eRk Uᶜ = (I \ U).encard := bN.eRk_eq_encard
  have tight : M.eRk U + N.eRk Uᶜ = I.encard := by
    rw [rM, rN, ← coe_ncard_eq_encard, ← coe_ncard_eq_encard, ← Nat.cast_add,
      ncard_inter_add_ncard_sdiff_eq_ncard, coe_ncard_eq_encard]
  refine ⟨rM, rN, tight, ?_⟩
  intro J jM jN
  have weak := (edmonds_matroid_intersection' (M₁ := M) (M₂ := N) (k := J.ncard)).mp
    ⟨J.toFinite.toFinset, by simpa using jM, by simpa using jN, (ncard_eq_toFinset_card J).le⟩ U
  exact ENat.natCast_le_natCast.mp (weak.trans_eq (tight.trans I.toFinite.cast_ncard_eq.symm))

private theorem exists_step (h : ¬ Terminal M N I) : ∃ J, Step M N I J := by
  classical
  obtain hex : ∃ n, ∃ p, Joins M N I n p := not_not.mp h
  obtain ⟨p, hp⟩ := Nat.find_spec hex
  exact ⟨_, Nat.find hex, p, ⟨hp, fun _ q hq ↦ Nat.find_min' hex ⟨q, hq⟩⟩, rfl⟩

private theorem Step.correct [Finite α] (s : Step M N I J) (hM : M.Indep I) (hN : N.Indep I) :
    M.Indep J ∧ N.Indep J ∧ J.ncard = I.ncard + 1 := by
  obtain ⟨_, _, hp, rfl⟩ := s
  exact hp.augment hM hN

/-- Let `M` and `N` be matroids on a finite type and let `I` be independent in both. There is no
infinite sequence of shortest joining path augmentations starting at `I`: each step decreases the
number of elements of the type outside the current set. -/
theorem accessible [Finite α] (hM : M.Indep I) (hN : N.Indep I) :
    Acc (fun J I ↦ Step M N I J) I := by
  induction I using (measure (fun K : Set α ↦ Nat.card α - K.ncard)).wf.induction with
  | h I ih =>
    refine .intro _ fun J s ↦ ?_
    obtain ⟨hjM, hjN, hc⟩ := s.correct hM hN
    apply ih J _ hjM hjN
    change Nat.card α - J.ncard < Nat.card α - I.ncard
    have hb := ncard_le_ncard (subset_univ J)
    rw [ncard_univ] at hb
    omega

private theorem exists_terminal (acc : Acc (fun J I ↦ Step M N I J) I) :
    ∃ J, ReflTransGen (Step M N) I J ∧ Terminal M N J := by
  induction acc with
  | intro I _ ih =>
    by_cases h : Terminal M N I
    · exact ⟨I, .refl, h⟩
    obtain ⟨K, s⟩ := exists_step h
    obtain ⟨J, run, hJ⟩ := ih K s
    exact ⟨J, run.head s, hJ⟩

/-- Let `M` and `N` be matroids whose ground sets are both the whole finite type. From the empty
set there exists a finite run of shortest joining path augmentations to a common independent set
`I` with no joining walk. Let `U` be the vertices that can reach `addable N I` in the final graph.
The rank of `U` in `M` plus the rank of its complement in `N` equals the size of `I`, and `I` has
maximum cardinality among all common independent sets. -/
theorem exists_run_from_empty [Finite α] (groundM : M.E = univ) (groundN : N.E = univ) :
    ∃ I, ReflTransGen (Step M N) ∅ I ∧ Terminal M N I ∧ M.Indep I ∧ N.Indep I ∧
      (M.eRk (canReachSink M N I) + N.eRk (canReachSink M N I)ᶜ = I.encard) ∧
      ∀ J, M.Indep J → N.Indep J → J.ncard ≤ I.ncard := by
  obtain ⟨I, run, stop⟩ := exists_terminal (accessible M.empty_indep N.empty_indep)
  have common : M.Indep I ∧ N.Indep I := by
    clear stop
    induction run with
    | refl => exact ⟨M.empty_indep, N.empty_indep⟩
    | tail _ s ih => exact ⟨(s.correct ih.1 ih.2).1, (s.correct ih.1 ih.2).2.1⟩
  obtain ⟨-, -, tight, opt⟩ := stop.certificate common.1 common.2 groundM groundN
  exact ⟨I, run, stop, common.1, common.2, tight, opt⟩

end Matroid.Intersection
