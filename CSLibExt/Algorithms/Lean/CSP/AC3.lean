/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic

/-!
# AC-3 arc consistency: soundness and termination

A binary constraint satisfaction problem (`BinaryCSP X D`) has variables `X`, values `D`, a list
of directed arcs `(x, y)` and, for each arc, the allowed pairs `allowed x y a b` (`x = a` together
with `y = b`). A *solution* within domains `dom : X → Finset D` assigns every variable a value of
its domain satisfying every arc (`IsSolution`). An arc `(x, y)` is *consistent* when every value
of `x` has a support in the domain of `y` (`ArcConsistent`).

AC-3 (Mackworth, *Consistency in networks of relations*, Artificial Intelligence 8 (1977);
Russell and Norvig, *Artificial Intelligence: A Modern Approach*, fourth edition, Figure 6.3)
keeps a queue of arcs, initially all of them. It pops an arc `(x, y)` and *revises* it, deleting
the values of `x` without a support in `y` (`revise`); if the domain of `x` shrank, it queues
every arc `(z, x)` with `z ≠ y`. `ac3` charges one unit per revision. Main results:

* `ac3_subset`: domains only shrink.
* `mem_ac3_of_isSolution`: no solution is lost, so the final domains still contain every solution;
  an emptied domain proves there is none (`not_isSolution_of_ac3_eq_empty`).
* `arcConsistent_ac3`: for constraints given symmetrically on both orientations of an arc
  (`Symmetric`) and arcs between distinct variables, every arc is consistent at the end.
* Termination: `ac3` is defined by well-founded recursion on the potential `queue length +
  ∑ x, |dom x| · indeg x` (`potential`), which every revision decreases by at least `1`; hence
  `ac3_time_le`: at most `|arcs| + ∑ x, |dom₀ x| · indeg x` revisions, that is `O(e d)` for `e`
  arcs and domains of size `d` (Mackworth and Freuder 1985).

## Cost model

`ac3` runs in `TimeM` and charges one unit per arc revision; a revision of `(x, y)` performs
`|dom x| · |dom y|` constraint checks, which are not charged separately. Queue and domain updates
are free.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.ArcConsistency

open Cslib.Algorithms.Lean

/-- A binary constraint satisfaction problem: directed arcs and, for each arc `(x, y)`, the
allowed value pairs `allowed x y a b`. -/
structure BinaryCSP (X D : Type*) where
  /-- The directed arcs. -/
  arcs : List (X × X)
  /-- `allowed x y a b`: the arc `(x, y)` allows `x = a` together with `y = b`. -/
  allowed : X → X → D → D → Bool

variable {X D : Type*} [DecidableEq X] [DecidableEq D] (P : BinaryCSP X D)

/-- A solution within the domains `dom`. -/
def IsSolution (dom : X → Finset D) (σ : X → D) : Prop :=
  (∀ x, σ x ∈ dom x) ∧ ∀ e ∈ P.arcs, P.allowed e.1 e.2 (σ e.1) (σ e.2) = true

/-- The arc `(x, y)` is consistent: every value of `x` has a support in the domain of `y`. -/
def ArcConsistent (dom : X → Finset D) (e : X × X) : Prop :=
  ∀ a ∈ dom e.1, ∃ b ∈ dom e.2, P.allowed e.1 e.2 a b = true

/-- Each constraint is given on both orientations of its arc, with the same allowed pairs. -/
def Symmetric : Prop := ∀ x y a b, P.allowed x y a b = P.allowed y x b a

/-- Revise the arc `(x, y)`: the values of `x` with a support in the domain of `y`. -/
def revise (dom : X → Finset D) (x y : X) : Finset D :=
  (dom x).filter fun a => ∃ b ∈ dom y, P.allowed x y a b = true

/-- The number of arcs into `x`. -/
def indeg (x : X) : ℕ := (P.arcs.filter fun e => e.2 = x).length

/-- The arcs queued after the domain of `x` shrank while revising `(x, y)`. -/
def requeue (x y : X) : List (X × X) := P.arcs.filter fun e => e.2 = x ∧ e.1 ≠ y

/-- The termination potential: queue length plus `∑ x, |dom x| · indeg x`. -/
def potential [Fintype X] (dom : X → Finset D) (q : List (X × X)) : ℕ :=
  q.length + ∑ x, (dom x).card * indeg P x

omit [DecidableEq D] in
theorem length_requeue_le (x y : X) : (requeue P x y).length ≤ indeg P x := by
  have : requeue P x y = (P.arcs.filter fun e => e.2 = x).filter fun e => e.1 ≠ y := by
    simp only [requeue, List.filter_filter, Bool.decide_and]
    congr 1
    funext e
    exact Bool.and_comm _ _
  rw [this]
  exact List.length_filter_le _ _

omit [DecidableEq X] [DecidableEq D] in
theorem revise_subset (dom : X → Finset D) (x y : X) : revise P dom x y ⊆ dom x :=
  Finset.filter_subset _ _

omit [DecidableEq D] in
/-- A revision that shrinks the domain of `x` lowers the potential, even after requeueing. -/
theorem potential_lt [Fintype X] (dom : X → Finset D) (x y : X) (q : List (X × X))
    (h : revise P dom x y ≠ dom x) :
    potential P (Function.update dom x (revise P dom x y)) (q ++ requeue P x y) <
      potential P dom ((x, y) :: q) := by
  have hlt : (revise P dom x y).card < (dom x).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨revise_subset P dom x y, h⟩)
  have hr := length_requeue_le P x y
  have hsplit : ∀ g : X → ℕ, ∑ v, g v = g x + ∑ v ∈ Finset.univ.erase x, g v := fun g =>
    (Finset.add_sum_erase _ g (Finset.mem_univ x)).symm
  have hrest : ∑ v ∈ Finset.univ.erase x,
      (Function.update dom x (revise P dom x y) v).card * indeg P v =
      ∑ v ∈ Finset.univ.erase x, (dom v).card * indeg P v :=
    Finset.sum_congr rfl fun v hv => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
  unfold potential
  rw [hsplit, hsplit (fun v => (dom v).card * indeg P v), hrest, Function.update_self,
    List.length_append, List.length_cons]
  have : (revise P dom x y).card * indeg P x + indeg P x ≤ (dom x).card * indeg P x := by
    have := Nat.mul_le_mul_right (indeg P x) (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    exact this
  omega

/-- AC-3 from domains `dom` with the queue `q`; one unit per revision. -/
def ac3 [Fintype X] : (X → Finset D) → List (X × X) → TimeM ℕ (X → Finset D)
  | dom, [] => pure dom
  | dom, (x, y) :: q => do
      TimeM.tick 1
      if revise P dom x y = dom x then ac3 dom q
      else ac3 (Function.update dom x (revise P dom x y)) (q ++ requeue P x y)
termination_by dom q => potential P dom q
decreasing_by
  · simp [potential]
  · exact potential_lt P dom x y q ‹_›

/-- AC-3 on the whole problem: all arcs queued. -/
def ac3All [Fintype X] (dom : X → Finset D) : TimeM ℕ (X → Finset D) := ac3 P dom P.arcs

/-! ## Soundness -/

/-- **Domains only shrink.** -/
theorem ac3_subset [Fintype X] (dom : X → Finset D) (q : List (X × X)) (v : X) :
    (ac3 P dom q).ret v ⊆ dom v := by
  match q with
  | [] => simp [ac3.eq_1]
  | (x, y) :: q =>
      rw [ac3.eq_2]
      simp only [TimeM.ret_bind]
      split_ifs with h
      · exact ac3_subset dom q v
      · refine (ac3_subset _ _ v).trans ?_
        by_cases hv : v = x
        · subst hv; rw [Function.update_self]; exact revise_subset P dom v y
        · rw [Function.update_of_ne hv]
termination_by potential P dom q
decreasing_by
  · simp [potential]
  · exact potential_lt P dom x y q h

omit [DecidableEq X] [DecidableEq D] in
/-- A revision keeps every value of a solution. -/
theorem mem_revise_of_isSolution {dom : X → Finset D} {σ : X → D} (hσ : IsSolution P dom σ)
    {x y : X} (he : (x, y) ∈ P.arcs) : σ x ∈ revise P dom x y := by
  unfold revise
  rw [Finset.mem_filter]
  exact ⟨hσ.1 x, σ y, hσ.1 y, hσ.2 _ he⟩

/-- **No solution is lost**: every solution within `dom` stays within the final domains, when
the queue holds arcs of the problem. -/
theorem isSolution_ac3 [Fintype X] (dom : X → Finset D) (q : List (X × X))
    (hq : ∀ e ∈ q, e ∈ P.arcs)
    (σ : X → D) (hσ : IsSolution P dom σ) : IsSolution P (ac3 P dom q).ret σ := by
  match q with
  | [] => simpa [ac3.eq_1] using hσ
  | (x, y) :: q =>
      have hxy := hq (x, y) List.mem_cons_self
      rw [ac3.eq_2]
      simp only [TimeM.ret_bind]
      split_ifs with h
      · exact isSolution_ac3 dom q (fun e he => hq e (List.mem_cons_of_mem _ he)) σ hσ
      · refine isSolution_ac3 _ _ (fun e he => ?_) σ ⟨fun v => ?_, hσ.2⟩
        · rcases List.mem_append.1 he with he | he
          · exact hq e (List.mem_cons_of_mem _ he)
          · exact (List.mem_filter.1 he).1
        · by_cases hv : v = x
          · subst hv; rw [Function.update_self]; exact mem_revise_of_isSolution P hσ hxy
          · rw [Function.update_of_ne hv]; exact hσ.1 v
termination_by potential P dom q
decreasing_by
  · simp [potential]
  · exact potential_lt P dom x y q h

/-- Every solution within the initial domains lies within AC-3's domains. -/
theorem mem_ac3_of_isSolution [Fintype X] {dom : X → Finset D} {σ : X → D} (hσ : IsSolution P dom σ)
    (v : X) : σ v ∈ (ac3All P dom).ret v :=
  (isSolution_ac3 P dom P.arcs (fun _ he => he) σ hσ).1 v

/-- If AC-3 empties a domain, the problem has no solution. -/
theorem not_isSolution_of_ac3_eq_empty [Fintype X] {dom : X → Finset D} {v : X}
    (hv : (ac3All P dom).ret v = ∅) (σ : X → D) : ¬IsSolution P dom σ := fun hσ => by
  have := mem_ac3_of_isSolution P hσ v
  rw [hv] at this
  exact Finset.notMem_empty _ this

/-! ## Arc consistency of the result -/

omit [DecidableEq D] in
/-- One revision makes its arc consistent and keeps the arcs that were consistent and are not
requeued. -/
theorem arcConsistent_step (hsym : Symmetric P) (dom : X → Finset D) (x y : X) (hxy : x ≠ y)
    (e : X × X) (hne : e.1 ≠ e.2)
    (he : e = (x, y) ∨ ArcConsistent P dom e)
    (hreq : revise P dom x y ≠ dom x → e ∉ requeue P x y) (hmem : e ∈ P.arcs) :
    ArcConsistent P (Function.update dom x (revise P dom x y)) e := by
  obtain ⟨u, v⟩ := e
  simp only at hne
  intro a ha
  simp only at ha ⊢
  by_cases hu : u = x
  · subst hu
    rw [Function.update_self] at ha
    rw [Function.update_of_ne (Ne.symm hne)]
    rcases he with he | he
    · cases he
      obtain ⟨-, b, hb, hab⟩ := Finset.mem_filter.1 ha
      exact ⟨b, hb, hab⟩
    · exact he a (revise_subset P dom u y ha)
  · rw [Function.update_of_ne hu] at ha
    rcases he with he | he
    · cases he; exact absurd rfl hu
    by_cases hv : v = x
    · subst hv
      rw [Function.update_self]
      obtain ⟨b, hb, hab⟩ := he a ha
      by_cases hch : revise P dom v y = dom v
      · exact ⟨b, hch ▸ hb, hab⟩
      · have hy : u = y := by
          by_contra hy
          exact hreq hch (List.mem_filter.2 ⟨hmem, by simp [hy]⟩)
        subst hy
        refine ⟨b, Finset.mem_filter.2 ⟨hb, a, ha, ?_⟩, hab⟩
        rw [hsym]; exact hab
    · rw [Function.update_of_ne hv]
      exact he a ha

/-- The invariant: every arc of the problem outside the queue stays consistent, and at the end
the queue is empty. -/
theorem arcConsistent_ac3_of_inv [Fintype X] (hsym : Symmetric P)
    (hdist : ∀ e ∈ P.arcs, e.1 ≠ e.2) (dom : X → Finset D) (q : List (X × X))
    (hq : ∀ e ∈ q, e ∈ P.arcs) (hinv : ∀ e ∈ P.arcs, e ∉ q → ArcConsistent P dom e) :
    ∀ e ∈ P.arcs, ArcConsistent P (ac3 P dom q).ret e := by
  match q with
  | [] => simpa [ac3.eq_1] using hinv
  | (x, y) :: q =>
      have hxy := hdist (x, y) (hq (x, y) List.mem_cons_self)
      rw [ac3.eq_2]
      simp only [TimeM.ret_bind]
      split_ifs with h
      · refine arcConsistent_ac3_of_inv hsym hdist dom q
          (fun e he => hq e (List.mem_cons_of_mem _ he)) fun e he heq => ?_
        by_cases hexy : e = (x, y)
        · subst hexy
          intro a ha
          rw [← h] at ha
          obtain ⟨-, b, hb, hab⟩ := Finset.mem_filter.1 ha
          exact ⟨b, hb, hab⟩
        · exact hinv e he (by simp [hexy, heq])
      · refine arcConsistent_ac3_of_inv hsym hdist _ _ (fun e he => ?_) fun e he heq => ?_
        · rcases List.mem_append.1 he with he | he
          · exact hq e (List.mem_cons_of_mem _ he)
          · exact (List.mem_filter.1 he).1
        · have hnq : e ∉ q := fun h' => heq (List.mem_append_left _ h')
          have hnr : e ∉ requeue P x y := fun h' => heq (List.mem_append_right _ h')
          refine arcConsistent_step P hsym dom x y hxy e (hdist e he) ?_ (fun _ => hnr) he
          by_cases hexy : e = (x, y)
          · exact Or.inl hexy
          · exact Or.inr (hinv e he (by simp [hexy, hnq]))
termination_by potential P dom q
decreasing_by
  · simp [potential]
  · exact potential_lt P dom x y q h

/-- **AC-3 makes every arc consistent**, for constraints given symmetrically on both
orientations of an arc and arcs between distinct variables. -/
theorem arcConsistent_ac3 [Fintype X] (hsym : Symmetric P) (hdist : ∀ e ∈ P.arcs, e.1 ≠ e.2)
    (dom : X → Finset D) : ∀ e ∈ P.arcs, ArcConsistent P (ac3All P dom).ret e :=
  arcConsistent_ac3_of_inv P hsym hdist dom P.arcs (fun _ he => he) fun _ he heq => absurd he heq

/-! ## Termination bound -/

/-- Each revision lowers the potential by at least `1`, so the revisions are at most the initial
potential. -/
theorem ac3_time_le_potential [Fintype X] (dom : X → Finset D) (q : List (X × X)) :
    (ac3 P dom q).time ≤ potential P dom q := by
  match q with
  | [] => simp [ac3.eq_1]
  | (x, y) :: q =>
      rw [ac3.eq_2]
      simp only [TimeM.time_bind, TimeM.time_tick]
      split_ifs with h
      · have := ac3_time_le_potential dom q
        simp only [potential, List.length_cons] at this ⊢
        omega
      · have := ac3_time_le_potential (Function.update dom x (revise P dom x y))
          (q ++ requeue P x y)
        have := potential_lt P dom x y q h
        omega
termination_by potential P dom q
decreasing_by
  · simp [potential]
  · exact potential_lt P dom x y q h

/-- **Termination bound**: AC-3 performs at most `|arcs| + ∑ x, |dom x| · indeg x` revisions,
`O(e d)` for `e` arcs and domains of size `d`. -/
theorem ac3_time_le [Fintype X] (dom : X → Finset D) :
    (ac3All P dom).time ≤ P.arcs.length + ∑ x, (dom x).card * indeg P x :=
  ac3_time_le_potential P dom P.arcs

end Cslib.Algorithms.Lean.ArcConsistency
