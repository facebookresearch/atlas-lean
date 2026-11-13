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

/-- **Binary constraint satisfaction problem.** A binary constraint satisfaction problem with
variables in $X$ and values in $D$ consists of a finite list of directed arcs $(x, y)$ with
$x, y \in X$, and, for all variables $x, y$ and values $a, b \in D$, a Boolean saying whether the
arc $(x, y)$ allows $x = a$ together with $y = b$. -/
structure BinaryCSP (X D : Type*) where
  /-- The directed arcs. -/
  arcs : List (X × X)
  /-- `allowed x y a b`: the arc `(x, y)` allows `x = a` together with `y = b`. -/
  allowed : X → X → D → D → Bool

variable {X D : Type*} [DecidableEq X] [DecidableEq D] (P : BinaryCSP X D)

/-- **Solution of a binary CSP within given domains.** Let $P$ be a binary constraint
satisfaction problem with variables $X$ and values $D$, and give each variable $x$ a finite
domain $\mathrm{dom}(x) \subseteq D$. An assignment $\sigma : X \to D$ is a solution of $P$ within
$\mathrm{dom}$ when $\sigma(x) \in \mathrm{dom}(x)$ for every variable $x$ and, for every arc
$(x, y)$ of $P$, the arc $(x, y)$ allows the pair $(\sigma(x), \sigma(y))$. -/
def IsSolution (dom : X → Finset D) (σ : X → D) : Prop :=
  (∀ x, σ x ∈ dom x) ∧ ∀ e ∈ P.arcs, P.allowed e.1 e.2 (σ e.1) (σ e.2) = true

/-- **Arc consistency.** Given a binary CSP $P$ and domains $\mathrm{dom}$, an arc $(x, y)$ is
consistent when for every value $a \in \mathrm{dom}(x)$ there is a value $b \in \mathrm{dom}(y)$
such that the arc $(x, y)$ allows $x = a$ together with $y = b$. -/
def ArcConsistent (dom : X → Finset D) (e : X × X) : Prop :=
  ∀ a ∈ dom e.1, ∃ b ∈ dom e.2, P.allowed e.1 e.2 a b = true

/-- **Symmetric binary CSP.** A binary constraint satisfaction problem is symmetric when, for
all variables $x, y$ and values $a, b$, the constraint on the ordered pair $(x, y)$ allows
$x = a$ together with $y = b$ exactly when the constraint on $(y, x)$ allows $y = b$ together
with $x = a$.

The condition concerns the allowed pairs for every ordered pair of variables; it does not
require the reverse of a listed arc to be listed. -/
def Symmetric : Prop := ∀ x y a b, P.allowed x y a b = P.allowed y x b a

/-- **Revision of an arc.** Let $P$ be a binary constraint satisfaction problem with values $D$,
$\mathrm{dom}$ finite domains for its variables, and $x$, $y$ variables. The revision of the arc
$(x, y)$ is the set of values $a \in \mathrm{dom}(x)$ that have a support in the domain of $y$:
some $b \in \mathrm{dom}(y)$ such that the arc $(x, y)$ allows the pair $(a, b)$. -/
def revise (dom : X → Finset D) (x y : X) : Finset D :=
  (dom x).filter fun a => ∃ b ∈ dom y, P.allowed x y a b = true

/-- **In-degree of a variable.** For a binary constraint satisfaction problem $P$ and a variable
$x$, the in-degree of $x$ is the number of arcs $(z, x)$ of $P$ ending at $x$, counted with
multiplicity in the list of arcs of $P$. -/
def indeg (x : X) : ℕ := (P.arcs.filter fun e => e.2 = x).length

/-- **Arcs requeued after a revision.** For a binary constraint satisfaction problem $P$ and
variables $x$ and $y$, the arcs requeued after revising $(x, y)$ are the arcs $(z, x)$ of $P$
with $z \neq y$, in their order in the list of arcs of $P$.

AC-3 queues these arcs when revising $(x, y)$ shrinks the domain of $x$. -/
def requeue (x y : X) : List (X × X) := P.arcs.filter fun e => e.2 = x ∧ e.1 ≠ y

/-- **Termination potential of AC-3.** Let $P$ be a binary constraint satisfaction problem with
finitely many variables, $\mathrm{dom}$ finite domains for its variables and $q$ a queue of arcs.
The potential of $\mathrm{dom}$ and $q$ is
$$|q| + \sum_{x} |\mathrm{dom}(x)| \cdot \mathrm{indeg}(x),$$
where $|q|$ is the length of the queue, the sum runs over all variables $x$, and
$\mathrm{indeg}(x)$ is the in-degree of $x$ in $P$. -/
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
/-- **A shrinking revision lowers the potential.** Let $P$ be a binary constraint satisfaction
problem with finitely many variables, $\mathrm{dom}$ finite domains for its variables, $x$ and
$y$ variables and $q$ a queue of arcs. Suppose the revision $R$ of the arc $(x, y)$ with respect
to $\mathrm{dom}$ differs from $\mathrm{dom}(x)$, and let $\mathrm{dom}'$ agree with
$\mathrm{dom}$ except that $\mathrm{dom}'(x) = R$. Then the potential of $\mathrm{dom}'$ with the
queue $q$ followed by the arcs requeued after revising $(x, y)$ is strictly less than the
potential of $\mathrm{dom}$ with the queue $(x, y)$ followed by $q$. -/
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

/-- **The AC-3 algorithm.** Given a binary CSP $P$ with finitely many variables, domains
$\mathrm{dom}$ and a queue $q$ of pairs of variables, AC-3 returns $\mathrm{dom}$ when $q$ is
empty. Otherwise it removes the first pair $(x, y)$ of $q$ and revises it: the revised domain of
$x$ consists of the values $a \in \mathrm{dom}(x)$ for which some $b \in \mathrm{dom}(y)$ has the
arc $(x, y)$ allowing $x = a$ together with $y = b$. If the revised domain equals
$\mathrm{dom}(x)$, AC-3 continues from $\mathrm{dom}$ with the rest of $q$; otherwise it replaces
the domain of $x$ by the revised domain and continues with the rest of $q$ followed by the arcs
$(z, x)$ of $P$ with $z \ne y$, in the order of the arc list of $P$. Each revision costs one unit
of time. -/
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

/-- **AC-3 on the whole problem.** For a binary CSP $P$ with finitely many variables and
domains $\mathrm{dom}$, AC-3 on the whole problem is AC-3 run from $\mathrm{dom}$ with the queue
initialized to the arc list of $P$; it returns the final domains together with the number of
revisions performed. -/
def ac3All [Fintype X] (dom : X → Finset D) : TimeM ℕ (X → Finset D) := ac3 P dom P.arcs

/-! ## Soundness -/

/-- **AC-3 only shrinks domains.** For a binary CSP $P$ with finitely many variables, domains
$\mathrm{dom}$, a queue $q$ of pairs of variables and a variable $v$, the domain of $v$ returned
by AC-3 run from $\mathrm{dom}$ with queue $q$ is a subset of $\mathrm{dom}(v)$. -/
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
/-- **Revision keeps solution values.** Let $P$ be a binary constraint satisfaction problem,
$\mathrm{dom}$ finite domains for its variables and $\sigma$ a solution of $P$ within
$\mathrm{dom}$. For every arc $(x, y)$ of $P$, the value $\sigma(x)$ lies in the revision of the
arc $(x, y)$ with respect to $\mathrm{dom}$. -/
theorem mem_revise_of_isSolution {dom : X → Finset D} {σ : X → D} (hσ : IsSolution P dom σ)
    {x y : X} (he : (x, y) ∈ P.arcs) : σ x ∈ revise P dom x y := by
  unfold revise
  rw [Finset.mem_filter]
  exact ⟨hσ.1 x, σ y, hσ.1 y, hσ.2 _ he⟩

/-- **No solution is lost.** Let $P$ be a binary constraint satisfaction problem with finitely
many variables, $\mathrm{dom}$ finite domains for its variables, and $q$ a queue of arcs each of
which is an arc of $P$. Then every solution $\sigma$ of $P$ within $\mathrm{dom}$ is also a
solution of $P$ within the domains returned by AC-3 started from $\mathrm{dom}$ with queue $q$. -/
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

/-- **Solutions survive AC-3.** Let $P$ be a binary constraint satisfaction problem with
finitely many variables and $\mathrm{dom}$ finite domains for its variables. If $\sigma$ is a
solution of $P$ within $\mathrm{dom}$, then for every variable $v$ the value $\sigma(v)$ lies in
the domain of $v$ returned by AC-3 run from $\mathrm{dom}$ with all arcs of $P$ queued. -/
theorem mem_ac3_of_isSolution [Fintype X] {dom : X → Finset D} {σ : X → D} (hσ : IsSolution P dom σ)
    (v : X) : σ v ∈ (ac3All P dom).ret v :=
  (isSolution_ac3 P dom P.arcs (fun _ he => he) σ hσ).1 v

/-- **An emptied domain rules out solutions.** Let $P$ be a binary constraint satisfaction
problem with finitely many variables and $\mathrm{dom}$ finite domains for its variables. If AC-3,
run from $\mathrm{dom}$ with all arcs of $P$ queued, returns the empty domain for some variable
$v$, then no assignment $\sigma$ is a solution of $P$ within $\mathrm{dom}$. -/
theorem not_isSolution_of_ac3_eq_empty [Fintype X] {dom : X → Finset D} {v : X}
    (hv : (ac3All P dom).ret v = ∅) (σ : X → D) : ¬IsSolution P dom σ := fun hσ => by
  have := mem_ac3_of_isSolution P hσ v
  rw [hv] at this
  exact Finset.notMem_empty _ this

/-! ## Arc consistency of the result -/

omit [DecidableEq D] in
/-- **Arc consistency after one AC-3 revision.** Let $P$ be a binary CSP whose constraints are
symmetric, that is the arc $(x, y)$ allows $(a, b)$ exactly when the arc $(y, x)$ allows $(b, a)$.
Let $\mathrm{dom}$ be domains, let $x \ne y$ be variables, let $R$ be the set of values
$a \in \mathrm{dom}(x)$ for which some $b \in \mathrm{dom}(y)$ has the arc $(x, y)$ allowing
$x = a$ together with $y = b$, and let $\mathrm{dom}'$ be $\mathrm{dom}$ with the domain of $x$
replaced by $R$. Let $e$ be an arc of $P$ with two distinct endpoints such that $e = (x, y)$ or
$e$ is consistent with respect to $\mathrm{dom}$, and such that, if $R \ne \mathrm{dom}(x)$, then
$e$ is not of the form $(z, x)$ with $z \ne y$. Then $e$ is consistent with respect to
$\mathrm{dom}'$. -/
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

/-- **Arc consistency invariant of AC-3.** Let $P$ be a binary CSP with finitely many variables
whose constraints are symmetric, that is the arc $(x, y)$ allows $(a, b)$ exactly when the arc
$(y, x)$ allows $(b, a)$, and whose arcs all join two distinct variables. Let $\mathrm{dom}$ be
domains and $q$ a queue whose entries are arcs of $P$, such that every arc of $P$ not in $q$ is
consistent with respect to $\mathrm{dom}$. Then every arc of $P$ is consistent with respect to the
domains returned by AC-3 run from $\mathrm{dom}$ with queue $q$.

The invariant: every arc of the problem outside the queue stays consistent, and at the end the
queue is empty. -/
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

/-- **AC-3 revisions are bounded by the potential.** For a binary CSP $P$ with finitely many
variables, domains $\mathrm{dom}$ and a queue $q$ of pairs of variables, the number of revisions
AC-3 performs from $\mathrm{dom}$ with queue $q$ is at most the potential
$\ell + \sum_x |\mathrm{dom}(x)| \cdot \mathrm{indeg}(x)$, where $\ell$ is the length of $q$ and
$\mathrm{indeg}(x)$ is the number of entries of the arc list of $P$ ending at $x$.

Each revision lowers the potential by at least $1$. -/
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

/-- **Bound on the number of AC-3 revisions.** For a binary CSP $P$ with finitely many variables
and initial domains $\mathrm{dom}$, AC-3 run from $\mathrm{dom}$ with every arc of $P$ queued
performs at most $m + \sum_x |\mathrm{dom}(x)| \cdot \mathrm{indeg}(x)$ revisions, where $m$ is
the length of the arc list of $P$ and $\mathrm{indeg}(x)$ is the number of entries of that list
ending at $x$.

This is $O(e d)$ for $e$ arcs and domains of size $d$. -/
theorem ac3_time_le [Fintype X] (dom : X → Finset D) :
    (ac3All P dom).time ≤ P.arcs.length + ∑ x, (dom x).card * indeg P x :=
  ac3_time_le_potential P dom P.arcs

end Cslib.Algorithms.Lean.ArcConsistency
