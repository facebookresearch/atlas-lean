/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Input/output automata: composition and finite schedules
-/
module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Set.Basic

/-!
# Input/output automata and their composition

The input/output automaton model of Lynch and Tuttle, built on CSLib's labelled transition
systems (`Cslib.LTS`). An I/O automaton has an action signature splitting its actions into
input, output and internal actions, a nonempty set of start states, and a transition relation
that is input-enabled: every input action can be taken in every state. Strongly compatible
automata (disjoint outputs, private internal actions) compose by synchronizing on shared
actions; the composition is again an I/O automaton, and its finite schedules and behaviours
are exactly related to those of the components.

## Main definitions

* `ActionSig`: an action signature, with `acts`, `ext` (external actions), `StronglyCompatible`,
  `compose`, and the projections `proj` (onto the actions) and `extProj` (onto the external
  actions) of a sequence of actions.
* `IOAutomaton α σ`: an I/O automaton with actions `α` and states `σ`.
* `IOAutomaton.Sched`, `IOAutomaton.Beh`: the finite schedules and finite behaviours.
* `IOAutomaton.compose`: the composition of two strongly compatible automata, in which each
  component makes a `MoveOrStay`.

## Main results

* `ActionSig.acts_compose`: the actions of a composition are those of its components.
* `IOAutomaton.mTr_proj_left`, `mTr_proj_right`, `mTr_of_proj`: projecting and pasting finite
  executions.
* `IOAutomaton.sched_proj_left`, `sched_proj_right`: Proposition 1 of Lynch and Tuttle for
  finite schedules: the projection of a schedule of the composition onto a component is a
  schedule of that component.
* `IOAutomaton.beh_proj_left`, `beh_proj_right`: the same for finite behaviours (traces).
* `ActionSig.proj_extProj_compose_left`, `proj_extProj_compose_right`: projecting onto a
  component commutes with keeping the external actions.
* `IOAutomaton.sched_of_proj`: Proposition 3 of Lynch and Tuttle for finite schedules: a
  sequence of actions of the composition whose projections are schedules of the components is a
  schedule of the composition.
* `IOAutomaton.beh_of_proj`: Proposition 3 for finite behaviours: a sequence of external actions
  of the composition whose projections are behaviours of the components is a behaviour of the
  composition. Together with `beh_proj_left` and `beh_proj_right` this says that the finite
  behaviours of a composition are determined by those of its components.

## Implementation notes

Only binary composition and finite schedules are treated; Lynch and Tuttle compose countable
collections and also treat infinite schedules, fair executions and the partition of locally
controlled actions into tasks, none of which is formalized here. Projection onto a component
keeps the actions of that component, as `β|A` does in the source.

## References

* N. A. Lynch, M. R. Tuttle, *An introduction to input/output automata*, CWI Quarterly 2(3),
  1989, 219–246: §3.1 (action signatures, input/output automata, executions, schedules and
  behaviours) and §3.2 (strong compatibility, composition, Propositions 1–3).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib

/-- **Action signature.** A partition of actions into input, output and internal actions
(Lynch and Tuttle, 1989, §3.1). -/
structure ActionSig (α : Type*) where
  /-- The input actions. -/
  inp : Set α
  /-- The output actions. -/
  out : Set α
  /-- The internal actions. -/
  int : Set α
  disjoint_inp_out : Disjoint inp out
  disjoint_inp_int : Disjoint inp int
  disjoint_out_int : Disjoint out int

namespace ActionSig

variable {α : Type*}

/-- **Actions of a signature.** All its input, output and internal actions. -/
def acts (S : ActionSig α) : Set α := S.inp ∪ S.out ∪ S.int

/-- **External actions of a signature.** Its input and output actions. -/
def ext (S : ActionSig α) : Set α := S.inp ∪ S.out

/-- **Strongly compatible signatures** (Lynch and Tuttle, 1989, §3.2, for two signatures):
their output actions are disjoint, and the internal actions of each are not actions of the
other. -/
structure StronglyCompatible (S₁ S₂ : ActionSig α) : Prop where
  disjoint_out : Disjoint S₁.out S₂.out
  disjoint_int_left : Disjoint S₁.int S₂.acts
  disjoint_int_right : Disjoint S₂.int S₁.acts

/-- **Composition of action signatures** (Lynch and Tuttle, 1989, §3.2). Outputs are the
outputs of either component, internal actions the internal actions of either, and inputs the
inputs of either that are output by neither. -/
def compose (S₁ S₂ : ActionSig α) (h : S₁.StronglyCompatible S₂) : ActionSig α where
  inp := (S₁.inp ∪ S₂.inp) \ (S₁.out ∪ S₂.out)
  out := S₁.out ∪ S₂.out
  int := S₁.int ∪ S₂.int
  disjoint_inp_out := Set.disjoint_sdiff_left
  disjoint_inp_int := by
    rw [Set.disjoint_left]
    rintro a ⟨hi | hi, -⟩ (ha | ha)
    · exact Set.disjoint_left.1 S₁.disjoint_inp_int hi ha
    · exact Set.disjoint_left.1 h.disjoint_int_right ha (Or.inl (Or.inl hi))
    · exact Set.disjoint_left.1 h.disjoint_int_left ha (Or.inl (Or.inl hi))
    · exact Set.disjoint_left.1 S₂.disjoint_inp_int hi ha
  disjoint_out_int := by
    rw [Set.disjoint_left]
    rintro a (ho | ho) (ha | ha)
    · exact Set.disjoint_left.1 S₁.disjoint_out_int ho ha
    · exact Set.disjoint_left.1 h.disjoint_int_right ha (Or.inl (Or.inr ho))
    · exact Set.disjoint_left.1 h.disjoint_int_left ha (Or.inl (Or.inr ho))
    · exact Set.disjoint_left.1 S₂.disjoint_out_int ho ha

/-- **Actions of a composed signature.** They are the actions of either component. -/
theorem acts_compose (S₁ S₂ : ActionSig α) (h : S₁.StronglyCompatible S₂) :
    (S₁.compose S₂ h).acts = S₁.acts ∪ S₂.acts := by
  ext a
  simp only [ActionSig.acts, ActionSig.compose, Set.mem_union, Set.mem_sdiff]
  tauto

/-- **Projection onto a signature.** The subsequence of the actions of `β` that are actions of
`S` (written `β|A` by Lynch and Tuttle). -/
noncomputable def proj (S : ActionSig α) (β : List α) : List α :=
  open Classical in β.filter (· ∈ S.acts)

/-- **External projection.** The subsequence of the actions of `β` that are external actions
of `S`. -/
noncomputable def extProj (S : ActionSig α) (β : List α) : List α :=
  open Classical in β.filter (· ∈ S.ext)

@[simp] theorem proj_nil (S : ActionSig α) : S.proj [] = [] := rfl

theorem proj_cons_of_mem (S : ActionSig α) {a : α} (β : List α) (ha : a ∈ S.acts) :
    S.proj (a :: β) = a :: S.proj β := by
  classical
  simp [proj, ha]

theorem proj_cons_of_notMem (S : ActionSig α) {a : α} (β : List α) (ha : a ∉ S.acts) :
    S.proj (a :: β) = S.proj β := by
  classical
  simp [proj, ha]

@[simp] theorem extProj_nil (S : ActionSig α) : S.extProj [] = [] := rfl

theorem extProj_cons_of_mem (S : ActionSig α) {a : α} (β : List α) (ha : a ∈ S.ext) :
    S.extProj (a :: β) = a :: S.extProj β := by
  classical
  simp [extProj, ha]

theorem extProj_cons_of_notMem (S : ActionSig α) {a : α} (β : List α) (ha : a ∉ S.ext) :
    S.extProj (a :: β) = S.extProj β := by
  classical
  simp [extProj, ha]

/-- **Non-internal actions are external.** An action of a signature that is not internal is
external. -/
theorem mem_ext_of_mem_acts {S : ActionSig α} {a : α} (ha : a ∈ S.acts) (hn : a ∉ S.int) :
    a ∈ S.ext := by
  rcases ha with h | h
  · exact h
  · exact absurd h hn

/-- **Internal actions are not external.** -/
theorem notMem_ext_of_mem_int {S : ActionSig α} {a : α} (ha : a ∈ S.int) : a ∉ S.ext := by
  rintro (h | h)
  · exact Set.disjoint_left.1 S.disjoint_inp_int h ha
  · exact Set.disjoint_left.1 S.disjoint_out_int h ha

/-- **External actions of a composition.** Each is an action of one of the components. -/
theorem mem_acts_of_mem_ext_compose {S₁ S₂ : ActionSig α} (h : S₁.StronglyCompatible S₂)
    {a : α} (ha : a ∈ (S₁.compose S₂ h).ext) : a ∈ S₁.acts ∪ S₂.acts := by
  rw [← acts_compose S₁ S₂ h]
  exact Or.inl ha

/-- **External actions of a composition in its first component.** An external action of a
composition that is an action of the first component is an external action of it, and
conversely. -/
theorem mem_ext_compose_and_acts_left {S₁ S₂ : ActionSig α} (h : S₁.StronglyCompatible S₂)
    {a : α} : a ∈ (S₁.compose S₂ h).ext ∧ a ∈ S₁.acts ↔ a ∈ S₁.ext := by
  simp only [ext, acts, compose, Set.mem_union, Set.mem_sdiff]
  constructor
  · rintro ⟨hext, (hio | hn)⟩
    · exact hio
    · exfalso
      rcases hext with ⟨hi | hi, -⟩ | ho | ho
      · exact Set.disjoint_left.1 S₁.disjoint_inp_int hi hn
      · exact Set.disjoint_left.1 h.disjoint_int_left hn (Or.inl (Or.inl hi))
      · exact Set.disjoint_left.1 S₁.disjoint_out_int ho hn
      · exact Set.disjoint_left.1 h.disjoint_int_left hn (Or.inl (Or.inr ho))
  · rintro (hi | ho)
    · refine ⟨?_, Or.inl (Or.inl hi)⟩
      by_cases hc : a ∈ S₁.out ∨ a ∈ S₂.out
      · exact Or.inr hc
      · exact Or.inl ⟨Or.inl hi, hc⟩
    · exact ⟨Or.inr (Or.inl ho), Or.inl (Or.inr ho)⟩

/-- **External actions of a composition in its second component.** An external action of a
composition that is an action of the second component is an external action of it, and
conversely. -/
theorem mem_ext_compose_and_acts_right {S₁ S₂ : ActionSig α} (h : S₁.StronglyCompatible S₂)
    {a : α} : a ∈ (S₁.compose S₂ h).ext ∧ a ∈ S₂.acts ↔ a ∈ S₂.ext := by
  simp only [ext, acts, compose, Set.mem_union, Set.mem_sdiff]
  constructor
  · rintro ⟨hext, (hio | hn)⟩
    · exact hio
    · exfalso
      rcases hext with ⟨hi | hi, -⟩ | ho | ho
      · exact Set.disjoint_left.1 h.disjoint_int_right hn (Or.inl (Or.inl hi))
      · exact Set.disjoint_left.1 S₂.disjoint_inp_int hi hn
      · exact Set.disjoint_left.1 h.disjoint_int_right hn (Or.inl (Or.inr ho))
      · exact Set.disjoint_left.1 S₂.disjoint_out_int ho hn
  · rintro (hi | ho)
    · refine ⟨?_, Or.inl (Or.inl hi)⟩
      by_cases hc : a ∈ S₁.out ∨ a ∈ S₂.out
      · exact Or.inr hc
      · exact Or.inl ⟨Or.inr hi, hc⟩
    · exact ⟨Or.inr (Or.inr ho), Or.inl (Or.inr ho)⟩

/-- **Projection onto the first component and external projection commute.** Keeping the
external actions of the composition and then the actions of the first component gives the
external actions of the first component among its actions. -/
theorem proj_extProj_compose_left {S₁ S₂ : ActionSig α} (h : S₁.StronglyCompatible S₂)
    (γ : List α) : S₁.proj ((S₁.compose S₂ h).extProj γ) = S₁.extProj (S₁.proj γ) := by
  classical
  simp only [proj, extProj, List.filter_filter]
  refine List.filter_congr fun a _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [and_comm, mem_ext_compose_and_acts_left h]
  exact ⟨fun h' => ⟨h', (Or.inl h' : a ∈ S₁.inp ∪ S₁.out ∪ S₁.int)⟩, fun h' => h'.1⟩

/-- **Projection onto the second component and external projection commute.** Keeping the
external actions of the composition and then the actions of the second component gives the
external actions of the second component among its actions. -/
theorem proj_extProj_compose_right {S₁ S₂ : ActionSig α} (h : S₁.StronglyCompatible S₂)
    (γ : List α) : S₂.proj ((S₁.compose S₂ h).extProj γ) = S₂.extProj (S₂.proj γ) := by
  classical
  simp only [proj, extProj, List.filter_filter]
  refine List.filter_congr fun a _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [and_comm, mem_ext_compose_and_acts_right h]
  exact ⟨fun h' => ⟨h', (Or.inl h' : a ∈ S₂.inp ∪ S₂.out ∪ S₂.int)⟩, fun h' => h'.1⟩

end ActionSig

/-- **Input/output automaton** (Lynch and Tuttle, 1989, §3.1). An action signature, a nonempty
set of start states and a labelled transition system whose transitions are labelled by actions
of the signature and which is input-enabled: every input action is enabled in every state. The
partition of locally controlled actions, used for fairness, is not included. -/
structure IOAutomaton (α σ : Type*) where
  /-- The action signature. -/
  sig : ActionSig α
  /-- The start states. -/
  start : Set σ
  /-- The transitions. -/
  lts : LTS σ α
  start_nonempty : start.Nonempty
  mem_acts_of_tr : ∀ s a s', lts.Tr s a s' → a ∈ sig.acts
  input_enabled : ∀ s, ∀ a ∈ sig.inp, ∃ s', lts.Tr s a s'

namespace IOAutomaton

variable {α σ σ₁ σ₂ : Type*}

/-- **Finite schedule of an I/O automaton.** The sequence of actions of a finite execution
from a start state (Lynch and Tuttle, 1989, §3.1). -/
def Sched (A : IOAutomaton α σ) (β : List α) : Prop :=
  ∃ s₀ ∈ A.start, ∃ s, A.lts.MTr s₀ β s

/-- **Finite behaviour of an I/O automaton.** The external actions of a finite schedule, in
order (Lynch and Tuttle, 1989, §3.1). -/
def Beh (A : IOAutomaton α σ) (β : List α) : Prop :=
  ∃ γ, A.Sched γ ∧ β = A.sig.extProj γ

/-- **Component move in a composition.** For an action `a`, the component `A` moves from `s` to
`t` by a transition labelled `a` if `a` is one of its actions, and stays put otherwise. -/
def MoveOrStay (A : IOAutomaton α σ) (s : σ) (a : α) (t : σ) : Prop :=
  (a ∈ A.sig.acts → A.lts.Tr s a t) ∧ (a ∉ A.sig.acts → t = s)

/-- **Composition of I/O automata** (Lynch and Tuttle, 1989, §3.2, for two automata). States
are pairs; an action of the composition moves each component having it in its signature by one
of its transitions, and leaves the other component unchanged. -/
def compose (A₁ : IOAutomaton α σ₁) (A₂ : IOAutomaton α σ₂)
    (h : A₁.sig.StronglyCompatible A₂.sig) : IOAutomaton α (σ₁ × σ₂) where
  sig := A₁.sig.compose A₂.sig h
  start := A₁.start ×ˢ A₂.start
  lts := ⟨fun s a t => a ∈ A₁.sig.acts ∪ A₂.sig.acts ∧
    A₁.MoveOrStay s.1 a t.1 ∧ A₂.MoveOrStay s.2 a t.2⟩
  start_nonempty := A₁.start_nonempty.prod A₂.start_nonempty
  mem_acts_of_tr := by
    rintro s a t ⟨ha | ha, -⟩
    · rcases ha with (hi | ho) | hn
      · by_cases hc : a ∈ A₁.sig.out ∪ A₂.sig.out
        · exact Or.inl (Or.inr hc)
        · exact Or.inl (Or.inl ⟨Or.inl hi, hc⟩)
      · exact Or.inl (Or.inr (Or.inl ho))
      · exact Or.inr (Or.inl hn)
    · rcases ha with (hi | ho) | hn
      · by_cases hc : a ∈ A₁.sig.out ∪ A₂.sig.out
        · exact Or.inl (Or.inr hc)
        · exact Or.inl (Or.inl ⟨Or.inr hi, hc⟩)
      · exact Or.inl (Or.inr (Or.inr ho))
      · exact Or.inr (Or.inr hn)
  input_enabled := by
    rintro ⟨s₁, s₂⟩ a ⟨hi, hno⟩
    -- An input of the composition that is an action of a component is an input of it.
    have key : ∀ {S : ActionSig α}, a ∈ S.acts → a ∉ S.out → a ∉ S.int → a ∈ S.inp := by
      rintro S ((h | h) | h) h' h''
      exacts [h, absurd h h', absurd h h'']
    have hni₁ : a ∉ A₁.sig.int := fun hn => by
      rcases hi with hi | hi
      · exact Set.disjoint_left.1 A₁.sig.disjoint_inp_int hi hn
      · exact Set.disjoint_left.1 h.disjoint_int_left hn (Or.inl (Or.inl hi))
    have hni₂ : a ∉ A₂.sig.int := fun hn => by
      rcases hi with hi | hi
      · exact Set.disjoint_left.1 h.disjoint_int_right hn (Or.inl (Or.inl hi))
      · exact Set.disjoint_left.1 A₂.sig.disjoint_inp_int hi hn
    have e₁ : ∃ t₁, A₁.MoveOrStay s₁ a t₁ := by
      by_cases ha : a ∈ A₁.sig.acts
      · obtain ⟨t₁, ht₁⟩ := A₁.input_enabled s₁ a (key ha (fun ho => hno (Or.inl ho)) hni₁)
        exact ⟨t₁, fun _ => ht₁, fun h' => absurd ha h'⟩
      · exact ⟨s₁, fun h' => absurd h' ha, fun _ => rfl⟩
    have e₂ : ∃ t₂, A₂.MoveOrStay s₂ a t₂ := by
      by_cases ha : a ∈ A₂.sig.acts
      · obtain ⟨t₂, ht₂⟩ := A₂.input_enabled s₂ a (key ha (fun ho => hno (Or.inr ho)) hni₂)
        exact ⟨t₂, fun _ => ht₂, fun h' => absurd ha h'⟩
      · exact ⟨s₂, fun h' => absurd h' ha, fun _ => rfl⟩
    obtain ⟨t₁, ht₁⟩ := e₁
    obtain ⟨t₂, ht₂⟩ := e₂
    refine ⟨(t₁, t₂), ?_, ht₁, ht₂⟩
    rcases hi with hi | hi
    · exact Or.inl (Or.inl (Or.inl hi))
    · exact Or.inr (Or.inl (Or.inl hi))

/-- One step of a component, or no move if the action is not its own, extends a finite
execution along the projected actions. -/
private theorem mTr_proj_cons (A : IOAutomaton α σ) {s u t : σ} {a : α} {β : List α}
    (hs : A.MoveOrStay s a u) (hu : A.lts.MTr u (A.sig.proj β) t) :
    A.lts.MTr s (A.sig.proj (a :: β)) t := by
  by_cases ha : a ∈ A.sig.acts
  · rw [A.sig.proj_cons_of_mem β ha]
    exact LTS.MTr.stepL (hs.1 ha) hu
  · obtain rfl := hs.2 ha
    rwa [A.sig.proj_cons_of_notMem β ha]

/-- Conversely, a finite execution along the projection of `a :: β` starts with a step of the
component for `a` if `a` is its own, and with no move otherwise. -/
private theorem exists_of_mTr_proj_cons (A : IOAutomaton α σ) {s t : σ} {a : α}
    {β : List α} (h : A.lts.MTr s (A.sig.proj (a :: β)) t) :
    ∃ u, A.MoveOrStay s a u ∧ A.lts.MTr u (A.sig.proj β) t := by
  by_cases ha : a ∈ A.sig.acts
  · rw [A.sig.proj_cons_of_mem β ha] at h
    obtain ⟨u, hu, hu'⟩ := LTS.MTr.cons_iff.1 h
    exact ⟨u, ⟨fun _ => hu, fun h' => absurd ha h'⟩, hu'⟩
  · rw [A.sig.proj_cons_of_notMem β ha] at h
    exact ⟨s, ⟨fun h' => absurd h' ha, fun _ => rfl⟩, h⟩

variable (A₁ : IOAutomaton α σ₁) (A₂ : IOAutomaton α σ₂) (h : A₁.sig.StronglyCompatible A₂.sig)

/-- **Projection of an execution of a composition onto its first component.** A finite execution
of the composition projects to a finite execution of the first component, along the actions of
that component. -/
theorem mTr_proj_left {s t : σ₁ × σ₂} {β : List α} (hβ : (A₁.compose A₂ h).lts.MTr s β t) :
    A₁.lts.MTr s.1 (A₁.sig.proj β) t.1 := by
  induction hβ with
  | refl => exact .refl
  | stepL htr _ ih => exact mTr_proj_cons A₁ htr.2.1 ih

/-- **Projection of an execution of a composition onto its second component.** A finite
execution of the composition projects to a finite execution of the second component, along the
actions of that component. -/
theorem mTr_proj_right {s t : σ₁ × σ₂} {β : List α} (hβ : (A₁.compose A₂ h).lts.MTr s β t) :
    A₂.lts.MTr s.2 (A₂.sig.proj β) t.2 := by
  induction hβ with
  | refl => exact .refl
  | stepL htr _ ih => exact mTr_proj_cons A₂ htr.2.2 ih

/-- **Pasting executions of the components of a composition.** If every action of `β` is an
action of a component and the projections of `β` label finite executions of the components from
`s.1` to `t₁` and from `s.2` to `t₂`, then `β` labels a finite execution of the composition from
`s` to `(t₁, t₂)`. -/
theorem mTr_of_proj {s : σ₁ × σ₂} {t₁ : σ₁} {t₂ : σ₂} {β : List α}
    (hβ : ∀ a ∈ β, a ∈ A₁.sig.acts ∪ A₂.sig.acts)
    (h₁ : A₁.lts.MTr s.1 (A₁.sig.proj β) t₁)
    (h₂ : A₂.lts.MTr s.2 (A₂.sig.proj β) t₂) :
    (A₁.compose A₂ h).lts.MTr s β (t₁, t₂) := by
  induction β generalizing s with
  | nil =>
      obtain ⟨s₁, s₂⟩ := s
      obtain rfl := LTS.MTr.nil_eq _ h₁
      obtain rfl := LTS.MTr.nil_eq _ h₂
      exact .refl
  | cons a β ih =>
      obtain ⟨u₁, hu₁, hu₁'⟩ := exists_of_mTr_proj_cons A₁ h₁
      obtain ⟨u₂, hu₂, hu₂'⟩ := exists_of_mTr_proj_cons A₂ h₂
      exact .stepL (s2 := (u₁, u₂)) ⟨hβ a (List.mem_cons_self ..), hu₁, hu₂⟩
        (ih (fun b hb => hβ b (List.mem_cons_of_mem _ hb)) hu₁' hu₂')

/-- **Projection of a schedule of a composition onto its first component** (Lynch and Tuttle,
1989, Proposition 1, for finite schedules). -/
theorem sched_proj_left {β : List α} (hβ : (A₁.compose A₂ h).Sched β) :
    A₁.Sched (A₁.sig.proj β) := by
  obtain ⟨s₀, hs₀, t, ht⟩ := hβ
  exact ⟨s₀.1, hs₀.1, t.1, A₁.mTr_proj_left A₂ h ht⟩

/-- **Projection of a schedule of a composition onto its second component** (Lynch and Tuttle,
1989, Proposition 1, for finite schedules). -/
theorem sched_proj_right {β : List α} (hβ : (A₁.compose A₂ h).Sched β) :
    A₂.Sched (A₂.sig.proj β) := by
  obtain ⟨s₀, hs₀, t, ht⟩ := hβ
  exact ⟨s₀.2, hs₀.2, t.2, A₁.mTr_proj_right A₂ h ht⟩

/-- **Pasting schedules of the components of a composition** (Lynch and Tuttle, 1989,
Proposition 3, for finite schedules). A finite sequence `β` of actions of the composition whose
projections onto the two components are schedules of the components is a schedule of the
composition. -/
theorem sched_of_proj {β : List α} (hβ : ∀ a ∈ β, a ∈ (A₁.compose A₂ h).sig.acts)
    (h₁ : A₁.Sched (A₁.sig.proj β)) (h₂ : A₂.Sched (A₂.sig.proj β)) :
    (A₁.compose A₂ h).Sched β := by
  obtain ⟨s₁, hs₁, t₁, ht₁⟩ := h₁
  obtain ⟨s₂, hs₂, t₂, ht₂⟩ := h₂
  have hβ' : ∀ a ∈ β, a ∈ A₁.sig.acts ∪ A₂.sig.acts := fun a ha => by
    have := hβ a ha
    rwa [compose, ActionSig.acts_compose] at this
  exact ⟨(s₁, s₂), ⟨hs₁, hs₂⟩, (t₁, t₂), A₁.mTr_of_proj A₂ h (s := (s₁, s₂)) hβ' ht₁ ht₂⟩

/-- **Projection of a behaviour of a composition onto its first component** (Lynch and Tuttle,
1989, Proposition 1, for finite behaviours). -/
theorem beh_proj_left {β : List α} (hβ : (A₁.compose A₂ h).Beh β) :
    A₁.Beh (A₁.sig.proj β) := by
  obtain ⟨γ, hγ, rfl⟩ := hβ
  exact ⟨_, A₁.sched_proj_left A₂ h hγ, ActionSig.proj_extProj_compose_left h γ⟩

/-- **Projection of a behaviour of a composition onto its second component** (Lynch and Tuttle,
1989, Proposition 1, for finite behaviours). -/
theorem beh_proj_right {β : List α} (hβ : (A₁.compose A₂ h).Beh β) :
    A₂.Beh (A₂.sig.proj β) := by
  obtain ⟨γ, hγ, rfl⟩ := hβ
  exact ⟨_, A₁.sched_proj_right A₂ h hγ, ActionSig.proj_extProj_compose_right h γ⟩

/-- Pasting finite executions whose external projections match a common sequence `β`, by
induction on the total length. -/
private theorem exists_mTr_of_extProj (n : ℕ) :
    ∀ (β γ₁ γ₂ : List α) (s₁ t₁ : σ₁) (s₂ t₂ : σ₂),
      β.length + γ₁.length + γ₂.length = n →
      (∀ a ∈ β, a ∈ (A₁.compose A₂ h).sig.ext) →
      A₁.lts.MTr s₁ γ₁ t₁ → A₂.lts.MTr s₂ γ₂ t₂ →
      A₁.sig.proj β = A₁.sig.extProj γ₁ → A₂.sig.proj β = A₂.sig.extProj γ₂ →
      ∃ γ, (A₁.compose A₂ h).lts.MTr (s₁, s₂) γ (t₁, t₂) ∧
        (A₁.compose A₂ h).sig.extProj γ = β := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro β γ₁ γ₂ s₁ t₁ s₂ t₂ hn hβ h₁ h₂ e₁ e₂
  set A := A₁.compose A₂ h
  -- A leading internal action of the first component is taken alone.
  by_cases hi₁ : ∃ x γ₁', γ₁ = x :: γ₁' ∧ x ∈ A₁.sig.int
  · obtain ⟨x, γ₁', rfl, hx⟩ := hi₁
    obtain ⟨u₁, hu₁, h₁'⟩ := LTS.MTr.cons_iff.1 h₁
    have hx₂ : x ∉ A₂.sig.acts := Set.disjoint_left.1 h.disjoint_int_left hx
    have hxA : x ∉ A.sig.ext := ActionSig.notMem_ext_of_mem_int (S := A.sig) (Or.inl hx)
    obtain ⟨γ, hγ, hγe⟩ := ih (β.length + γ₁'.length + γ₂.length) (by simp at hn; omega) β γ₁'
      γ₂ u₁ t₁ s₂ t₂ rfl hβ h₁' h₂
      (by rw [e₁, ActionSig.extProj_cons_of_notMem _ _ (ActionSig.notMem_ext_of_mem_int hx)])
      e₂
    refine ⟨x :: γ, .stepL (s2 := (u₁, s₂)) ⟨Or.inl (Or.inr hx), ⟨fun _ => hu₁, fun h' =>
      absurd (Or.inr hx) h'⟩, ⟨fun h' => absurd h' hx₂, fun _ => rfl⟩⟩ hγ, ?_⟩
    rw [ActionSig.extProj_cons_of_notMem _ _ hxA, hγe]
  -- So is a leading internal action of the second component.
  by_cases hi₂ : ∃ x γ₂', γ₂ = x :: γ₂' ∧ x ∈ A₂.sig.int
  · obtain ⟨x, γ₂', rfl, hx⟩ := hi₂
    obtain ⟨u₂, hu₂, h₂'⟩ := LTS.MTr.cons_iff.1 h₂
    have hx₁ : x ∉ A₁.sig.acts := Set.disjoint_left.1 h.disjoint_int_right hx
    have hxA : x ∉ A.sig.ext := ActionSig.notMem_ext_of_mem_int (S := A.sig) (Or.inr hx)
    obtain ⟨γ, hγ, hγe⟩ := ih (β.length + γ₁.length + γ₂'.length) (by simp at hn; omega) β γ₁
      γ₂' s₁ t₁ u₂ t₂ rfl hβ h₁ h₂' e₁
      (by rw [e₂, ActionSig.extProj_cons_of_notMem _ _ (ActionSig.notMem_ext_of_mem_int hx)])
    refine ⟨x :: γ, .stepL (s2 := (s₁, u₂)) ⟨Or.inr (Or.inr hx), ⟨fun h' => absurd h' hx₁,
      fun _ => rfl⟩, ⟨fun _ => hu₂, fun h' => absurd (Or.inr hx) h'⟩⟩ hγ, ?_⟩
    rw [ActionSig.extProj_cons_of_notMem _ _ hxA, hγe]
  push Not at hi₁ hi₂
  -- Otherwise every leading action is external, and is the next action of `β`.
  have lead₁ : ∀ y γ', γ₁ = y :: γ' → A₁.sig.extProj γ₁ = y :: A₁.sig.extProj γ' := by
    rintro y γ' rfl
    obtain ⟨u, hu, -⟩ := LTS.MTr.cons_iff.1 h₁
    exact ActionSig.extProj_cons_of_mem _ _
      (ActionSig.mem_ext_of_mem_acts (A₁.mem_acts_of_tr _ _ _ hu) (hi₁ y γ' rfl))
  have lead₂ : ∀ y γ', γ₂ = y :: γ' → A₂.sig.extProj γ₂ = y :: A₂.sig.extProj γ' := by
    rintro y γ' rfl
    obtain ⟨u, hu, -⟩ := LTS.MTr.cons_iff.1 h₂
    exact ActionSig.extProj_cons_of_mem _ _
      (ActionSig.mem_ext_of_mem_acts (A₂.mem_acts_of_tr _ _ _ hu) (hi₂ y γ' rfl))
  cases β with
  | nil =>
      -- Both executions are empty.
      have g₁ : γ₁ = [] := by
        cases γ₁ with
        | nil => rfl
        | cons y γ' => simp [lead₁ y γ' rfl, ActionSig.proj_nil] at e₁
      have g₂ : γ₂ = [] := by
        cases γ₂ with
        | nil => rfl
        | cons y γ' => simp [lead₂ y γ' rfl, ActionSig.proj_nil] at e₂
      subst g₁ g₂
      obtain rfl := LTS.MTr.nil_eq _ h₁
      obtain rfl := LTS.MTr.nil_eq _ h₂
      exact ⟨[], .refl, rfl⟩
  | cons a β =>
      have ha := hβ a (List.mem_cons_self ..)
      have hβ' : ∀ b ∈ β, b ∈ A.sig.ext := fun b hb => hβ b (List.mem_cons_of_mem _ hb)
      -- Each component that has `a` takes it first; the other stays put.
      have step₁ : ∃ u₁ γ₁', A₁.MoveOrStay s₁ a u₁ ∧ A₁.lts.MTr u₁ γ₁' t₁ ∧
          A₁.sig.proj β = A₁.sig.extProj γ₁' ∧ γ₁'.length ≤ γ₁.length := by
        by_cases ha₁ : a ∈ A₁.sig.acts
        · rw [ActionSig.proj_cons_of_mem _ _ ha₁] at e₁
          cases γ₁ with
          | nil => simp at e₁
          | cons y γ' =>
              rw [lead₁ y γ' rfl] at e₁
              obtain ⟨rfl, e⟩ := List.cons.inj e₁
              obtain ⟨u, hu, hu'⟩ := LTS.MTr.cons_iff.1 h₁
              exact ⟨u, γ', ⟨fun _ => hu, fun h' => absurd ha₁ h'⟩, hu', e, by simp⟩
        · rw [ActionSig.proj_cons_of_notMem _ _ ha₁] at e₁
          exact ⟨s₁, γ₁, ⟨fun h' => absurd h' ha₁, fun _ => rfl⟩, h₁, e₁, le_rfl⟩
      have step₂ : ∃ u₂ γ₂', A₂.MoveOrStay s₂ a u₂ ∧ A₂.lts.MTr u₂ γ₂' t₂ ∧
          A₂.sig.proj β = A₂.sig.extProj γ₂' ∧ γ₂'.length ≤ γ₂.length := by
        by_cases ha₂ : a ∈ A₂.sig.acts
        · rw [ActionSig.proj_cons_of_mem _ _ ha₂] at e₂
          cases γ₂ with
          | nil => simp at e₂
          | cons y γ' =>
              rw [lead₂ y γ' rfl] at e₂
              obtain ⟨rfl, e⟩ := List.cons.inj e₂
              obtain ⟨u, hu, hu'⟩ := LTS.MTr.cons_iff.1 h₂
              exact ⟨u, γ', ⟨fun _ => hu, fun h' => absurd ha₂ h'⟩, hu', e, by simp⟩
        · rw [ActionSig.proj_cons_of_notMem _ _ ha₂] at e₂
          exact ⟨s₂, γ₂, ⟨fun h' => absurd h' ha₂, fun _ => rfl⟩, h₂, e₂, le_rfl⟩
      obtain ⟨u₁, γ₁', hu₁, h₁', e₁', l₁⟩ := step₁
      obtain ⟨u₂, γ₂', hu₂, h₂', e₂', l₂⟩ := step₂
      obtain ⟨γ, hγ, hγe⟩ := ih (β.length + γ₁'.length + γ₂'.length)
        (by simp only [List.length_cons] at hn; omega) β γ₁' γ₂' u₁ t₁ u₂
        t₂ rfl hβ' h₁' h₂' e₁' e₂'
      refine ⟨a :: γ, .stepL (s2 := (u₁, u₂))
        ⟨ActionSig.mem_acts_of_mem_ext_compose h ha, hu₁, hu₂⟩ hγ, ?_⟩
      rw [ActionSig.extProj_cons_of_mem _ _ ha, hγe]

/-- **Pasting behaviours of the components of a composition** (Lynch and Tuttle, 1989,
Proposition 3 with schedules replaced by behaviours, for finite behaviours). A finite sequence
`β` of external actions of the composition whose projections onto the two components are
behaviours of the components is a behaviour of the composition. -/
theorem beh_of_proj {β : List α} (hβ : ∀ a ∈ β, a ∈ (A₁.compose A₂ h).sig.ext)
    (h₁ : A₁.Beh (A₁.sig.proj β)) (h₂ : A₂.Beh (A₂.sig.proj β)) :
    (A₁.compose A₂ h).Beh β := by
  obtain ⟨γ₁, ⟨s₁, hs₁, t₁, ht₁⟩, e₁⟩ := h₁
  obtain ⟨γ₂, ⟨s₂, hs₂, t₂, ht₂⟩, e₂⟩ := h₂
  obtain ⟨γ, hγ, hγe⟩ := exists_mTr_of_extProj A₁ A₂ h _ β γ₁ γ₂ s₁ t₁ s₂ t₂ rfl hβ ht₁ ht₂ e₁ e₂
  exact ⟨γ, ⟨(s₁, s₂), ⟨hs₁, hs₂⟩, (t₁, t₂), hγ⟩, hγe.symm⟩

end IOAutomaton

end Cslib
