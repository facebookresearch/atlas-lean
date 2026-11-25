/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.SessionTypes.Multiparty.Typing

/-!
# Multiparty session types: finite synchronous subject reduction and session fidelity

Finite, synchronous, single-session, participant-addressed specialization
of subject reduction and session fidelity from Honda, Yoshida and Carbone,
*Multiparty Asynchronous Session Types*, JACM 63(1), 2016, for networks
typed by the projections of a well-formed global type
(`Multiparty.Typing`).

* Subject reduction (Theorem 5.19 (2)): `Net.TypedBy.step_of_global`. If a
  typed network takes a synchronous step with label `ℓ` to `net'`, then
  `net'` is typed by every global type that the original global type
  reaches by a step with the same label. Every network step is a session interaction, so the
  source's case where the session environment does not move cannot arise.
* Session fidelity (Corollary 5.23 (1)): `Net.TypedBy.step` gives, for every
  network step, a global step with the same label whose target types the
  stepped network, so typing contexts evolve by steps of the global LTS.
  `Net.lts` is the synchronous network LTS and `Net.TypedBy.mtr` lifts
  fidelity to finite traces.
* Projection completeness at a matched pair (the if-direction of
  Lemma 5.11): `GlobalType.step_of_project_send_recv` and
  `GlobalType.step_of_project_select_branch`. When the projections onto
  `p` and `q` show a matching send and receive, or a selection offering a
  label and a matching branch, the global type has the corresponding step.
  No well-formedness premise is needed. The receiver's projection is
  required: the sender's projection alone does not suffice.

This is a project specialization, not a verbatim source statement. Fidelity
is stated from network steps to global steps only. Not claimed: the
converse of fidelity (a global step realised by the network; it is false
label-wise here, because a selection is the process's choice), progress
(Corollary 5.30) and every progress result, subject congruence
(Theorem 5.19 (1); networks have no structural congruence), Theorem 5.19 (3)
and session initiation, Corollary 5.23 (2) (there are no queues),
determinacy (Lemma 5.12), communication safety (Theorem 5.22), recursive
global types, asynchrony, delegation and subtyping, and the general
Lemma 5.11 equivalence beyond a matched sender and receiver.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.SessionTypes

/-- Every branch of a projectable list projects to a member of the list. -/
private theorem GlobalType.Branches.projectList_mem {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {peer : P} :
    ∀ {bs : GlobalType.Branches P S L} {ts : List (LocalType P S L)},
      bs.projectList peer = some ts → ∀ {l : L} {G : GlobalType P S L},
        (l, G) ∈ bs.entries → ∃ t, G.project peer = some t ∧ t ∈ ts
  | .nil, _, _, _, _, hm => by simp [GlobalType.Branches.entries] at hm
  | .cons label head tail, ts, hts, l, G, hm => by
    rw [GlobalType.Branches.projectList] at hts
    cases hh : head.project peer with
    | none => simp [hh] at hts
    | some head' =>
      cases htl : tail.projectList peer with
      | none => simp [hh, htl] at hts
      | some tail' =>
        simp only [hh, htl, Option.some.injEq] at hts
        subst hts
        simp only [GlobalType.Branches.entries, List.mem_cons, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | hm
        · exact ⟨head', hh, List.mem_cons_self⟩
        · obtain ⟨t, ht, htm⟩ := GlobalType.Branches.projectList_mem htl hm
          exact ⟨t, ht, List.mem_cons_of_mem _ htm⟩

/-- A third-party projection of a choice comes from a nonempty branch list,
and every branch projects brace-equal to it. -/
private theorem GlobalType.Branches.projectThirdParty_mem {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {peer : P} {T : LocalType P S L} :
    ∀ {bs : GlobalType.Branches P S L}, bs.projectThirdParty peer = some T →
      bs ≠ .nil ∧ ∀ {l : L} {G : GlobalType P S L}, (l, G) ∈ bs.entries →
        ∃ t, G.project peer = some t ∧ t.braceEq T = true
  | .nil, h => by simp [GlobalType.Branches.projectThirdParty] at h
  | .cons label head tail, h => by
    refine ⟨by simp, ?_⟩
    rw [GlobalType.Branches.projectThirdParty] at h
    cases hh : head.project peer with
    | none => simp [hh] at h
    | some head' =>
      cases htl : tail.projectList peer with
      | none => simp [hh, htl] at h
      | some rest =>
        simp only [hh, htl] at h
        by_cases hall : (head' :: rest).all
            (fun t => (head' :: rest).all (LocalType.braceEq t)) = true
        · rw [ite_eq_left hall, Option.some.injEq] at h
          subst h
          have key : ∀ t ∈ head' :: rest, t.braceEq head' = true := fun t ht =>
            List.all_eq_true.mp (List.all_eq_true.mp hall t ht) head' List.mem_cons_self
          intro hm
          simp only [GlobalType.Branches.entries, List.mem_cons, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | hm
          · exact ⟨head', hh, key head' List.mem_cons_self⟩
          · obtain ⟨t, ht, htm⟩ := GlobalType.Branches.projectList_mem htl hm
            exact ⟨t, ht, key t (List.mem_cons_of_mem _ htm)⟩
        · rw [ite_eq_right hall] at h
          cases h

/-- Projecting the branches of a choice for a principal keeps the labels. -/
private theorem GlobalType.Branches.projectBranches_labels {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {peer : P} :
    ∀ {bs : GlobalType.Branches P S L} {lbs : LocalType.Branches P S L},
      bs.projectBranches peer = some lbs → lbs.labels = bs.labels
  | .nil, lbs, h => by
    rw [GlobalType.Branches.projectBranches, Option.some.injEq] at h
    subst h
    rfl
  | .cons label head tail, lbs, h => by
    rw [GlobalType.Branches.projectBranches] at h
    cases hh : head.project peer with
    | none => simp [hh] at h
    | some head' =>
      cases htl : tail.projectBranches peer with
      | none => simp [hh, htl] at h
      | some tail' =>
        simp only [hh, htl, Option.some.injEq] at h
        subst h
        have ih := GlobalType.Branches.projectBranches_labels htl
        simp only [LocalType.Branches.labels, GlobalType.Branches.labels,
          LocalType.Branches.entries, GlobalType.Branches.entries, List.map_cons] at ih ⊢
        rw [ih]

/-- A label with a lookup result is a label of the list. -/
private theorem LocalType.Branches.mem_labels_of_lookup {P S L : Type} [DecidableEq L]
    {label : L} {t : LocalType P S L} :
    ∀ {bs : LocalType.Branches P S L}, bs.lookup label = some t → label ∈ bs.labels
  | .nil, h => by simp [LocalType.Branches.lookup] at h
  | .cons entryLabel head tail, h => by
    by_cases hl : label = entryLabel
    · subst hl
      simp [LocalType.Branches.labels, LocalType.Branches.entries]
    · rw [LocalType.Branches.lookup, ite_eq_right hl] at h
      have ih := LocalType.Branches.mem_labels_of_lookup h
      simp only [LocalType.Branches.labels, LocalType.Branches.entries, List.map_cons,
        List.mem_cons] at ih ⊢
      exact Or.inr ih

/-- A type brace-equal to a send is a send to the same peer of the same sort. -/
private theorem LocalType.braceEq_send_shape {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {t u : LocalType P S L} {q : P} {s : S} :
    t.braceEq (.send q s u) = true → ∃ t', t = .send q s t' := by
  intro h
  cases t <;> simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq,
    Bool.false_eq_true] at h
  obtain ⟨⟨rfl, rfl⟩, -⟩ := h
  exact ⟨_, rfl⟩

/-- A type brace-equal to a receive is a receive from the same peer. -/
private theorem LocalType.braceEq_recv_shape {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {t u : LocalType P S L} {p : P} {s : S} :
    t.braceEq (.recv p s u) = true → ∃ t', t = .recv p s t' := by
  intro h
  cases t <;> simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq,
    Bool.false_eq_true] at h
  obtain ⟨⟨rfl, rfl⟩, -⟩ := h
  exact ⟨_, rfl⟩

/-- A type brace-equal to a selection is a selection towards the same peer
with brace-equal branches. -/
private theorem LocalType.braceEq_select_shape {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {t : LocalType P S L} {q : P}
    {lbs : LocalType.Branches P S L} :
    t.braceEq (.select q lbs) = true →
      ∃ lbs', t = .select q lbs' ∧ lbs'.braceEq lbs = true := by
  intro h
  cases t <;> simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq,
    Bool.false_eq_true] at h
  obtain ⟨rfl, h⟩ := h
  exact ⟨_, rfl, h⟩

/-- A type brace-equal to a branch is a branch on the same peer. -/
private theorem LocalType.braceEq_branch_shape {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {t : LocalType P S L} {p : P}
    {lbs : LocalType.Branches P S L} :
    t.braceEq (.branch p lbs) = true → ∃ lbs', t = .branch p lbs' := by
  intro h
  cases t <;> simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq,
    Bool.false_eq_true] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨_, rfl⟩

mutual

/-- Completeness for a message, by structural recursion on the global type. -/
private theorem GlobalType.step_of_project_send_recv_core {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {p q : P} {s : S} :
    ∀ {G : GlobalType P S L} {t : LocalType P S L} {s' : S} {u : LocalType P S L},
      G.project p = some (.send q s t) → G.project q = some (.recv p s' u) →
        ∃ G', G.Step (.msg p q s) G'
  | .end, _, _, _, hp, _ => by
    rw [GlobalType.project] at hp
    cases hp
  | .msg r r' pl next, t, s', u, hp, hq => by
    rw [GlobalType.project] at hp hq
    by_cases hpr : p = r
    · rw [ite_eq_left hpr] at hp
      by_cases hrr : r = r'
      · rw [ite_eq_left hrr] at hp
        cases hp
      · rw [ite_eq_right hrr, Option.map_eq_some_iff] at hp
        obtain ⟨_, -, h⟩ := hp
        cases h
        subst hpr
        exact ⟨next, .msg⟩
    rw [ite_eq_right hpr] at hp
    by_cases hpr' : p = r'
    · rw [ite_eq_left hpr', Option.map_eq_some_iff] at hp
      obtain ⟨_, -, h⟩ := hp
      cases h
    rw [ite_eq_right hpr'] at hp
    by_cases hqr : q = r
    · rw [ite_eq_left hqr] at hq
      by_cases hrr : r = r'
      · rw [ite_eq_left hrr] at hq
        cases hq
      · rw [ite_eq_right hrr, Option.map_eq_some_iff] at hq
        obtain ⟨_, -, h⟩ := hq
        cases h
    rw [ite_eq_right hqr] at hq
    by_cases hqr' : q = r'
    · rw [ite_eq_left hqr', Option.map_eq_some_iff] at hq
      obtain ⟨_, -, h⟩ := hq
      simp only [LocalType.recv.injEq] at h
      exact absurd h.1.symm hpr
    rw [ite_eq_right hqr'] at hq
    obtain ⟨next', h⟩ := GlobalType.step_of_project_send_recv_core hp hq
    exact ⟨_, .msgCongr h (Ne.symm hpr) (Ne.symm hqr) (Ne.symm hpr') (Ne.symm hqr')⟩
  | .choice r r' bs, t, s', u, hp, hq => by
    rw [GlobalType.project] at hp hq
    by_cases hpr : p = r
    · rw [ite_eq_left hpr] at hp
      by_cases hrr : r = r'
      · rw [ite_eq_left hrr] at hp
        cases hp
      · rw [ite_eq_right hrr, Option.map_eq_some_iff] at hp
        obtain ⟨_, -, h⟩ := hp
        cases h
    rw [ite_eq_right hpr] at hp
    by_cases hpr' : p = r'
    · rw [ite_eq_left hpr', Option.map_eq_some_iff] at hp
      obtain ⟨_, -, h⟩ := hp
      cases h
    rw [ite_eq_right hpr'] at hp
    by_cases hqr : q = r
    · rw [ite_eq_left hqr] at hq
      by_cases hrr : r = r'
      · rw [ite_eq_left hrr] at hq
        cases hq
      · rw [ite_eq_right hrr, Option.map_eq_some_iff] at hq
        obtain ⟨_, -, h⟩ := hq
        cases h
    rw [ite_eq_right hqr] at hq
    by_cases hqr' : q = r'
    · rw [ite_eq_left hqr', Option.map_eq_some_iff] at hq
      obtain ⟨_, -, h⟩ := hq
      cases h
    rw [ite_eq_right hqr'] at hq
    obtain ⟨hne, hpm⟩ := GlobalType.Branches.projectThirdParty_mem hp
    obtain ⟨-, hqm⟩ := GlobalType.Branches.projectThirdParty_mem hq
    obtain ⟨bs', hbs⟩ := GlobalType.Branches.step_of_project_send_recv bs fun hm => by
      obtain ⟨tp, htp, hbp⟩ := hpm hm
      obtain ⟨tq, htq, hbq⟩ := hqm hm
      obtain ⟨tp', rfl⟩ := LocalType.braceEq_send_shape hbp
      obtain ⟨tq', rfl⟩ := LocalType.braceEq_recv_shape hbq
      exact ⟨⟨tp', htp⟩, s', tq', htq⟩
    exact ⟨_, .choiceCongr hbs hne (Ne.symm hpr) (Ne.symm hqr) (Ne.symm hpr')
      (Ne.symm hqr')⟩

/-- Completeness for a message, every branch at once. -/
private theorem GlobalType.Branches.step_of_project_send_recv {P S L : Type}
    [DecidableEq P] [DecidableEq S] [DecidableEq L] {p q : P} {s : S} :
    ∀ (bs : GlobalType.Branches P S L),
      (∀ {l : L} {G : GlobalType P S L}, (l, G) ∈ bs.entries →
        (∃ t, G.project p = some (.send q s t)) ∧ ∃ s' u, G.project q = some (.recv p s' u)) →
      ∃ bs', GlobalType.Branches.Step bs (.msg p q s) bs'
  | .nil, _ => ⟨.nil, .nil⟩
  | .cons label head tail, H => by
    obtain ⟨⟨t, ht⟩, s', u, hu⟩ := H (l := label) (G := head)
      List.mem_cons_self
    obtain ⟨head', hh⟩ := GlobalType.step_of_project_send_recv_core ht hu
    obtain ⟨tail', htl⟩ := GlobalType.Branches.step_of_project_send_recv tail fun hm =>
      H (List.mem_cons_of_mem _ hm)
    exact ⟨.cons label head' tail', .cons hh htl⟩

end

mutual

/-- Completeness for a choice, by structural recursion on the global type. -/
private theorem GlobalType.step_of_project_select_branch_core {P S L : Type}
    [DecidableEq P] [DecidableEq S] [DecidableEq L] {p q : P} {label : L} :
    ∀ {G : GlobalType P S L} {lbs lbs' : LocalType.Branches P S L},
      G.project p = some (.select q lbs) → label ∈ lbs.labels →
        G.project q = some (.branch p lbs') → ∃ G', G.Step (.choice p q label) G'
  | .end, _, _, hp, _, _ => by
    rw [GlobalType.project] at hp
    cases hp
  | .msg r r' pl next, lbs, lbs', hp, hl, hq => by
    rw [GlobalType.project] at hp hq
    by_cases hpr : p = r
    · rw [ite_eq_left hpr] at hp
      by_cases hrr : r = r'
      · rw [ite_eq_left hrr] at hp
        cases hp
      · rw [ite_eq_right hrr, Option.map_eq_some_iff] at hp
        obtain ⟨_, -, h⟩ := hp
        cases h
    rw [ite_eq_right hpr] at hp
    by_cases hpr' : p = r'
    · rw [ite_eq_left hpr', Option.map_eq_some_iff] at hp
      obtain ⟨_, -, h⟩ := hp
      cases h
    rw [ite_eq_right hpr'] at hp
    by_cases hqr : q = r
    · rw [ite_eq_left hqr] at hq
      by_cases hrr : r = r'
      · rw [ite_eq_left hrr] at hq
        cases hq
      · rw [ite_eq_right hrr, Option.map_eq_some_iff] at hq
        obtain ⟨_, -, h⟩ := hq
        cases h
    rw [ite_eq_right hqr] at hq
    by_cases hqr' : q = r'
    · rw [ite_eq_left hqr', Option.map_eq_some_iff] at hq
      obtain ⟨_, -, h⟩ := hq
      cases h
    rw [ite_eq_right hqr'] at hq
    obtain ⟨next', h⟩ := GlobalType.step_of_project_select_branch_core hp hl hq
    exact ⟨_, .msgCongr h (Ne.symm hpr) (Ne.symm hqr) (Ne.symm hpr') (Ne.symm hqr')⟩
  | .choice r r' bs, lbs, lbs', hp, hl, hq => by
    rw [GlobalType.project] at hp hq
    by_cases hpr : p = r
    · rw [ite_eq_left hpr] at hp
      by_cases hrr : r = r'
      · rw [ite_eq_left hrr] at hp
        cases hp
      · rw [ite_eq_right hrr, Option.map_eq_some_iff] at hp
        obtain ⟨_, hpb, h⟩ := hp
        cases h
        rw [GlobalType.Branches.projectBranches_labels hpb] at hl
        obtain ⟨⟨l, next⟩, hmem, hfst⟩ := List.mem_map.mp hl
        subst hpr
        subst hfst
        exact ⟨next, .choice hmem⟩
    rw [ite_eq_right hpr] at hp
    by_cases hpr' : p = r'
    · rw [ite_eq_left hpr', Option.map_eq_some_iff] at hp
      obtain ⟨_, -, h⟩ := hp
      cases h
    rw [ite_eq_right hpr'] at hp
    by_cases hqr : q = r
    · rw [ite_eq_left hqr] at hq
      by_cases hrr : r = r'
      · rw [ite_eq_left hrr] at hq
        cases hq
      · rw [ite_eq_right hrr, Option.map_eq_some_iff] at hq
        obtain ⟨_, -, h⟩ := hq
        cases h
    rw [ite_eq_right hqr] at hq
    by_cases hqr' : q = r'
    · rw [ite_eq_left hqr', Option.map_eq_some_iff] at hq
      obtain ⟨_, -, h⟩ := hq
      simp only [LocalType.branch.injEq] at h
      exact absurd h.1.symm hpr
    rw [ite_eq_right hqr'] at hq
    obtain ⟨hne, hpm⟩ := GlobalType.Branches.projectThirdParty_mem hp
    obtain ⟨-, hqm⟩ := GlobalType.Branches.projectThirdParty_mem hq
    obtain ⟨bs', hbs⟩ := GlobalType.Branches.step_of_project_select_branch bs fun hm => by
      obtain ⟨tp, htp, hbp⟩ := hpm hm
      obtain ⟨tq, htq, hbq⟩ := hqm hm
      obtain ⟨lp, rfl, hlp⟩ := LocalType.braceEq_select_shape hbp
      obtain ⟨lq, rfl⟩ := LocalType.braceEq_branch_shape hbq
      exact ⟨⟨lp, htp, (LocalType.Branches.braceEq_mem_labels hlp label).mpr hl⟩, lq, htq⟩
    exact ⟨_, .choiceCongr hbs hne (Ne.symm hpr) (Ne.symm hqr) (Ne.symm hpr')
      (Ne.symm hqr')⟩

/-- Completeness for a choice, every branch at once. -/
private theorem GlobalType.Branches.step_of_project_select_branch {P S L : Type}
    [DecidableEq P] [DecidableEq S] [DecidableEq L] {p q : P} {label : L} :
    ∀ (bs : GlobalType.Branches P S L),
      (∀ {l : L} {G : GlobalType P S L}, (l, G) ∈ bs.entries →
        (∃ lbs, G.project p = some (.select q lbs) ∧ label ∈ lbs.labels) ∧
          ∃ lbs', G.project q = some (.branch p lbs')) →
      ∃ bs', GlobalType.Branches.Step bs (.choice p q label) bs'
  | .nil, _ => ⟨.nil, .nil⟩
  | .cons l head tail, H => by
    obtain ⟨⟨lbs, hp, hl⟩, lbs', hq⟩ := H (l := l) (G := head)
      List.mem_cons_self
    obtain ⟨head', hh⟩ := GlobalType.step_of_project_select_branch_core hp hl hq
    obtain ⟨tail', htl⟩ := GlobalType.Branches.step_of_project_select_branch tail fun hm =>
      H (List.mem_cons_of_mem _ hm)
    exact ⟨.cons l head' tail', .cons hh htl⟩

end

section Completeness

variable {P S L : Type} [DecidableEq P] [DecidableEq S] [DecidableEq L]

/-- Projection completeness for a message (if-direction of HYC Lemma 5.11 at
a matched pair): if `p` projects to a send of `s` to `q` and `q` projects to
a receive from `p`, the global type has a step with label `p → q : s`. -/
theorem GlobalType.step_of_project_send_recv {p q : P} {s : S}
    {G : GlobalType P S L} {t : LocalType P S L} {s' : S}
    {u : LocalType P S L} :
    G.project p = some (.send q s t) →
    G.project q = some (.recv p s' u) →
      ∃ G', G.Step (.msg p q s) G' := by
  intro hp hq
  exact GlobalType.step_of_project_send_recv_core hp hq

/-- Projection completeness for a choice (if-direction of HYC Lemma 5.11 at
a matched pair): if `p` projects to a selection towards `q` offering
`label` and `q` projects to a branch on `p`, the global type has a step with
label `p → q : label`. -/
theorem GlobalType.step_of_project_select_branch {p q : P} {label : L}
    {G : GlobalType P S L} {lbs lbs' : LocalType.Branches P S L} :
    G.project p = some (.select q lbs) → label ∈ lbs.labels →
      G.project q = some (.branch p lbs') →
        ∃ G', G.Step (.choice p q label) G' := by
  intro hp hl hq
  exact GlobalType.step_of_project_select_branch_core hp hl hq

end Completeness

namespace Multiparty

section Fidelity

variable {P S V L : Type} [DecidableEq P] [DecidableEq S] [DecidableEq L]
  {sortOf : V → S}

/-- Subject reduction (HYC Theorem 5.19 (2), finite synchronous): if a network
typed by `G` steps with label `ℓ` to `net'`, then `net'` is typed by
every `G'` with `G →ℓ G'`. -/
theorem Net.TypedBy.step_of_global {G G' : GlobalType P S L}
    {net net' : Net P V L} {ℓ : GlobalType.Label P S L} :
    Net.TypedBy sortOf G net → Net.Step sortOf net ℓ net' →
      G.Step ℓ G' → Net.TypedBy sortOf G' net' := by
  intro hT hstep hG
  obtain ⟨hwf, htyped⟩ := hT
  obtain ⟨-, hper⟩ := GlobalType.project_step_sound hwf hG
  refine ⟨hwf.step hG, fun peer => ?_⟩
  obtain ⟨t, t', ht, ht', hS, hR, hB⟩ := hper peer
  obtain ⟨t₀, ht₀, hty₀⟩ := htyped peer
  rw [ht, Option.some.injEq] at ht₀
  subst ht₀
  have hwft : t.WellFormed := GlobalType.project_wellFormed hwf.1 ht
  refine ⟨t', ht', ?_⟩
  cases hstep with
  | @msg sender receiver value next cont hne hsnd hrcv =>
    rcases eq_or_ne peer receiver with rfl | hpr
    · rw [Function.update_self]
      rw [hrcv] at hty₀
      obtain ⟨s, u, rfl, hu⟩ := hty₀.recv_inv
      cases hR rfl
      exact HasType.subst_zero hu rfl
    · rw [Function.update_of_ne hpr]
      rcases eq_or_ne peer sender with rfl | hps
      · rw [Function.update_self]
        rw [hsnd] at hty₀
        obtain ⟨s, u, rfl, -, hu⟩ := hty₀.send_inv
        cases hS rfl
        exact hu
      · rw [Function.update_of_ne hps]
        exact hty₀.braceEq (hB hps hpr)
  | @choice sender receiver label next cont branches hne hsnd hrcv hlook =>
    rcases eq_or_ne peer receiver with rfl | hpr
    · rw [Function.update_self]
      rw [hrcv] at hty₀
      obtain ⟨types, rfl, -, hlk⟩ := hty₀.branch_inv
      obtain ⟨u, hu, hcont⟩ := hlk label cont hlook
      cases hR rfl with
      | branch hmem =>
        cases hwft with
        | branch hbw =>
          rw [LocalType.Branches.lookup_of_mem_entries hbw hmem, Option.some.injEq] at hu
          subst hu
          exact hcont
    · rw [Function.update_of_ne hpr]
      rcases eq_or_ne peer sender with rfl | hps
      · rw [Function.update_self]
        rw [hsnd] at hty₀
        obtain ⟨bs, u, rfl, hu, hnext⟩ := hty₀.select_inv
        cases hS rfl with
        | select hmem =>
          cases hwft with
          | select hbw =>
            rw [LocalType.Branches.lookup_of_mem_entries hbw hmem, Option.some.injEq] at hu
            subst hu
            exact hnext
      · rw [Function.update_of_ne hps]
        exact hty₀.braceEq (hB hps hpr)

/-- Session fidelity (HYC Corollary 5.23 (1), finite synchronous): every step
of a network typed by `G` is matched by a global step with the same label
whose target types the stepped network. -/
theorem Net.TypedBy.step {G : GlobalType P S L}
    {net net' : Net P V L} {ℓ : GlobalType.Label P S L} :
    Net.TypedBy sortOf G net → Net.Step sortOf net ℓ net' →
      ∃ G', G.Step ℓ G' ∧ Net.TypedBy sortOf G' net' := by
  intro hT hstep
  obtain ⟨G', hG'⟩ : ∃ G', G.Step ℓ G' := by
    obtain ⟨-, htyped⟩ := hT
    cases hstep with
    | @msg sender receiver value next cont hne hsnd hrcv =>
      obtain ⟨ts, hts, htys⟩ := htyped sender
      rw [hsnd] at htys
      obtain ⟨s, t₁, rfl, hs, -⟩ := htys.send_inv
      obtain ⟨tr, htr, htyr⟩ := htyped receiver
      rw [hrcv] at htyr
      obtain ⟨s', u, rfl, -⟩ := htyr.recv_inv
      cases hs with
      | val hv =>
        subst hv
        exact GlobalType.step_of_project_send_recv hts htr
    | @choice sender receiver label next cont branches hne hsnd hrcv hlook =>
      obtain ⟨ts, hts, htys⟩ := htyped sender
      rw [hsnd] at htys
      obtain ⟨bs, u, rfl, hu, -⟩ := htys.select_inv
      obtain ⟨tr, htr, htyr⟩ := htyped receiver
      rw [hrcv] at htyr
      obtain ⟨types, rfl, -⟩ := htyr.branch_inv
      exact GlobalType.step_of_project_select_branch hts
        (LocalType.Branches.mem_labels_of_lookup hu) htr
  exact ⟨G', hG', hT.step_of_global hstep hG'⟩

omit [DecidableEq S] in
/-- The synchronous network LTS: states are networks, transitions are
`Net.Step`. -/
def Net.lts (sortOf : V → S) :
    _root_.Cslib.LTS (Net P V L) (GlobalType.Label P S L) :=
  ⟨Net.Step sortOf⟩

/-- Trace session fidelity: every finite trace of a network typed by `G` is a
trace of the global LTS from `G`, ending at a global type that types the
final network. -/
theorem Net.TypedBy.mtr {G : GlobalType P S L}
    {net net' : Net P V L} {ℓs : List (GlobalType.Label P S L)} :
    Net.TypedBy sortOf G net → (Net.lts sortOf).MTr net ℓs net' →
      ∃ G', GlobalType.lts.MTr G ℓs G' ∧ Net.TypedBy sortOf G' net' := by
  intro hT htr
  induction htr generalizing G with
  | refl => exact ⟨G, .refl, hT⟩
  | stepL hstep _ ih =>
    obtain ⟨G₁, hG₁, hT₁⟩ := hT.step hstep
    obtain ⟨G', hG', hT'⟩ := ih hT₁
    exact ⟨G', .stepL hG₁ hG', hT'⟩

end Fidelity

end Multiparty

end Cslib.SessionTypes
