/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Cslib.Foundations.Semantics.LTS.Basic
public import CSLibExt.Languages.SessionTypes.Multiparty.Projection

/-!
# Multiparty session types: finite synchronous LTS

Finite, synchronous, participant-addressed specialization of the global
and local transition systems of Honda, Yoshida and Carbone, *Multiparty
Asynchronous Session Types*, JACM 63(1), 2016: Definition 3.2 for global
steps, Definition 5.7 for local steps, Definition 5.8 for full
projection, the only-if direction of Lemma 5.11 for projection
soundness, and Proposition 4.4 for preservation of well-formedness.
This file's finite reading is a project specialization, not a verbatim
source statement: there is no parallel composition, recursion, channel
index, output permutation, queue, or asynchrony.

Two specialization choices are forced by the merged finite projection.
First, the congruence rules require neither prefix participant to occur
in the moving label; the source's weaker asynchronous side condition
would allow a later interaction involving the prefix sender to fire first.
Second, bystanders are preserved only up to brace equality, not
syntactic equality, because third-party projection returns the first
branch's projection after a choice step.

No completeness or determinacy of projection, process typing, subject
reduction, session fidelity, progress, or claim about the source's
asynchronous development is made here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.SessionTypes

/-- Labels of the global LTS: a message or a chosen branch between two
participants. -/
inductive GlobalType.Label (P S L : Type) where
  | msg (sender receiver : P) (payload : S) : GlobalType.Label P S L
  | choice (sender receiver : P) (label : L) : GlobalType.Label P S L
deriving DecidableEq

/-- The sender of a global label. -/
def GlobalType.Label.sender {P S L : Type} :
    GlobalType.Label P S L → P
  | .msg sender _ _ => sender
  | .choice sender _ _ => sender

/-- The receiver of a global label. -/
def GlobalType.Label.receiver {P S L : Type} :
    GlobalType.Label P S L → P
  | .msg _ receiver _ => receiver
  | .choice _ receiver _ => receiver

/-- Actions performed by one local end point. -/
inductive LocalType.Action (P S L : Type) where
  | send (peer : P) (payload : S) : LocalType.Action P S L
  | recv (peer : P) (payload : S) : LocalType.Action P S L
  | select (peer : P) (label : L) : LocalType.Action P S L
  | branch (peer : P) (label : L) : LocalType.Action P S L
deriving DecidableEq

/-- The local action of a global label's sender. -/
def GlobalType.Label.senderAction {P S L : Type} :
    GlobalType.Label P S L → LocalType.Action P S L
  | .msg _ receiver payload => .send receiver payload
  | .choice _ receiver label => .select receiver label

/-- The local action of a global label's receiver. -/
def GlobalType.Label.receiverAction {P S L : Type} :
    GlobalType.Label P S L → LocalType.Action P S L
  | .msg sender _ payload => .recv sender payload
  | .choice sender _ label => .branch sender label

mutual
/-- Synchronous steps of finite global types, specializing [GR1]-[GR4].
In the two congruence rules, neither participant of the outer prefix may
occur in the moving label. Choice congruence also requires a nonempty branch list. -/
inductive GlobalType.Step {P S L : Type} :
    GlobalType P S L → GlobalType.Label P S L → GlobalType P S L → Prop where
  | msg {sender receiver : P} {payload : S} {next : GlobalType P S L} :
      GlobalType.Step (.msg sender receiver payload next)
        (.msg sender receiver payload) next
  | choice {sender receiver : P} {branches : GlobalType.Branches P S L}
      {label : L} {next : GlobalType P S L} :
      (label, next) ∈ branches.entries →
      GlobalType.Step (.choice sender receiver branches)
        (.choice sender receiver label) next
  | msgCongr {sender receiver : P} {payload : S}
      {next next' : GlobalType P S L} {label : GlobalType.Label P S L} :
      GlobalType.Step next label next' →
      sender ≠ label.sender → sender ≠ label.receiver →
      receiver ≠ label.sender → receiver ≠ label.receiver →
      GlobalType.Step (.msg sender receiver payload next) label
        (.msg sender receiver payload next')
  | choiceCongr {sender receiver : P}
      {branches branches' : GlobalType.Branches P S L}
      {label : GlobalType.Label P S L} :
      GlobalType.Branches.Step branches label branches' →
      branches ≠ .nil →
      sender ≠ label.sender → sender ≠ label.receiver →
      receiver ≠ label.sender → receiver ≠ label.receiver →
      GlobalType.Step (.choice sender receiver branches) label
        (.choice sender receiver branches')

/-- Every branch performs the same global label, keeping labels and
order. -/
inductive GlobalType.Branches.Step {P S L : Type} :
    GlobalType.Branches P S L → GlobalType.Label P S L →
      GlobalType.Branches P S L → Prop where
  | nil {label : GlobalType.Label P S L} :
      GlobalType.Branches.Step .nil label .nil
  | cons {label : L} {head head' : GlobalType P S L}
      {tail tail' : GlobalType.Branches P S L}
      {stepLabel : GlobalType.Label P S L} :
      GlobalType.Step head stepLabel head' →
      GlobalType.Branches.Step tail stepLabel tail' →
      GlobalType.Branches.Step (.cons label head tail) stepLabel
        (.cons label head' tail')
end

/-- Steps of one local end point. -/
inductive LocalType.Step {P S L : Type} :
    LocalType P S L → LocalType.Action P S L → LocalType P S L → Prop where
  | send {peer : P} {payload : S} {next : LocalType P S L} :
      LocalType.Step (.send peer payload next) (.send peer payload) next
  | recv {peer : P} {payload : S} {next : LocalType P S L} :
      LocalType.Step (.recv peer payload next) (.recv peer payload) next
  | select {peer : P} {branches : LocalType.Branches P S L}
      {label : L} {next : LocalType P S L} :
      (label, next) ∈ branches.entries →
      LocalType.Step (.select peer branches) (.select peer label) next
  | branch {peer : P} {branches : LocalType.Branches P S L}
      {label : L} {next : LocalType P S L} :
      (label, next) ∈ branches.entries →
      LocalType.Step (.branch peer branches) (.branch peer label) next

/-- The global LTS as a `Cslib.LTS`. -/
def GlobalType.lts {P S L : Type} :
    _root_.Cslib.LTS (GlobalType P S L) (GlobalType.Label P S L) :=
  ⟨GlobalType.Step⟩

/-- The local LTS as a `Cslib.LTS`. -/
def LocalType.lts {P S L : Type} :
    _root_.Cslib.LTS (LocalType P S L) (LocalType.Action P S L) :=
  ⟨LocalType.Step⟩

/-- Brace equality is reflexive on local types. -/
theorem LocalType.braceEq_refl {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] (t : LocalType P S L) :
    t.braceEq t = true := by
  exact LocalType.rec (motive_1 := fun t => t.braceEq t = true)
    (motive_2 := fun bs => bs.braceEq bs = true) rfl
    (fun peer payload next ih => by
      simp only [LocalType.braceEq, beq_self_eq_true, Bool.and_eq_true,
        ih, and_self])
    (fun peer payload next ih => by
      simp only [LocalType.braceEq, beq_self_eq_true, Bool.and_eq_true,
        ih, and_self])
    (fun peer branches ih => by
      simp only [LocalType.braceEq, beq_self_eq_true, Bool.and_eq_true,
        ih, and_self])
    (fun peer branches ih => by
      simp only [LocalType.braceEq, beq_self_eq_true, Bool.and_eq_true,
        ih, and_self])
    rfl
    (fun label head tail ih_head ih_tail => by
      simp only [LocalType.Branches.braceEq, LocalType.Branches.lookup,
        LocalType.Branches.eraseLabel, ↓reduceIte, ih_head, ih_tail,
        Bool.and_self])
    t

/-- Brace equality is reflexive on local branch lists. -/
theorem LocalType.Branches.braceEq_refl {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L]
    (branches : LocalType.Branches P S L) :
    branches.braceEq branches = true := by
  exact LocalType.Branches.rec (motive_1 := fun t => t.braceEq t = true)
    (motive_2 := fun bs => bs.braceEq bs = true) rfl
    (fun peer payload next ih => by
      simp only [LocalType.braceEq, beq_self_eq_true, Bool.and_eq_true,
        ih, and_self])
    (fun peer payload next ih => by
      simp only [LocalType.braceEq, beq_self_eq_true, Bool.and_eq_true,
        ih, and_self])
    (fun peer branches ih => by
      simp only [LocalType.braceEq, beq_self_eq_true, Bool.and_eq_true,
        ih, and_self])
    (fun peer branches ih => by
      simp only [LocalType.braceEq, beq_self_eq_true, Bool.and_eq_true,
        ih, and_self])
    rfl
    (fun label head tail ih_head ih_tail => by
      simp only [LocalType.Branches.braceEq, LocalType.Branches.lookup,
        LocalType.Branches.eraseLabel, ↓reduceIte, ih_head, ih_tail,
        Bool.and_self])
    branches

/-- Brace equality is symmetric on local types. -/
theorem LocalType.braceEq_symm {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {t u : LocalType P S L} :
    t.braceEq u = true → u.braceEq t = true := by
  have hins : ∀ (bs : LocalType.Branches P S L) (l : L) (h' h : LocalType P S L)
      (tl : LocalType.Branches P S L), bs.lookup l = some h' → h'.braceEq h = true →
        (bs.eraseLabel l).braceEq tl = true → bs.braceEq (.cons l h tl) = true := by
    intro bs
    exact LocalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => ∀ (l : L) (h' h : LocalType P S L)
        (tl : LocalType.Branches P S L), bs.lookup l = some h' → h'.braceEq h = true →
          (bs.eraseLabel l).braceEq tl = true → bs.braceEq (.cons l h tl) = true)
      trivial
      (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun l h' h tl hlook _ _ => by
        simp only [LocalType.Branches.lookup, reduceCtorEq] at hlook)
      (fun l₀ h₀ bs₀ _ ih l h' h tl hlook hhead htail => by
        by_cases hl : l₀ = l
        · subst hl
          simp only [LocalType.Branches.lookup, ↓reduceIte] at hlook
          simp only [LocalType.Branches.eraseLabel, ↓reduceIte] at htail
          cases hlook
          simp only [LocalType.Branches.braceEq, LocalType.Branches.lookup,
            LocalType.Branches.eraseLabel, ↓reduceIte, hhead, htail, Bool.and_self]
        · have hl' : ¬ l = l₀ := fun e => hl e.symm
          simp only [LocalType.Branches.lookup, hl', ↓reduceIte] at hlook
          simp only [LocalType.Branches.eraseLabel, hl', ↓reduceIte] at htail
          rcases htlk : tl.lookup l₀ with _ | h₀'
          · simp only [LocalType.Branches.braceEq, htlk, Bool.false_eq_true] at htail
          · simp only [LocalType.Branches.braceEq, htlk, Bool.and_eq_true] at htail
            obtain ⟨h₀eq, htail2⟩ := htail
            have hih := ih l h' h (tl.eraseLabel l₀) hlook hhead htail2
            simp only [LocalType.Branches.braceEq, LocalType.Branches.lookup,
              LocalType.Branches.eraseLabel, hl, htlk, ↓reduceIte, h₀eq, hih,
              Bool.and_self])
      bs
  have key : ∀ t u : LocalType P S L, t.braceEq u = true → u.braceEq t = true := by
    intro t
    exact LocalType.rec (motive_1 := fun t => ∀ u, t.braceEq u = true → u.braceEq t = true)
      (motive_2 := fun bs => ∀ bs', bs.braceEq bs' = true → bs'.braceEq bs = true)
      (fun u hu => by
        cases u
        · rfl
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu)
      (fun peer payload next ih u hu => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at hu ⊢
          obtain ⟨⟨rfl, rfl⟩, hcont⟩ := hu
          exact ⟨⟨rfl, rfl⟩, ih _ hcont⟩
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu)
      (fun peer payload next ih u hu => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at hu ⊢
          obtain ⟨⟨rfl, rfl⟩, hcont⟩ := hu
          exact ⟨⟨rfl, rfl⟩, ih _ hcont⟩
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu)
      (fun peer branches ih u hu => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at hu ⊢
          obtain ⟨rfl, hbr⟩ := hu
          exact ⟨rfl, ih _ hbr⟩
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu)
      (fun peer branches ih u hu => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at hu ⊢
          obtain ⟨rfl, hbr⟩ := hu
          exact ⟨rfl, ih _ hbr⟩)
      (fun bs' hbs => by
        cases bs'
        · rfl
        · simp only [LocalType.Branches.braceEq, Bool.false_eq_true] at hbs)
      (fun l h tl ih_h ih_tl bs' hbs => by
        rcases hlk : bs'.lookup l with _ | h'
        · simp only [LocalType.Branches.braceEq, hlk, Bool.false_eq_true] at hbs
        · simp only [LocalType.Branches.braceEq, hlk, Bool.and_eq_true] at hbs
          exact hins bs' l h' h tl hlk (ih_h h' hbs.1) (ih_tl _ hbs.2))
      t
  exact key t u

/-- Brace equality is symmetric on local branch lists. -/
theorem LocalType.Branches.braceEq_symm {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L]
    {branches branches' : LocalType.Branches P S L} :
    branches.braceEq branches' = true →
      branches'.braceEq branches = true := by
  have hins : ∀ (bs : LocalType.Branches P S L) (l : L) (h' h : LocalType P S L)
      (tl : LocalType.Branches P S L), bs.lookup l = some h' → h'.braceEq h = true →
        (bs.eraseLabel l).braceEq tl = true → bs.braceEq (.cons l h tl) = true := by
    intro bs
    exact LocalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => ∀ (l : L) (h' h : LocalType P S L)
        (tl : LocalType.Branches P S L), bs.lookup l = some h' → h'.braceEq h = true →
          (bs.eraseLabel l).braceEq tl = true → bs.braceEq (.cons l h tl) = true)
      trivial
      (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun l h' h tl hlook _ _ => by
        simp only [LocalType.Branches.lookup, reduceCtorEq] at hlook)
      (fun l₀ h₀ bs₀ _ ih l h' h tl hlook hhead htail => by
        by_cases hl : l₀ = l
        · subst hl
          simp only [LocalType.Branches.lookup, ↓reduceIte] at hlook
          simp only [LocalType.Branches.eraseLabel, ↓reduceIte] at htail
          cases hlook
          simp only [LocalType.Branches.braceEq, LocalType.Branches.lookup,
            LocalType.Branches.eraseLabel, ↓reduceIte, hhead, htail, Bool.and_self]
        · have hl' : ¬ l = l₀ := fun e => hl e.symm
          simp only [LocalType.Branches.lookup, hl', ↓reduceIte] at hlook
          simp only [LocalType.Branches.eraseLabel, hl', ↓reduceIte] at htail
          rcases htlk : tl.lookup l₀ with _ | h₀'
          · simp only [LocalType.Branches.braceEq, htlk, Bool.false_eq_true] at htail
          · simp only [LocalType.Branches.braceEq, htlk, Bool.and_eq_true] at htail
            obtain ⟨h₀eq, htail2⟩ := htail
            have hih := ih l h' h (tl.eraseLabel l₀) hlook hhead htail2
            simp only [LocalType.Branches.braceEq, LocalType.Branches.lookup,
              LocalType.Branches.eraseLabel, hl, htlk, ↓reduceIte, h₀eq, hih,
              Bool.and_self])
      bs
  have key : ∀ bs bs' : LocalType.Branches P S L,
      bs.braceEq bs' = true → bs'.braceEq bs = true := by
    intro bs
    exact LocalType.Branches.rec
      (motive_1 := fun t => ∀ u, t.braceEq u = true → u.braceEq t = true)
      (motive_2 := fun bs => ∀ bs', bs.braceEq bs' = true → bs'.braceEq bs = true)
      (fun u hu => by
        cases u
        · rfl
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu)
      (fun peer payload next ih u hu => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at hu ⊢
          obtain ⟨⟨rfl, rfl⟩, hcont⟩ := hu
          exact ⟨⟨rfl, rfl⟩, ih _ hcont⟩
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu)
      (fun peer payload next ih u hu => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at hu ⊢
          obtain ⟨⟨rfl, rfl⟩, hcont⟩ := hu
          exact ⟨⟨rfl, rfl⟩, ih _ hcont⟩
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu)
      (fun peer branches ih u hu => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at hu ⊢
          obtain ⟨rfl, hbr⟩ := hu
          exact ⟨rfl, ih _ hbr⟩
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu)
      (fun peer branches ih u hu => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.false_eq_true] at hu
        · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at hu ⊢
          obtain ⟨rfl, hbr⟩ := hu
          exact ⟨rfl, ih _ hbr⟩)
      (fun bs' hbs => by
        cases bs'
        · rfl
        · simp only [LocalType.Branches.braceEq, Bool.false_eq_true] at hbs)
      (fun l h tl ih_h ih_tl bs' hbs => by
        rcases hlk : bs'.lookup l with _ | h'
        · simp only [LocalType.Branches.braceEq, hlk, Bool.false_eq_true] at hbs
        · simp only [LocalType.Branches.braceEq, hlk, Bool.and_eq_true] at hbs
          exact hins bs' l h' h tl hlk (ih_h h' hbs.1) (ih_tl _ hbs.2))
      bs
  exact key branches branches'

/-- Brace equality is transitive on local types. -/
theorem LocalType.braceEq_trans {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {t u v : LocalType P S L} :
    t.braceEq u = true → u.braceEq v = true →
      t.braceEq v = true := by
  have hlk_ne : ∀ (bs : LocalType.Branches P S L) (a b : L), a ≠ b →
      (bs.eraseLabel b).lookup a = bs.lookup a := by
    intro bs
    exact LocalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => ∀ (a b : L), a ≠ b →
        (bs.eraseLabel b).lookup a = bs.lookup a)
      trivial
      (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun a b _ => by
        simp only [LocalType.Branches.eraseLabel,
          LocalType.Branches.lookup])
      (fun l₀ h₀ bs₀ _ ih a b hab => by
        by_cases hb : l₀ = b
        · subst hb
          by_cases ha : l₀ = a
          · exact (hab ha.symm).elim
          · have ha' : ¬ a = l₀ := fun e => ha e.symm
            simp only [LocalType.Branches.eraseLabel,
              LocalType.Branches.lookup, ha', ↓reduceIte]
        · have hb' : ¬ b = l₀ := fun e => hb e.symm
          by_cases ha : l₀ = a
          · subst ha
            simp only [LocalType.Branches.eraseLabel,
              LocalType.Branches.lookup, hb', ↓reduceIte]
          · have ha' : ¬ a = l₀ := fun e => ha e.symm
            simp only [LocalType.Branches.eraseLabel,
              LocalType.Branches.lookup, hb', ha', ↓reduceIte, ih a b hab])
      bs
  have her_comm : ∀ (bs : LocalType.Branches P S L) (a b : L),
      (bs.eraseLabel a).eraseLabel b = (bs.eraseLabel b).eraseLabel a := by
    intro bs
    exact LocalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => ∀ (a b : L),
        (bs.eraseLabel a).eraseLabel b = (bs.eraseLabel b).eraseLabel a)
      trivial
      (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun a b => by
        simp only [LocalType.Branches.eraseLabel])
      (fun l₀ h₀ bs₀ _ ih a b => by
        by_cases ha : l₀ = a
        · subst ha
          by_cases hb : l₀ = b
          · subst hb
            rfl
          · have hb' : ¬ b = l₀ := fun e => hb e.symm
            simp only [LocalType.Branches.eraseLabel, hb', ↓reduceIte]
        · have ha' : ¬ a = l₀ := fun e => ha e.symm
          by_cases hb : l₀ = b
          · subst hb
            simp only [LocalType.Branches.eraseLabel, ha', ↓reduceIte]
          · have hb' : ¬ b = l₀ := fun e => hb e.symm
            simp only [LocalType.Branches.eraseLabel, ha', hb', ↓reduceIte,
              ih a b])
      bs
  have hext : ∀ (bs bs' : LocalType.Branches P S L) (l : L) (h : LocalType P S L),
      bs.braceEq bs' = true → bs.lookup l = some h →
        ∃ h', bs'.lookup l = some h' ∧ h.braceEq h' = true ∧
          (bs.eraseLabel l).braceEq (bs'.eraseLabel l) = true := by
    intro bs
    exact LocalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => ∀ (bs' : LocalType.Branches P S L) (l : L)
        (h : LocalType P S L), bs.braceEq bs' = true → bs.lookup l = some h →
          ∃ h', bs'.lookup l = some h' ∧ h.braceEq h' = true ∧
            (bs.eraseLabel l).braceEq (bs'.eraseLabel l) = true)
      trivial
      (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun bs' l h _ hlk => by
        simp only [LocalType.Branches.lookup, reduceCtorEq] at hlk)
      (fun l₀ h₀ bs₀ _ ih bs' l h hb hlk => by
        by_cases hl : l = l₀
        · subst hl
          simp only [LocalType.Branches.lookup, ↓reduceIte,
            Option.some.injEq] at hlk
          subst hlk
          rcases hk : bs'.lookup l with _ | h₀'
          · simp only [LocalType.Branches.braceEq, hk, Bool.false_eq_true] at hb
          · simp only [LocalType.Branches.braceEq, hk, Bool.and_eq_true] at hb
            refine ⟨h₀', rfl, hb.1, ?_⟩
            simp only [LocalType.Branches.eraseLabel, ↓reduceIte]
            exact hb.2
        · simp only [LocalType.Branches.lookup, hl, ↓reduceIte] at hlk
          rcases hk : bs'.lookup l₀ with _ | h₀'
          · simp only [LocalType.Branches.braceEq, hk, Bool.false_eq_true] at hb
          · simp only [LocalType.Branches.braceEq, hk, Bool.and_eq_true] at hb
            obtain ⟨h'', hl', hh'', her⟩ := ih (bs'.eraseLabel l₀) l h hb.2 hlk
            rw [hlk_ne bs' l l₀ hl] at hl'
            refine ⟨h'', hl', hh'', ?_⟩
            simp only [LocalType.Branches.eraseLabel, hl, ↓reduceIte,
              LocalType.Branches.braceEq, hlk_ne bs' l₀ l (Ne.symm hl), hk,
              Bool.and_eq_true]
            rw [her_comm bs' l l₀]
            exact ⟨hb.1, her⟩)
      bs
  have key : ∀ t u v : LocalType P S L, t.braceEq u = true → u.braceEq v = true →
      t.braceEq v = true := by
    intro t
    exact LocalType.rec
      (motive_1 := fun t => ∀ u v, t.braceEq u = true → u.braceEq v = true →
        t.braceEq v = true)
      (motive_2 := fun bs => ∀ bs' bs'', bs.braceEq bs' = true →
        bs'.braceEq bs'' = true → bs.braceEq bs'' = true)
      (fun u v h1 h2 => by
        cases u
        · cases v
          · rfl
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1)
      (fun peer payload next ih u v h1 h2 => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · cases v
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
            obtain ⟨⟨rfl, rfl⟩, hn1⟩ := h1
            obtain ⟨⟨rfl, rfl⟩, hn2⟩ := h2
            exact ⟨⟨rfl, rfl⟩, ih _ _ hn1 hn2⟩
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1)
      (fun peer payload next ih u v h1 h2 => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · cases v
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
            obtain ⟨⟨rfl, rfl⟩, hn1⟩ := h1
            obtain ⟨⟨rfl, rfl⟩, hn2⟩ := h2
            exact ⟨⟨rfl, rfl⟩, ih _ _ hn1 hn2⟩
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1)
      (fun peer branches ih u v h1 h2 => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · cases v
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
            obtain ⟨rfl, hb1⟩ := h1
            obtain ⟨rfl, hb2⟩ := h2
            exact ⟨rfl, ih _ _ hb1 hb2⟩
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1)
      (fun peer branches ih u v h1 h2 => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · cases v
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
            obtain ⟨rfl, hb1⟩ := h1
            obtain ⟨rfl, hb2⟩ := h2
            exact ⟨rfl, ih _ _ hb1 hb2⟩)
      (fun bs' bs'' h1 h2 => by
        cases bs'
        · cases bs''
          · rfl
          · simp only [LocalType.Branches.braceEq, Bool.false_eq_true] at h2
        · simp only [LocalType.Branches.braceEq, Bool.false_eq_true] at h1)
      (fun l h tl ih_h ih_tl bs' bs'' h1 h2 => by
        rcases hlk : bs'.lookup l with _ | h'
        · simp only [LocalType.Branches.braceEq, hlk, Bool.false_eq_true] at h1
        · simp only [LocalType.Branches.braceEq, hlk, Bool.and_eq_true] at h1
          obtain ⟨h'', hlk'', hh'', her⟩ := hext bs' bs'' l h' h2 hlk
          simp only [LocalType.Branches.braceEq, hlk'', Bool.and_eq_true]
          exact ⟨ih_h h' h'' h1.1 hh'', ih_tl _ _ h1.2 her⟩)
      t
  exact key t u v

/-- Brace equality is transitive on local branch lists. -/
theorem LocalType.Branches.braceEq_trans {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L]
    {branches branches' branches'' : LocalType.Branches P S L} :
    branches.braceEq branches' = true →
      branches'.braceEq branches'' = true →
      branches.braceEq branches'' = true := by
  have hlk_ne : ∀ (bs : LocalType.Branches P S L) (a b : L), a ≠ b →
      (bs.eraseLabel b).lookup a = bs.lookup a := by
    intro bs
    exact LocalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => ∀ (a b : L), a ≠ b →
        (bs.eraseLabel b).lookup a = bs.lookup a)
      trivial
      (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun a b _ => by
        simp only [LocalType.Branches.eraseLabel,
          LocalType.Branches.lookup])
      (fun l₀ h₀ bs₀ _ ih a b hab => by
        by_cases hb : l₀ = b
        · subst hb
          by_cases ha : l₀ = a
          · exact (hab ha.symm).elim
          · have ha' : ¬ a = l₀ := fun e => ha e.symm
            simp only [LocalType.Branches.eraseLabel,
              LocalType.Branches.lookup, ha', ↓reduceIte]
        · have hb' : ¬ b = l₀ := fun e => hb e.symm
          by_cases ha : l₀ = a
          · subst ha
            simp only [LocalType.Branches.eraseLabel,
              LocalType.Branches.lookup, hb', ↓reduceIte]
          · have ha' : ¬ a = l₀ := fun e => ha e.symm
            simp only [LocalType.Branches.eraseLabel,
              LocalType.Branches.lookup, hb', ha', ↓reduceIte, ih a b hab])
      bs
  have her_comm : ∀ (bs : LocalType.Branches P S L) (a b : L),
      (bs.eraseLabel a).eraseLabel b = (bs.eraseLabel b).eraseLabel a := by
    intro bs
    exact LocalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => ∀ (a b : L),
        (bs.eraseLabel a).eraseLabel b = (bs.eraseLabel b).eraseLabel a)
      trivial
      (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun a b => by
        simp only [LocalType.Branches.eraseLabel])
      (fun l₀ h₀ bs₀ _ ih a b => by
        by_cases ha : l₀ = a
        · subst ha
          by_cases hb : l₀ = b
          · subst hb
            rfl
          · have hb' : ¬ b = l₀ := fun e => hb e.symm
            simp only [LocalType.Branches.eraseLabel, hb', ↓reduceIte]
        · have ha' : ¬ a = l₀ := fun e => ha e.symm
          by_cases hb : l₀ = b
          · subst hb
            simp only [LocalType.Branches.eraseLabel, ha', ↓reduceIte]
          · have hb' : ¬ b = l₀ := fun e => hb e.symm
            simp only [LocalType.Branches.eraseLabel, ha', hb', ↓reduceIte,
              ih a b])
      bs
  have hext : ∀ (bs bs' : LocalType.Branches P S L) (l : L) (h : LocalType P S L),
      bs.braceEq bs' = true → bs.lookup l = some h →
        ∃ h', bs'.lookup l = some h' ∧ h.braceEq h' = true ∧
          (bs.eraseLabel l).braceEq (bs'.eraseLabel l) = true := by
    intro bs
    exact LocalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => ∀ (bs' : LocalType.Branches P S L) (l : L)
        (h : LocalType P S L), bs.braceEq bs' = true → bs.lookup l = some h →
          ∃ h', bs'.lookup l = some h' ∧ h.braceEq h' = true ∧
            (bs.eraseLabel l).braceEq (bs'.eraseLabel l) = true)
      trivial
      (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun bs' l h _ hlk => by
        simp only [LocalType.Branches.lookup, reduceCtorEq] at hlk)
      (fun l₀ h₀ bs₀ _ ih bs' l h hb hlk => by
        by_cases hl : l = l₀
        · subst hl
          simp only [LocalType.Branches.lookup, ↓reduceIte,
            Option.some.injEq] at hlk
          subst hlk
          rcases hk : bs'.lookup l with _ | h₀'
          · simp only [LocalType.Branches.braceEq, hk, Bool.false_eq_true] at hb
          · simp only [LocalType.Branches.braceEq, hk, Bool.and_eq_true] at hb
            refine ⟨h₀', rfl, hb.1, ?_⟩
            simp only [LocalType.Branches.eraseLabel, ↓reduceIte]
            exact hb.2
        · simp only [LocalType.Branches.lookup, hl, ↓reduceIte] at hlk
          rcases hk : bs'.lookup l₀ with _ | h₀'
          · simp only [LocalType.Branches.braceEq, hk, Bool.false_eq_true] at hb
          · simp only [LocalType.Branches.braceEq, hk, Bool.and_eq_true] at hb
            obtain ⟨h'', hl', hh'', her⟩ := ih (bs'.eraseLabel l₀) l h hb.2 hlk
            rw [hlk_ne bs' l l₀ hl] at hl'
            refine ⟨h'', hl', hh'', ?_⟩
            simp only [LocalType.Branches.eraseLabel, hl, ↓reduceIte,
              LocalType.Branches.braceEq, hlk_ne bs' l₀ l (Ne.symm hl), hk,
              Bool.and_eq_true]
            rw [her_comm bs' l l₀]
            exact ⟨hb.1, her⟩)
      bs
  have key : ∀ bs bs' bs'' : LocalType.Branches P S L,
      bs.braceEq bs' = true → bs'.braceEq bs'' = true →
        bs.braceEq bs'' = true := by
    intro bs
    exact LocalType.Branches.rec
      (motive_1 := fun t => ∀ u v, t.braceEq u = true → u.braceEq v = true →
        t.braceEq v = true)
      (motive_2 := fun bs => ∀ bs' bs'', bs.braceEq bs' = true →
        bs'.braceEq bs'' = true → bs.braceEq bs'' = true)
      (fun u v h1 h2 => by
        cases u
        · cases v
          · rfl
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1)
      (fun peer payload next ih u v h1 h2 => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · cases v
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
            obtain ⟨⟨rfl, rfl⟩, hn1⟩ := h1
            obtain ⟨⟨rfl, rfl⟩, hn2⟩ := h2
            exact ⟨⟨rfl, rfl⟩, ih _ _ hn1 hn2⟩
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1)
      (fun peer payload next ih u v h1 h2 => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · cases v
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
            obtain ⟨⟨rfl, rfl⟩, hn1⟩ := h1
            obtain ⟨⟨rfl, rfl⟩, hn2⟩ := h2
            exact ⟨⟨rfl, rfl⟩, ih _ _ hn1 hn2⟩
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1)
      (fun peer branches ih u v h1 h2 => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · cases v
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
            obtain ⟨rfl, hb1⟩ := h1
            obtain ⟨rfl, hb2⟩ := h2
            exact ⟨rfl, ih _ _ hb1 hb2⟩
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1)
      (fun peer branches ih u v h1 h2 => by
        cases u
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · simp only [LocalType.braceEq, Bool.false_eq_true] at h1
        · cases v
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.false_eq_true] at h2
          · simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
            obtain ⟨rfl, hb1⟩ := h1
            obtain ⟨rfl, hb2⟩ := h2
            exact ⟨rfl, ih _ _ hb1 hb2⟩)
      (fun bs' bs'' h1 h2 => by
        cases bs'
        · cases bs''
          · rfl
          · simp only [LocalType.Branches.braceEq, Bool.false_eq_true] at h2
        · simp only [LocalType.Branches.braceEq, Bool.false_eq_true] at h1)
      (fun l h tl ih_h ih_tl bs' bs'' h1 h2 => by
        rcases hlk : bs'.lookup l with _ | h'
        · simp only [LocalType.Branches.braceEq, hlk, Bool.false_eq_true] at h1
        · simp only [LocalType.Branches.braceEq, hlk, Bool.and_eq_true] at h1
          obtain ⟨h'', hlk'', hh'', her⟩ := hext bs' bs'' l h' h2 hlk
          simp only [LocalType.Branches.braceEq, hlk'', Bool.and_eq_true]
          exact ⟨ih_h h' h'' h1.1 hh'', ih_tl _ _ h1.2 her⟩)
      bs
  exact key branches branches' branches''

/-- A defined projection of a label-well-formed global type is a
well-formed local type. -/
theorem GlobalType.project_wellFormed {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {G : GlobalType P S L} {peer : P}
    {t : LocalType P S L} :
    G.LabelsWellFormed → G.project peer = some t → t.WellFormed := by
  have key : ∀ (G : GlobalType P S L),
      G.LabelsWellFormed → ∀ (t : LocalType P S L),
        G.project peer = some t → t.WellFormed := by
    intro G
    exact GlobalType.rec
      (motive_1 := fun G => G.LabelsWellFormed →
        ∀ t, G.project peer = some t → t.WellFormed)
      (motive_2 := fun bs => (∀ lbs, bs.projectBranches peer = some lbs →
        lbs.labels = bs.labels) ∧
        (bs.LabelsWellFormed →
          (∀ lbs, bs.projectBranches peer = some lbs → lbs.WellFormed) ∧
          ∀ t, bs.projectThirdParty peer = some t → t.WellFormed))
      (fun _ t ht => by
        simp only [GlobalType.project, Option.some.injEq] at ht
        subst ht
        exact LocalType.WellFormed.end)
      (fun sender receiver payload next ih hwf t ht => by
        cases hwf
        simp only [GlobalType.project] at ht
        split_ifs at ht with h1 h2 h3
        · obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp ht
          exact LocalType.WellFormed.send (ih (by assumption) t' ht')
        · obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp ht
          exact LocalType.WellFormed.recv (ih (by assumption) t' ht')
        · exact ih (by assumption) t ht)
      (fun sender receiver branches ih hwf t ht => by
        cases hwf
        simp only [GlobalType.project] at ht
        split_ifs at ht with h1 h2 h3
        · obtain ⟨lbs, hl, rfl⟩ := Option.map_eq_some_iff.mp ht
          exact LocalType.WellFormed.select ((ih.2 (by assumption)).1 lbs hl)
        · obtain ⟨lbs, hl, rfl⟩ := Option.map_eq_some_iff.mp ht
          exact LocalType.WellFormed.branch ((ih.2 (by assumption)).1 lbs hl)
        · exact (ih.2 (by assumption)).2 t ht)
      (by
        refine ⟨?_, ?_⟩
        · intro lbs h
          simp only [GlobalType.Branches.projectBranches, Option.some.injEq] at h
          subst h
          rfl
        · intro _
          refine ⟨?_, ?_⟩
          · intro lbs h
            simp only [GlobalType.Branches.projectBranches, Option.some.injEq] at h
            subst h
            exact LocalType.Branches.WellFormed.nil
          · intro t h
            simp only [GlobalType.Branches.projectThirdParty, reduceCtorEq] at h)
      (fun label head tail ih_head ih_tail => by
        refine ⟨?_, ?_⟩
        · intro lbs h
          rcases hh : head.project peer with _ | h'
          · rcases ht : tail.projectBranches peer with _ | t'
            · simp only [GlobalType.Branches.projectBranches, hh, ht,
                reduceCtorEq] at h
            · simp only [GlobalType.Branches.projectBranches, hh, ht,
                reduceCtorEq] at h
          · rcases ht : tail.projectBranches peer with _ | t'
            · simp only [GlobalType.Branches.projectBranches, hh, ht,
                reduceCtorEq] at h
            · simp only [GlobalType.Branches.projectBranches, hh, ht,
                Option.some.injEq] at h
              subst h
              have hlab : t'.labels = tail.labels := ih_tail.1 t' ht
              simp only [LocalType.Branches.labels, GlobalType.Branches.labels,
                LocalType.Branches.entries, GlobalType.Branches.entries,
                List.map_cons] at hlab ⊢
              rw [hlab]
        · intro hb
          cases hb
          refine ⟨?_, ?_⟩
          · intro lbs h
            rcases hh : head.project peer with _ | h'
            · rcases ht : tail.projectBranches peer with _ | t'
              · simp only [GlobalType.Branches.projectBranches, hh, ht,
                  reduceCtorEq] at h
              · simp only [GlobalType.Branches.projectBranches, hh, ht,
                  reduceCtorEq] at h
            · rcases ht : tail.projectBranches peer with _ | t'
              · simp only [GlobalType.Branches.projectBranches, hh, ht,
                  reduceCtorEq] at h
              · simp only [GlobalType.Branches.projectBranches, hh, ht,
                  Option.some.injEq] at h
                subst h
                have hlab : t'.labels = tail.labels := ih_tail.1 t' ht
                have hfresh' : label ∉ t'.labels := by rw [hlab]; assumption
                exact LocalType.Branches.WellFormed.cons hfresh'
                  (ih_head (by assumption) h' hh)
                  ((ih_tail.2 (by assumption)).1 t' ht)
          · intro t h
            rcases hh : head.project peer with _ | h'
            · rcases ht : tail.projectList peer with _ | t'
              · simp only [GlobalType.Branches.projectThirdParty, hh, ht,
                  reduceCtorEq] at h
              · simp only [GlobalType.Branches.projectThirdParty, hh, ht,
                  reduceCtorEq] at h
            · rcases ht : tail.projectList peer with _ | t'
              · simp only [GlobalType.Branches.projectThirdParty, hh, ht,
                  reduceCtorEq] at h
              · simp only [GlobalType.Branches.projectThirdParty, hh, ht] at h
                split_ifs at h with hall
                simp only [Option.some.injEq] at h
                subst h
                exact ih_head (by assumption) h' hh)
      G
  exact fun hLW ht => key G hLW t ht

/-- A non-participant of a label-well-formed global type projects to
inaction. -/
theorem GlobalType.project_of_not_mem_participants {P S L : Type}
    [DecidableEq P] [DecidableEq S] [DecidableEq L]
    {G : GlobalType P S L} {peer : P} :
    G.LabelsWellFormed → peer ∉ G.participants →
      G.project peer = some .end := by
  intro hwf hnot
  exact GlobalType.rec
    (motive_1 := fun G => G.LabelsWellFormed → peer ∉ G.participants →
      G.project peer = some .end)
    (motive_2 := fun bs => bs.LabelsWellFormed → peer ∉ bs.participants →
      (∃ rest, bs.projectList peer = some rest ∧
        ∀ x ∈ rest, x = LocalType.end) ∧
      (bs ≠ .nil → bs.projectThirdParty peer = some .end))
    (fun _ _ => rfl)
    (fun sender receiver payload next ih hwf hnot => by
      cases hwf
      simp only [GlobalType.participants, Finset.mem_insert, not_or] at hnot
      obtain ⟨hne_s, hne_r, hnot_next⟩ := hnot
      simp only [GlobalType.project, hne_s, hne_r, ↓reduceIte]
      exact ih (by assumption) hnot_next)
    (fun sender receiver branches ih hwf hnot => by
      cases hwf
      simp only [GlobalType.participants, Finset.mem_insert, not_or] at hnot
      obtain ⟨hne_s, hne_r, hnot_bs⟩ := hnot
      simp only [GlobalType.project, hne_s, hne_r, ↓reduceIte]
      exact (ih (by assumption) hnot_bs).2 (by assumption))
    (fun _ _ => by
      have hall : ∀ x ∈ ([] : List (LocalType P S L)), x = .end := by
        intro x hx
        simp only [List.not_mem_nil] at hx
      exact ⟨⟨[], rfl, hall⟩, fun hne => (hne rfl).elim⟩)
    (fun label head tail ih_head ih_tail hwf hnot => by
      cases hwf
      simp only [GlobalType.Branches.participants, Finset.mem_union, not_or]
        at hnot
      obtain ⟨hnot_head, hnot_tail⟩ := hnot
      have hhead : head.project peer = some .end :=
        ih_head (by assumption) hnot_head
      have htail := ih_tail (by assumption) hnot_tail
      obtain ⟨rest_tail, hlist_tail, hall_tail⟩ := htail.1
      have hlist : (GlobalType.Branches.cons label head tail).projectList peer =
          some (.end :: rest_tail) := by
        simp only [GlobalType.Branches.projectList, hhead, hlist_tail]
      have hall : ∀ x ∈ .end :: rest_tail, x = LocalType.end := by
        intro x hx
        simp only [List.mem_cons] at hx
        cases hx with
        | inl h => exact h
        | inr h => exact hall_tail x h
      have hcheck : ((.end :: rest_tail).all fun x =>
          (.end :: rest_tail).all (x.braceEq ·)) = true :=
        List.all_eq_true.mpr fun x hx =>
          List.all_eq_true.mpr fun y hy => by
            have hx' : x = .end := hall x hx
            have hy' : y = .end := hall y hy
            simp only [hx', hy']
            rfl
      refine ⟨⟨.end :: rest_tail, hlist, hall⟩, fun _ => ?_⟩
      simp only [GlobalType.Branches.projectThirdParty, hhead, hlist_tail, hcheck,
        ↓reduceIte])
    G hwf hnot

/-- Every participant or non-participant has a defined projection from
a well-formed global type. -/
theorem GlobalType.WellFormed.project_isSome {P S L : Type}
    [DecidableEq P] [DecidableEq S] [DecidableEq L]
    {G : GlobalType P S L} :
    G.WellFormed → ∀ peer : P, (G.project peer).isSome := by
  intro hG peer
  by_cases hp : peer ∈ G.participants
  · exact hG.2 peer hp
  · rw [GlobalType.project_of_not_mem_participants hG.1 hp]
    rfl

/-- Shared invariant of a global step from a well-formed type: the target is
label-well-formed, the label has distinct principals, and every peer's
projections are related by the matching local step or brace equality. -/
private theorem GlobalType.step_key {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] :
    ∀ G : GlobalType P S L, ∀ (ℓ : GlobalType.Label P S L) (G' : GlobalType P S L),
      G.Step ℓ G' → G.WellFormed →
        G'.LabelsWellFormed ∧ ℓ.sender ≠ ℓ.receiver ∧
        ∀ peer : P, ∃ t t' : LocalType P S L,
          G.project peer = some t ∧ G'.project peer = some t' ∧
          (peer = ℓ.sender → LocalType.Step t ℓ.senderAction t') ∧
          (peer = ℓ.receiver → LocalType.Step t ℓ.receiverAction t') ∧
          (peer ≠ ℓ.sender → peer ≠ ℓ.receiver → t.braceEq t' = true) := by
  have hLW1 : ∀ (bs : GlobalType.Branches P S L), bs.LabelsWellFormed →
      ∀ (l : L) (G : GlobalType P S L), (l, G) ∈ bs.entries → G.LabelsWellFormed := by
    intro bs
    exact GlobalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => bs.LabelsWellFormed →
        ∀ (l : L) (G : GlobalType P S L), (l, G) ∈ bs.entries → G.LabelsWellFormed)
      trivial (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
      (fun _ l G hm => absurd hm List.not_mem_nil)
      (fun label head tail _ ih_t hwf l G hm => by
        cases hwf with
        | cons _ hh ht =>
          rcases List.mem_cons.1 hm with he | hm
          · rw [Prod.mk.injEq] at he
            rw [he.2]
            exact hh
          · exact ih_t ht l G hm)
      bs
  have hPB : ∀ (bs : GlobalType.Branches P S L) (p : P) (lbs : LocalType.Branches P S L),
      bs.projectBranches p = some lbs → ∀ (l : L) (G : GlobalType P S L),
        (l, G) ∈ bs.entries → ∃ t, G.project p = some t ∧ (l, t) ∈ lbs.entries := by
    intro bs
    exact GlobalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => ∀ (p : P) (lbs : LocalType.Branches P S L),
        bs.projectBranches p = some lbs → ∀ (l : L) (G : GlobalType P S L),
          (l, G) ∈ bs.entries → ∃ t, G.project p = some t ∧ (l, t) ∈ lbs.entries)
      trivial (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
      (fun _ _ _ l G hm => absurd hm List.not_mem_nil)
      (fun label head tail _ ih_t p lbs h l G hm => by
        rcases hh : head.project p with _ | hp
        · simp only [GlobalType.Branches.projectBranches, hh, reduceCtorEq] at h
        · rcases ht : tail.projectBranches p with _ | tp
          · simp only [GlobalType.Branches.projectBranches, hh, ht, reduceCtorEq] at h
          · simp only [GlobalType.Branches.projectBranches, hh, ht, Option.some.injEq] at h
            subst h
            rcases List.mem_cons.1 hm with he | hm
            · rw [Prod.mk.injEq] at he
              obtain ⟨rfl, rfl⟩ := he
              exact ⟨hp, hh, List.mem_cons.2 (Or.inl rfl)⟩
            · obtain ⟨t, ht1, ht2⟩ := ih_t p tp ht l G hm
              exact ⟨t, ht1, List.mem_cons.2 (Or.inr ht2)⟩)
      bs
  have hPL : ∀ (bs : GlobalType.Branches P S L) (p : P) (ts : List (LocalType P S L)),
      bs.projectList p = some ts → ∀ (l : L) (G : GlobalType P S L),
        (l, G) ∈ bs.entries → ∃ t, G.project p = some t ∧ t ∈ ts := by
    intro bs
    exact GlobalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => ∀ (p : P) (ts : List (LocalType P S L)),
        bs.projectList p = some ts → ∀ (l : L) (G : GlobalType P S L),
          (l, G) ∈ bs.entries → ∃ t, G.project p = some t ∧ t ∈ ts)
      trivial (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
      (fun _ _ _ l G hm => absurd hm List.not_mem_nil)
      (fun label head tail _ ih_t p ts h l G hm => by
        rcases hh : head.project p with _ | hp
        · simp only [GlobalType.Branches.projectList, hh, reduceCtorEq] at h
        · rcases ht : tail.projectList p with _ | tp
          · simp only [GlobalType.Branches.projectList, hh, ht, reduceCtorEq] at h
          · simp only [GlobalType.Branches.projectList, hh, ht, Option.some.injEq] at h
            subst h
            rcases List.mem_cons.1 hm with he | hm
            · rw [Prod.mk.injEq] at he
              obtain ⟨rfl, rfl⟩ := he
              exact ⟨hp, hh, List.mem_cons.2 (Or.inl rfl)⟩
            · obtain ⟨t, ht1, ht2⟩ := ih_t p tp ht l G hm
              exact ⟨t, ht1, List.mem_cons.2 (Or.inr ht2)⟩)
      bs
  have hTP : ∀ (bs : GlobalType.Branches P S L) (p : P) (T : LocalType P S L),
      bs.projectThirdParty p = some T → ∃ rest, bs.projectList p = some (T :: rest) ∧
        ∀ x ∈ T :: rest, ∀ y ∈ T :: rest, x.braceEq y = true := by
    intro bs p T h
    cases bs with
    | nil => simp only [GlobalType.Branches.projectThirdParty, reduceCtorEq] at h
    | cons label head tail =>
      rcases hh : head.project p with _ | hp
      · simp only [GlobalType.Branches.projectThirdParty, hh, reduceCtorEq] at h
      · rcases hl : tail.projectList p with _ | rest
        · simp only [GlobalType.Branches.projectThirdParty, hh, hl, reduceCtorEq] at h
        · simp only [GlobalType.Branches.projectThirdParty, hh, hl] at h
          split_ifs at h with hall
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨rest, by simp only [GlobalType.Branches.projectList, hh, hl], ?_⟩
          intro x hx y hy
          exact List.all_eq_true.mp (List.all_eq_true.mp hall x hx) y hy
  have hTPmk : ∀ (bs : GlobalType.Branches P S L) (p : P) (T : LocalType P S L)
      (rest : List (LocalType P S L)), bs.projectList p = some (T :: rest) →
        (∀ x ∈ T :: rest, ∀ y ∈ T :: rest, x.braceEq y = true) →
        bs.projectThirdParty p = some T := by
    intro bs p T rest h hpair
    cases bs with
    | nil =>
      simp only [GlobalType.Branches.projectList, Option.some.injEq, reduceCtorEq] at h
    | cons label head tail =>
      rcases hh : head.project p with _ | hp
      · simp only [GlobalType.Branches.projectList, hh, reduceCtorEq] at h
      · rcases hl : tail.projectList p with _ | tp
        · simp only [GlobalType.Branches.projectList, hh, hl, reduceCtorEq] at h
        · simp only [GlobalType.Branches.projectList, hh, hl, Option.some.injEq,
            List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hall : ((hp :: tp).all fun t => (hp :: tp).all (LocalType.braceEq t)) = true :=
            List.all_eq_true.mpr fun x hx => List.all_eq_true.mpr fun y hy => hpair x hx y hy
          simp only [GlobalType.Branches.projectThirdParty, hh, hl, hall, ↓reduceIte]
  have hF2 : ∀ {Q : LocalType P S L → LocalType P S L → Prop}
      (xs ys : List (LocalType P S L)), List.Forall₂ Q xs ys →
        ∀ y ∈ ys, ∃ x ∈ xs, Q x y := by
    intro Q xs ys h
    induction h with
    | nil => intro y hy; exact absurd hy List.not_mem_nil
    | @cons a b l₁ l₂ hq _ ih =>
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨a, List.mem_cons.2 (Or.inl rfl), hq⟩
      · obtain ⟨x, hx, hqx⟩ := ih y hy
        exact ⟨x, List.mem_cons.2 (Or.inr hx), hqx⟩
  have hnodup : ∀ bs : LocalType.Branches P S L, bs.WellFormed → bs.labels.Nodup := by
    intro bs
    exact LocalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => bs.WellFormed → bs.labels.Nodup)
      trivial (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial) (fun _ _ _ => trivial)
      (fun _ => List.nodup_nil)
      (fun l h tl _ ih hwf => by
        cases hwf with
        | cons hf _ ht =>
          simp only [LocalType.Branches.labels, LocalType.Branches.entries, List.map_cons,
            List.nodup_cons]
          exact ⟨hf, ih ht⟩)
      bs
  have hlkmem : ∀ bs : LocalType.Branches P S L, bs.labels.Nodup →
      ∀ (l : L) (t : LocalType P S L), (l, t) ∈ bs.entries → bs.lookup l = some t := by
    intro bs
    exact LocalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => bs.labels.Nodup →
        ∀ (l : L) (t : LocalType P S L), (l, t) ∈ bs.entries → bs.lookup l = some t)
      trivial (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial) (fun _ _ _ => trivial)
      (fun _ l t hm => absurd hm List.not_mem_nil)
      (fun l₀ h₀ tl _ ih hnd l t hm => by
        simp only [LocalType.Branches.labels, LocalType.Branches.entries, List.map_cons,
          List.nodup_cons] at hnd
        rcases List.mem_cons.1 hm with he | hm
        · rw [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          simp only [LocalType.Branches.lookup, ↓reduceIte]
        · have hne : ¬ l = l₀ := fun he => hnd.1 (he ▸ List.mem_map_of_mem (f := Prod.fst) hm)
          simp only [LocalType.Branches.lookup, hne, ↓reduceIte]
          exact ih hnd.2 l t hm)
      bs
  have hlk_ne : ∀ (bs : LocalType.Branches P S L) (a b : L), a ≠ b →
      (bs.eraseLabel b).lookup a = bs.lookup a := by
    intro bs
    exact LocalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => ∀ (a b : L), a ≠ b →
        (bs.eraseLabel b).lookup a = bs.lookup a)
      trivial (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial) (fun _ _ _ => trivial)
      (fun _ _ _ => rfl)
      (fun l₀ h₀ bs₀ _ ih a b hab => by
        by_cases hb : b = l₀
        · subst hb
          simp only [LocalType.Branches.eraseLabel, ↓reduceIte, LocalType.Branches.lookup, hab]
        · simp only [LocalType.Branches.eraseLabel, hb, ↓reduceIte, LocalType.Branches.lookup,
            ih a b hab])
      bs
  have hlktr : ∀ (bs bs' : LocalType.Branches P S L) (l : L) (h : LocalType P S L),
      bs.braceEq bs' = true → bs.lookup l = some h →
        ∃ h', bs'.lookup l = some h' ∧ h.braceEq h' = true := by
    intro bs
    exact LocalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => ∀ (bs' : LocalType.Branches P S L) (l : L)
        (h : LocalType P S L), bs.braceEq bs' = true → bs.lookup l = some h →
          ∃ h', bs'.lookup l = some h' ∧ h.braceEq h' = true)
      trivial (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
      (fun _ _ _ => trivial) (fun _ _ _ => trivial)
      (fun _ _ _ _ hlk => by
        simp only [LocalType.Branches.lookup, reduceCtorEq] at hlk)
      (fun l₀ h₀ bs₀ _ ih bs' l h hb hlk => by
        rcases hk : bs'.lookup l₀ with _ | h₀'
        · simp only [LocalType.Branches.braceEq, hk, Bool.false_eq_true] at hb
        · simp only [LocalType.Branches.braceEq, hk, Bool.and_eq_true] at hb
          by_cases hl : l = l₀
          · subst hl
            simp only [LocalType.Branches.lookup, ↓reduceIte, Option.some.injEq] at hlk
            subst hlk
            exact ⟨h₀', hk, hb.1⟩
          · simp only [LocalType.Branches.lookup, hl, ↓reduceIte] at hlk
            obtain ⟨h', hl', hh'⟩ := ih (bs'.eraseLabel l₀) l h hb.2 hlk
            rw [hlk_ne bs' l l₀ hl] at hl'
            exact ⟨h', hl', hh'⟩)
      bs
  have hcompat : ∀ (x y x' y' : LocalType P S L) (a : LocalType.Action P S L),
      x.WellFormed → y.WellFormed → x.braceEq y = true →
        LocalType.Step x a x' → LocalType.Step y a y' → x'.braceEq y' = true := by
    intro x y x' y' a hwx hwy hb hx hy
    cases hx with
    | send =>
      cases hy
      simp only [LocalType.braceEq, beq_self_eq_true, Bool.true_and] at hb
      exact hb
    | recv =>
      cases hy
      simp only [LocalType.braceEq, beq_self_eq_true, Bool.true_and] at hb
      exact hb
    | @select p xbs l _ hmx =>
      cases hy with
      | @select _ ybs _ _ hmy =>
        simp only [LocalType.braceEq, beq_self_eq_true, Bool.true_and] at hb
        cases hwx with
        | select hxw =>
          cases hwy with
          | select hyw =>
            have hxl := hlkmem xbs (hnodup xbs hxw) l x' hmx
            have hyl := hlkmem ybs (hnodup ybs hyw) l y' hmy
            obtain ⟨y'', hy'', hxy⟩ := hlktr xbs ybs l x' hb hxl
            rw [hyl, Option.some.injEq] at hy''
            rw [hy'']
            exact hxy
    | @branch p xbs l _ hmx =>
      cases hy with
      | @branch _ ybs _ _ hmy =>
        simp only [LocalType.braceEq, beq_self_eq_true, Bool.true_and] at hb
        cases hwx with
        | branch hxw =>
          cases hwy with
          | branch hyw =>
            have hxl := hlkmem xbs (hnodup xbs hxw) l x' hmx
            have hyl := hlkmem ybs (hnodup ybs hyw) l y' hmy
            obtain ⟨y'', hy'', hxy⟩ := hlktr xbs ybs l x' hb hxl
            rw [hyl, Option.some.injEq] at hy''
            rw [hy'']
            exact hxy
  have hSRmsg : ∀ (s r : P) (pl : S) (next : GlobalType P S L),
      (GlobalType.msg s r pl next).WellFormed → s ≠ r := by
    intro s r pl next hw heq
    have hx := GlobalType.WellFormed.project_isSome hw s
    subst heq
    simp only [GlobalType.project, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at hx
  have hSRchoice : ∀ (s r : P) (bs : GlobalType.Branches P S L),
      (GlobalType.choice s r bs).WellFormed → s ≠ r := by
    intro s r bs hw heq
    have hx := GlobalType.WellFormed.project_isSome hw s
    subst heq
    simp only [GlobalType.project, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at hx
  have hWFmsg : ∀ (s r : P) (pl : S) (next : GlobalType P S L),
      (GlobalType.msg s r pl next).WellFormed → next.WellFormed := by
    intro s r pl next hw
    refine ⟨?_, fun p _ => ?_⟩
    · cases hw.1 with
      | msg hn => exact hn
    · have hx := GlobalType.WellFormed.project_isSome hw p
      simp only [GlobalType.project] at hx
      split_ifs at hx with h1 h2 h3
      · simp only [Option.isSome_none, Bool.false_eq_true] at hx
      · simp only [Option.isSome_map] at hx
        exact hx
      · simp only [Option.isSome_map] at hx
        exact hx
      · exact hx
  have hWFchoice : ∀ (s r : P) (bs : GlobalType.Branches P S L),
      (GlobalType.choice s r bs).WellFormed →
        ∀ (l : L) (G : GlobalType P S L), (l, G) ∈ bs.entries → G.WellFormed := by
    intro s r bs hw l G hm
    refine ⟨?_, fun p _ => ?_⟩
    · cases hw.1 with
      | choice _ hb => exact hLW1 bs hb l G hm
    · have hx := GlobalType.WellFormed.project_isSome hw p
      simp only [GlobalType.project] at hx
      split_ifs at hx with h1 h2 h3
      · simp only [Option.isSome_none, Bool.false_eq_true] at hx
      · simp only [Option.isSome_map] at hx
        obtain ⟨lbs, hlbs⟩ := Option.isSome_iff_exists.mp hx
        obtain ⟨t, ht, _⟩ := hPB bs p lbs hlbs l G hm
        simp only [ht, Option.isSome_some]
      · simp only [Option.isSome_map] at hx
        obtain ⟨lbs, hlbs⟩ := Option.isSome_iff_exists.mp hx
        obtain ⟨t, ht, _⟩ := hPB bs p lbs hlbs l G hm
        simp only [ht, Option.isSome_some]
      · obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp hx
        obtain ⟨rest, hpl, _⟩ := hTP bs p T hT
        obtain ⟨t, ht, _⟩ := hPL bs p _ hpl l G hm
        simp only [ht, Option.isSome_some]
  have key : ∀ G : GlobalType P S L, ∀ (ℓ : GlobalType.Label P S L) (G' : GlobalType P S L),
      G.Step ℓ G' → G.WellFormed →
        G'.LabelsWellFormed ∧ ℓ.sender ≠ ℓ.receiver ∧
        ∀ peer : P, ∃ t t' : LocalType P S L,
          G.project peer = some t ∧ G'.project peer = some t' ∧
          (peer = ℓ.sender → LocalType.Step t ℓ.senderAction t') ∧
          (peer = ℓ.receiver → LocalType.Step t ℓ.receiverAction t') ∧
          (peer ≠ ℓ.sender → peer ≠ ℓ.receiver → t.braceEq t' = true) := by
    intro G
    exact GlobalType.rec
      (motive_1 := fun G => ∀ (ℓ : GlobalType.Label P S L) (G' : GlobalType P S L),
        G.Step ℓ G' → G.WellFormed →
          G'.LabelsWellFormed ∧ ℓ.sender ≠ ℓ.receiver ∧
          ∀ peer : P, ∃ t t' : LocalType P S L,
            G.project peer = some t ∧ G'.project peer = some t' ∧
            (peer = ℓ.sender → LocalType.Step t ℓ.senderAction t') ∧
            (peer = ℓ.receiver → LocalType.Step t ℓ.receiverAction t') ∧
            (peer ≠ ℓ.sender → peer ≠ ℓ.receiver → t.braceEq t' = true))
      (motive_2 := fun bs => ∀ (ℓ : GlobalType.Label P S L) (bs' : GlobalType.Branches P S L),
        GlobalType.Branches.Step bs ℓ bs' → bs.LabelsWellFormed →
          (∀ e ∈ bs.entries, e.2.WellFormed) →
          bs'.LabelsWellFormed ∧ bs'.labels = bs.labels ∧
          (bs ≠ .nil → ℓ.sender ≠ ℓ.receiver) ∧
          ∀ peer : P,
            (peer ≠ ℓ.sender → peer ≠ ℓ.receiver → ∀ lbs : LocalType.Branches P S L,
              bs.projectBranches peer = some lbs →
                ∃ lbs', bs'.projectBranches peer = some lbs' ∧ lbs.braceEq lbs' = true) ∧
            (∀ ts : List (LocalType P S L), bs.projectList peer = some ts →
              ∃ ts', bs'.projectList peer = some ts' ∧
                List.Forall₂ (fun t t' => t.WellFormed ∧ t'.WellFormed ∧
                  (peer = ℓ.sender → LocalType.Step t ℓ.senderAction t') ∧
                  (peer = ℓ.receiver → LocalType.Step t ℓ.receiverAction t') ∧
                  (peer ≠ ℓ.sender → peer ≠ ℓ.receiver → t.braceEq t' = true)) ts ts'))
      (fun ℓ G' hs _ => by cases hs)
      (fun s r pl next ih ℓ G' hs hw => by
        have hsr := hSRmsg s r pl next hw
        have hwn := hWFmsg s r pl next hw
        cases hs with
        | msg =>
          refine ⟨hwn.1, hsr, fun peer => ?_⟩
          obtain ⟨tn, htn⟩ :=
            Option.isSome_iff_exists.mp (GlobalType.WellFormed.project_isSome hwn peer)
          by_cases hps : peer = s
          · subst hps
            exact ⟨.send r pl tn, tn,
              by simp only [GlobalType.project, ↓reduceIte, hsr, htn, Option.map_some], htn,
              fun _ => LocalType.Step.send, fun h => absurd h hsr, fun h => absurd rfl h⟩
          · by_cases hpr : peer = r
            · subst hpr
              exact ⟨.recv s pl tn, tn,
                by simp only [GlobalType.project, hps, ↓reduceIte, htn, Option.map_some], htn,
                fun h => absurd h hps, fun _ => LocalType.Step.recv, fun _ h => absurd rfl h⟩
            · exact ⟨tn, tn, by simp only [GlobalType.project, hps, hpr, ↓reduceIte, htn], htn,
                fun h => absurd h hps, fun h => absurd h hpr,
                fun _ _ => LocalType.braceEq_refl tn⟩
        | msgCongr hnext hs1 hs2 hr1 hr2 =>
          obtain ⟨hLW', hsr', hper⟩ := ih ℓ _ hnext hwn
          refine ⟨GlobalType.LabelsWellFormed.msg hLW', hsr', fun peer => ?_⟩
          obtain ⟨tn, tn', htn, htn', hS, hR, hB⟩ := hper peer
          by_cases hps : peer = s
          · subst hps
            refine ⟨.send r pl tn, .send r pl tn',
              by simp only [GlobalType.project, ↓reduceIte, hsr, htn, Option.map_some],
              by simp only [GlobalType.project, ↓reduceIte, hsr, htn', Option.map_some],
              fun h => absurd h hs1, fun h => absurd h hs2, fun _ _ => ?_⟩
            simp only [LocalType.braceEq, beq_self_eq_true, Bool.true_and]
            exact hB hs1 hs2
          · by_cases hpr : peer = r
            · subst hpr
              refine ⟨.recv s pl tn, .recv s pl tn',
                by simp only [GlobalType.project, hps, ↓reduceIte, htn, Option.map_some],
                by simp only [GlobalType.project, hps, ↓reduceIte, htn', Option.map_some],
                fun h => absurd h hr1, fun h => absurd h hr2, fun _ _ => ?_⟩
              simp only [LocalType.braceEq, beq_self_eq_true, Bool.true_and]
              exact hB hr1 hr2
            · exact ⟨tn, tn', by simp only [GlobalType.project, hps, hpr, ↓reduceIte, htn],
                by simp only [GlobalType.project, hps, hpr, ↓reduceIte, htn'], hS, hR, hB⟩)
      (fun s r bs ih ℓ G' hs hw => by
        have hsr := hSRchoice s r bs hw
        have hent := hWFchoice s r bs hw
        obtain ⟨hne, hbLW⟩ : bs ≠ .nil ∧ bs.LabelsWellFormed := by
          cases hw.1 with
          | choice hne hb => exact ⟨hne, hb⟩
        cases hs with
        | @choice _ _ _ l _ hmem =>
          have hG' := hent l G' hmem
          refine ⟨hG'.1, hsr, fun peer => ?_⟩
          obtain ⟨t', ht'⟩ :=
            Option.isSome_iff_exists.mp (GlobalType.WellFormed.project_isSome hG' peer)
          have hx := GlobalType.WellFormed.project_isSome hw peer
          by_cases hps : peer = s
          · subst hps
            simp only [GlobalType.project, ↓reduceIte, hsr, Option.isSome_map] at hx
            obtain ⟨lbs, hlbs⟩ := Option.isSome_iff_exists.mp hx
            obtain ⟨t'', ht''1, ht''2⟩ := hPB bs _ lbs hlbs l G' hmem
            rw [ht', Option.some.injEq] at ht''1
            subst ht''1
            exact ⟨.select r lbs, t',
              by simp only [GlobalType.project, ↓reduceIte, hsr, hlbs, Option.map_some], ht',
              fun _ => LocalType.Step.select ht''2, fun h => absurd h hsr, fun h => absurd rfl h⟩
          · by_cases hpr : peer = r
            · subst hpr
              simp only [GlobalType.project, hps, ↓reduceIte, Option.isSome_map] at hx
              obtain ⟨lbs, hlbs⟩ := Option.isSome_iff_exists.mp hx
              obtain ⟨t'', ht''1, ht''2⟩ := hPB bs _ lbs hlbs l G' hmem
              rw [ht', Option.some.injEq] at ht''1
              subst ht''1
              exact ⟨.branch s lbs, t',
                by simp only [GlobalType.project, hps, ↓reduceIte, hlbs, Option.map_some], ht',
                fun h => absurd h hps, fun _ => LocalType.Step.branch ht''2,
                fun _ h => absurd rfl h⟩
            · simp only [GlobalType.project, hps, hpr, ↓reduceIte] at hx
              obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp hx
              obtain ⟨rest, hpl, hpair⟩ := hTP bs peer T hT
              obtain ⟨t'', ht''1, ht''2⟩ := hPL bs peer _ hpl l G' hmem
              rw [ht', Option.some.injEq] at ht''1
              subst ht''1
              exact ⟨T, t', by simp only [GlobalType.project, hps, hpr, ↓reduceIte, hT], ht',
                fun h => absurd h hps, fun h => absurd h hpr,
                fun _ _ => hpair T (List.mem_cons.2 (Or.inl rfl)) t' ht''2⟩
        | @choiceCongr _ _ _ bs' _ hbs' _ hs1 hs2 hr1 hr2 =>
          have hall : ∀ e ∈ bs.entries, e.2.WellFormed := fun e he => hent e.1 e.2 he
          obtain ⟨hLW', hlab, hsr', hper⟩ := ih ℓ bs' hbs' hbLW hall
          have hne' : bs' ≠ .nil := by
            intro h
            subst h
            cases bs with
            | nil => exact hne rfl
            | cons l hd tl =>
              simp only [GlobalType.Branches.labels, GlobalType.Branches.entries, List.map_cons,
                List.map_nil, reduceCtorEq] at hlab
          refine ⟨GlobalType.LabelsWellFormed.choice hne' hLW', hsr' hne, fun peer => ?_⟩
          have hx := GlobalType.WellFormed.project_isSome hw peer
          by_cases hps : peer = s
          · subst hps
            simp only [GlobalType.project, ↓reduceIte, hsr, Option.isSome_map] at hx
            obtain ⟨lbs, hlbs⟩ := Option.isSome_iff_exists.mp hx
            obtain ⟨lbs', hlbs', hbe⟩ := (hper _).1 hs1 hs2 lbs hlbs
            refine ⟨.select r lbs, .select r lbs',
              by simp only [GlobalType.project, ↓reduceIte, hsr, hlbs, Option.map_some],
              by simp only [GlobalType.project, ↓reduceIte, hsr, hlbs', Option.map_some],
              fun h => absurd h hs1, fun h => absurd h hs2, fun _ _ => ?_⟩
            simp only [LocalType.braceEq, beq_self_eq_true, Bool.true_and]
            exact hbe
          · by_cases hpr : peer = r
            · subst hpr
              simp only [GlobalType.project, hps, ↓reduceIte, Option.isSome_map] at hx
              obtain ⟨lbs, hlbs⟩ := Option.isSome_iff_exists.mp hx
              obtain ⟨lbs', hlbs', hbe⟩ := (hper _).1 hr1 hr2 lbs hlbs
              refine ⟨.branch s lbs, .branch s lbs',
                by simp only [GlobalType.project, hps, ↓reduceIte, hlbs, Option.map_some],
                by simp only [GlobalType.project, hps, ↓reduceIte, hlbs', Option.map_some],
                fun h => absurd h hr1, fun h => absurd h hr2, fun _ _ => ?_⟩
              simp only [LocalType.braceEq, beq_self_eq_true, Bool.true_and]
              exact hbe
            · simp only [GlobalType.project, hps, hpr, ↓reduceIte] at hx
              obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp hx
              obtain ⟨rest, hpl, hpair⟩ := hTP bs peer T hT
              obtain ⟨ts', hpl', hF⟩ := (hper peer).2 (T :: rest) hpl
              have hF2' := hF2 _ _ hF
              cases hF with
              | @cons _ T' _ rest' hq _ =>
                have hpair' : ∀ x ∈ T' :: rest', ∀ y ∈ T' :: rest', x.braceEq y = true := by
                  intro x' hx' y' hy'
                  obtain ⟨x, hx, hqx⟩ := hF2' x' hx'
                  obtain ⟨y, hy, hqy⟩ := hF2' y' hy'
                  by_cases h1 : peer = ℓ.sender
                  · exact hcompat x y x' y' _ hqx.1 hqy.1 (hpair x hx y hy)
                      (hqx.2.2.1 h1) (hqy.2.2.1 h1)
                  · by_cases h2 : peer = ℓ.receiver
                    · exact hcompat x y x' y' _ hqx.1 hqy.1 (hpair x hx y hy)
                        (hqx.2.2.2.1 h2) (hqy.2.2.2.1 h2)
                    · exact LocalType.braceEq_trans
                        (LocalType.braceEq_trans
                          (LocalType.braceEq_symm (hqx.2.2.2.2 h1 h2))
                          (hpair x hx y hy))
                        (hqy.2.2.2.2 h1 h2)
                exact ⟨T, T', by simp only [GlobalType.project, hps, hpr, ↓reduceIte, hT],
                  by simp only [GlobalType.project, hps, hpr, ↓reduceIte,
                    hTPmk bs' peer T' rest' hpl' hpair'],
                  hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2⟩)
      (fun ℓ bs' hs _ _ => by
        cases hs
        refine ⟨GlobalType.Branches.LabelsWellFormed.nil, rfl, fun h => absurd rfl h,
          fun peer => ⟨fun _ _ lbs h => ?_, fun ts h => ?_⟩⟩
        · simp only [GlobalType.Branches.projectBranches, Option.some.injEq] at h
          subst h
          exact ⟨.nil, rfl, rfl⟩
        · simp only [GlobalType.Branches.projectList, Option.some.injEq] at h
          subst h
          exact ⟨[], rfl, List.Forall₂.nil⟩)
      (fun label head tail ih_h ih_t ℓ bs' hs hLW hall => by
        cases hs with
        | @cons _ _ h' _ tl' _ hh ht =>
          cases hLW with
          | cons hfresh hhLW htLW =>
            have hhw : head.WellFormed := hall (label, head) (List.mem_cons.2 (Or.inl rfl))
            have htall : ∀ e ∈ tail.entries, e.2.WellFormed :=
              fun e he => hall e (List.mem_cons.2 (Or.inr he))
            obtain ⟨hhLW', hsr, hhper⟩ := ih_h ℓ h' hh hhw
            obtain ⟨htLW', htlab, _, htper⟩ := ih_t ℓ tl' ht htLW htall
            refine ⟨GlobalType.Branches.LabelsWellFormed.cons (by rwa [htlab]) hhLW' htLW',
              ?_, fun _ => hsr, fun peer => ⟨fun hps hpr lbs hl => ?_, fun ts hl => ?_⟩⟩
            · simp only [GlobalType.Branches.labels, GlobalType.Branches.entries,
                List.map_cons] at htlab ⊢
              rw [htlab]
            · rcases hh1 : head.project peer with _ | hp
              · simp only [GlobalType.Branches.projectBranches, hh1, reduceCtorEq] at hl
              · rcases ht1 : tail.projectBranches peer with _ | tp
                · simp only [GlobalType.Branches.projectBranches, hh1, ht1, reduceCtorEq] at hl
                · simp only [GlobalType.Branches.projectBranches, hh1, ht1,
                    Option.some.injEq] at hl
                  subst hl
                  obtain ⟨t, t', ht0, ht', _, _, hB⟩ := hhper peer
                  rw [hh1, Option.some.injEq] at ht0
                  subst ht0
                  obtain ⟨tp', htp', hB'⟩ := (htper peer).1 hps hpr tp ht1
                  refine ⟨.cons label t' tp',
                    by simp only [GlobalType.Branches.projectBranches, ht', htp'], ?_⟩
                  simp only [LocalType.Branches.braceEq, LocalType.Branches.lookup,
                    LocalType.Branches.eraseLabel, ↓reduceIte, hB hps hpr, hB', Bool.and_self]
            · rcases hh1 : head.project peer with _ | hp
              · simp only [GlobalType.Branches.projectList, hh1, reduceCtorEq] at hl
              · rcases ht1 : tail.projectList peer with _ | tp
                · simp only [GlobalType.Branches.projectList, hh1, ht1, reduceCtorEq] at hl
                · simp only [GlobalType.Branches.projectList, hh1, ht1, Option.some.injEq] at hl
                  subst hl
                  obtain ⟨t, t', ht0, ht', hS, hR, hB⟩ := hhper peer
                  rw [hh1, Option.some.injEq] at ht0
                  subst ht0
                  obtain ⟨tp', htp', hF⟩ := (htper peer).2 tp ht1
                  exact ⟨t' :: tp', by simp only [GlobalType.Branches.projectList, ht', htp'],
                    List.Forall₂.cons ⟨GlobalType.project_wellFormed hhLW hh1,
                      GlobalType.project_wellFormed hhLW' ht', hS, hR, hB⟩ hF⟩)
      G
  exact key

/-- Well-formedness is preserved by global steps. -/
theorem GlobalType.WellFormed.step {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {G G' : GlobalType P S L}
    {label : GlobalType.Label P S L} :
    G.WellFormed → G.Step label G' → G'.WellFormed := by
  intro hw hs
  obtain ⟨hLW', _, hper⟩ := GlobalType.step_key G label G' hs hw
  refine ⟨hLW', fun peer _ => ?_⟩
  obtain ⟨_, t', _, ht', _⟩ := hper peer
  simp only [ht', Option.isSome_some]

/-- Projection soundness: a global step induces exact local steps by
its sender and receiver, and every other participant's projection stays
brace-equal. -/
theorem GlobalType.project_step_sound {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {G G' : GlobalType P S L}
    {label : GlobalType.Label P S L}
    (hG : G.WellFormed) (hstep : G.Step label G') :
    label.sender ≠ label.receiver ∧
    ∀ peer : P, ∃ t t' : LocalType P S L,
      G.project peer = some t ∧ G'.project peer = some t' ∧
      (peer = label.sender → LocalType.Step t label.senderAction t') ∧
      (peer = label.receiver → LocalType.Step t label.receiverAction t') ∧
      (peer ≠ label.sender → peer ≠ label.receiver →
        t.braceEq t' = true) := by
  obtain ⟨_, hne, hcl⟩ := GlobalType.step_key G label G' hstep hG
  exact ⟨hne, hcl⟩

end Cslib.SessionTypes
