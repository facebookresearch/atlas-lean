/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.ClassicalProcesses.Reduction
public import Cslib.Foundations.Relation.Termination
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Classical processes: top-level cut elimination

Top-level cut elimination for Wadler's classical processes
(*Propositions as Sessions*, ICFP 2012, §2.7, Theorem 2): every typed
process reduces in finitely many steps to a process that is not a cut.
The process grammar and the reduction formalized here include no
introduction or communication rules for the exponentials or the
quantifiers; the propositions annotating processes and cuts are
unrestricted, and the theorem imposes no restriction on them. A process
is a cut when it has the form
`νx.(Q | R)`; a typed process that is not a cut acts on, or links, a free
channel of its environment, so it is ready for external communication. This
is the sense in which the theorem expresses deadlock freedom.

The development combines three facts about the one-step reduction `Step`.

* Termination: `Proc.measure` pairs the cut weight (the sum of the sizes of
  the cut propositions, an additive choice counting only its heavier branch)
  with the number of cuts not guarded by a prefix. It is invariant under
  structural equivalence and strictly decreases along every step, including
  reduction under a cut, so `Step` terminates on all processes.
* Progress: every typed cut takes a step.
* Preservation (`HasType.preservation_steps`): reduction keeps the typing
  environment.

The theorem refers to the reduction relation of `Reduction.lean`, which
extends the printed figures with the symmetric axiom-cut step and with
absorption-aware side conditions on the tensor commuting conversions and on
cut associativity, and corrects two misprints in §2.7. No process is typed
in the empty environment (`not_hasType_empty`), so a closed-process
formulation would be vacuous; the theorem is stated for an arbitrary
environment, as in the source. The reduction relation does not reduce
under prefixes, so the resulting process may still contain cuts guarded
by a prefix.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.ClassicalProcesses

variable {Atom : Type u}

/-- A process is a cut when it has the form `νx.(Q | R)` (Wadler, §2.7). -/
def Proc.IsCut (p : Proc Atom) : Prop := ∃ a q r, p = .cut a q r

/-- The cut weight of a process: the sum of the sizes of its cut propositions,
where an additive choice counts only its heavier branch. A principal `⊕`/`&`
step keeps one branch, and the `&` commuting conversion copies the opposite
premise into both branches. -/
noncomputable def Proc.cutWeight : Proc Atom → ℕ
  | .link _ _ => 0
  | .cut a p q => sizeOf a + p.cutWeight + q.cutWeight
  | .output _ p q => p.cutWeight + q.cutWeight
  | .input _ p => p.cutWeight
  | .selectLeft _ p => p.cutWeight
  | .selectRight _ p => p.cutWeight
  | .choice _ p q => max p.cutWeight q.cutWeight
  | .emptyOutput _ => 0
  | .emptyInput _ p => p.cutWeight
  | .emptyChoice _ => 0

/-- The number of cuts in the top-level cut tree of a process: the cuts
reachable from the root through cuts only, that is, not guarded by a
prefix. -/
def Proc.topCuts : Proc Atom → ℕ
  | .link _ _ => 0
  | .cut _ p q => p.topCuts + q.topCuts + 1
  | .output _ _ _ => 0
  | .input _ _ => 0
  | .selectLeft _ _ => 0
  | .selectRight _ _ => 0
  | .choice _ _ _ => 0
  | .emptyOutput _ => 0
  | .emptyInput _ _ => 0
  | .emptyChoice _ => 0

/-- The reduction measure: the cut weight, then the number of top-level cuts,
ordered lexicographically. -/
noncomputable def Proc.measure (p : Proc Atom) : ℕ ×ₗ ℕ :=
  toLex (p.cutWeight, p.topCuts)

/-- Lifting de Bruijn variables does not change the cut weight. -/
private theorem Proc.cutWeight_liftAt (p : Proc Atom) (c : ℕ) :
    (p.liftAt c).cutWeight = p.cutWeight := by
  induction p generalizing c <;> simp only [Proc.liftAt, Proc.cutWeight, *]

/-- Renaming channels does not change the cut weight. -/
private theorem Proc.cutWeight_rename (p : Proc Atom) (f : PiCalculus.Name → PiCalculus.Name) :
    (p.rename f).cutWeight = p.cutWeight := by
  induction p generalizing f <;> simp only [Proc.rename, Proc.cutWeight, *]

/-- Substituting a channel does not change the cut weight. -/
private theorem Proc.cutWeight_substAt (p : Proc Atom) (n : PiCalculus.Name) (c : ℕ) :
    (p.substAt n c).cutWeight = p.cutWeight := by
  induction p generalizing n c <;> simp only [Proc.substAt, Proc.cutWeight, *]

/-- Lifting de Bruijn variables does not change the number of top-level cuts. -/
private theorem Proc.topCuts_liftAt (p : Proc Atom) (c : ℕ) :
    (p.liftAt c).topCuts = p.topCuts := by
  induction p generalizing c <;> simp only [Proc.liftAt, Proc.topCuts, *]

/-- Renaming channels does not change the number of top-level cuts. -/
private theorem Proc.topCuts_rename (p : Proc Atom) (f : PiCalculus.Name → PiCalculus.Name) :
    (p.rename f).topCuts = p.topCuts := by
  induction p generalizing f <;> simp only [Proc.rename, Proc.topCuts, *]

/-- Substituting a channel does not change the number of top-level cuts. -/
private theorem Proc.topCuts_substAt (p : Proc Atom) (n : PiCalculus.Name) (c : ℕ) :
    (p.substAt n c).topCuts = p.topCuts := by
  induction p generalizing n c <;> simp only [Proc.substAt, Proc.topCuts, *]

/-- Every proposition has positive size. -/
private theorem sizeOf_proposition_pos (a : Logic.CLL.Proposition Atom) : 0 < sizeOf a := by
  induction a <;> simp <;> omega

/-- Structurally equivalent processes have the same cut weight and the same number of
top-level cuts. -/
private theorem Cong.weights_eq {p q : Proc Atom} (h : Cong p q) :
    (p.cutWeight, p.topCuts) = (q.cutWeight, q.topCuts) := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | swap a p q =>
    refine Prod.ext ?_ ?_
    · simp only [Proc.cutWeight, Logic.CLL.Proposition.dual_sizeOf]
      omega
    · simp only [Proc.topCuts]
      omega
  | assoc a b p q r _ _ =>
    refine Prod.ext ?_ ?_
    · simp only [Proc.cutWeight, Proc.cutWeight_liftAt, Proc.cutWeight_rename]
      omega
    · simp only [Proc.topCuts, Proc.topCuts_liftAt, Proc.topCuts_rename]
      omega

/-- The measure order unfolded: the cut weight decreases, or it is unchanged and the number
of top-level cuts decreases. -/
private theorem Proc.measure_lt_iff {p q : Proc Atom} :
    p.measure < q.measure ↔
      p.cutWeight < q.cutWeight ∨ p.cutWeight = q.cutWeight ∧ p.topCuts < q.topCuts :=
  Prod.Lex.toLex_lt_toLex

/-- Structurally equivalent processes have the same measure. -/
theorem Cong.measure_eq {p q : Proc Atom} (h : Cong p q) : p.measure = q.measure := by
  exact congrArg toLex h.weights_eq

/-- Every one-step reduction strictly decreases the measure, including
reduction under a cut and steps closed under structural equivalence. -/
theorem Step.measure_lt {p q : Proc Atom} (h : Step p q) : q.measure < p.measure := by
  induction h with
  | axCut a w r | axCutSymm a w r =>
    refine Proc.measure_lt_iff.mpr (Or.inl ?_)
    have ha := sizeOf_proposition_pos a
    simp only [Proc.subst, Proc.cutWeight, Proc.cutWeight_substAt]
    omega
  | tensorParr a b p₁ p₂ r =>
    refine Proc.measure_lt_iff.mpr (Or.inl ?_)
    simp only [Proc.cutWeight, Logic.CLL.Proposition.tensor.sizeOf_spec]
    omega
  | oplusWithLeft a b p₁ q₁ q₂ | oplusWithRight a b p₁ q₁ q₂ =>
    refine Proc.measure_lt_iff.mpr (Or.inl ?_)
    simp only [Proc.cutWeight, Logic.CLL.Proposition.oplus.sizeOf_spec]
    omega
  | oneBot r =>
    refine Proc.measure_lt_iff.mpr (Or.inl ?_)
    simp only [Proc.cutWeight, Proc.cutWeight_liftAt, Logic.CLL.Proposition.one.sizeOf_spec]
    omega
  | commTop c x r =>
    refine Proc.measure_lt_iff.mpr (Or.inl ?_)
    have hc := sizeOf_proposition_pos c
    simp only [Proc.cutWeight]
    omega
  | cutLeft a _ q ih | cutRight a p _ ih =>
    rw [Proc.measure_lt_iff] at ih ⊢
    simp only [Proc.cutWeight, Proc.topCuts]
    omega
  | cong h₁ _ h₃ ih =>
    rw [h₁.measure_eq, ← h₃.measure_eq]
    exact ih
  | commTensorLeft | commTensorRight | commChoice =>
    refine Proc.measure_lt_iff.mpr (Or.inr ⟨?_, ?_⟩)
    · simp only [Proc.cutWeight, Proc.cutWeight_liftAt, Proc.cutWeight_rename]
      omega
    · simp only [Proc.topCuts]
      omega
  | _ =>
    refine Proc.measure_lt_iff.mpr (Or.inr ⟨?_, ?_⟩)
    · simp only [Proc.cutWeight, Proc.cutWeight_liftAt, Proc.cutWeight_rename]
    · simp only [Proc.topCuts]
      omega

/-- One-step reduction terminates: there is no infinite reduction sequence,
whether or not the process is typed. -/
theorem Step.terminating : Relation.Terminating (Step (Atom := Atom)) := by
  refine Subrelation.wf ?_ (InvImage.wf Proc.measure wellFounded_lt)
  intro q p h
  exact Step.measure_lt h

/-- The premises of a typed cut. -/
private theorem HasType.cut_premises {C : Context Atom} {a : Logic.CLL.Proposition Atom}
    {p q : Proc Atom} (h : HasType C (.cut a p q)) :
    ∃ X Y : Context Atom, C = X ∪ Y ∧ HasType (X.lift.insert (.var 0) a) p ∧
      HasType (Y.lift.insert (.var 0) a.dual) q ∧ Finmap.Disjoint X Y := by
  cases h
  exact ⟨_, _, rfl, ‹_›, ‹_›, ‹_›⟩

/-- A typed link joins two distinct channels at dual propositions. -/
private theorem HasType.link_context {C : Context Atom} {w x : PiCalculus.Name}
    (h : HasType C (.link w x)) :
    ∃ a : Logic.CLL.Proposition Atom, w ≠ x ∧
      C = ((∅ : Context Atom).insert w a.dual).insert x a := by
  cases h
  exact ⟨_, ‹_›, rfl⟩

/-- A typed empty output holds exactly its subject, at `1`. -/
private theorem HasType.emptyOutput_context {C : Context Atom} {x : PiCalculus.Name}
    (h : HasType C (.emptyOutput x)) : C = (∅ : Context Atom).insert x .one := by
  cases h
  rfl

/-- The premise of a typed empty input. -/
private theorem HasType.emptyInput_premise {C : Context Atom} {x : PiCalculus.Name}
    {p : Proc Atom} (h : HasType C (.emptyInput x p)) :
    ∃ Γ : Context Atom, C = Γ.insert x .bot ∧ HasType Γ p ∧ x ∉ Γ := by
  cases h
  exact ⟨_, rfl, ‹_›, ‹_›⟩

/-- A name in which the variable `c` is not free under `d` binders is a lift at `c + d`. -/
private theorem exists_eq_liftName_add {x : PiCalculus.Name} {c d : ℕ}
    (h : PiCalculus.Name.var c ∉ freeNameAt d x) :
    ∃ x₀, x = PiCalculus.liftName (c + d) x₀ := by
  rcases x with n | i
  · exact ⟨.const n, rfl⟩
  rcases Nat.lt_trichotomy i (c + d) with hi | rfl | hi
  · exact ⟨.var i, by simp [PiCalculus.liftName, Nat.not_le.mpr hi]⟩
  · exact absurd (by simp [freeNameAt, Nat.not_lt.mpr (Nat.le_add_left d c)]) h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hi
    exact ⟨.var (c + d + k), by simp [PiCalculus.liftName]⟩

/-- A process in which the variable `c` is not free under `d` binders is a lift at
`c + d`. -/
private theorem Proc.exists_eq_liftAt_add {c : ℕ} (p : Proc Atom) :
    ∀ {d : ℕ}, PiCalculus.Name.var c ∉ p.freeNamesAt d →
      ∃ p₀ : Proc Atom, p = p₀.liftAt (c + d) := by
  induction p with
  | link x y =>
    intro d h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨⟨x₀, rfl⟩, ⟨y₀, rfl⟩⟩ := And.imp exists_eq_liftName_add exists_eq_liftName_add h
    exact ⟨.link x₀ y₀, rfl⟩
  | cut a p q ihp ihq =>
    intro d h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨⟨p₀, rfl⟩, ⟨q₀, rfl⟩⟩ := And.imp ihp ihq h
    exact ⟨.cut a p₀ q₀, rfl⟩
  | output x p q ihp ihq =>
    intro d h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨⟨⟨x₀, rfl⟩, ⟨p₀, rfl⟩⟩, ⟨q₀, rfl⟩⟩ :=
      And.imp (And.imp exists_eq_liftName_add ihp) ihq h
    exact ⟨.output x₀ p₀ q₀, rfl⟩
  | input x p ih =>
    intro d h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨⟨x₀, rfl⟩, ⟨p₀, rfl⟩⟩ := And.imp exists_eq_liftName_add ih h
    exact ⟨.input x₀ p₀, rfl⟩
  | selectLeft x p ih =>
    intro d h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨⟨x₀, rfl⟩, ⟨p₀, rfl⟩⟩ := And.imp exists_eq_liftName_add ih h
    exact ⟨.selectLeft x₀ p₀, rfl⟩
  | selectRight x p ih =>
    intro d h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨⟨x₀, rfl⟩, ⟨p₀, rfl⟩⟩ := And.imp exists_eq_liftName_add ih h
    exact ⟨.selectRight x₀ p₀, rfl⟩
  | choice x p q ihp ihq =>
    intro d h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨⟨⟨x₀, rfl⟩, ⟨p₀, rfl⟩⟩, ⟨q₀, rfl⟩⟩ :=
      And.imp (And.imp exists_eq_liftName_add ihp) ihq h
    exact ⟨.choice x₀ p₀ q₀, rfl⟩
  | emptyOutput x =>
    intro d h
    obtain ⟨x₀, rfl⟩ := exists_eq_liftName_add h
    exact ⟨.emptyOutput x₀, rfl⟩
  | emptyInput x p ih =>
    intro d h
    simp only [Proc.freeNamesAt, Finset.mem_union, not_or] at h
    obtain ⟨⟨x₀, rfl⟩, ⟨p₀, rfl⟩⟩ := And.imp exists_eq_liftName_add ih h
    exact ⟨.emptyInput x₀ p₀, rfl⟩
  | emptyChoice x =>
    intro d h
    obtain ⟨x₀, rfl⟩ := exists_eq_liftName_add h
    exact ⟨.emptyChoice x₀, rfl⟩

/-- In a well-typed cut premise, the continuation of an empty input on the cut channel is a lift
at zero, so it does not use that channel. -/
private theorem HasType.exists_liftAt_of_emptyInput_var_zero {C : Context Atom}
    {a : Logic.CLL.Proposition Atom} {r : Proc Atom}
    (h : HasType (C.lift.insert (.var 0) a) (.emptyInput (.var 0) r)) :
    ∃ r₀ : Proc Atom, r = r₀.liftAt 0 := by
  obtain ⟨Δ, -, hr, h0⟩ := h.emptyInput_premise
  exact Proc.exists_eq_liftAt_add (c := 0) r (d := 0) fun hm =>
    h0 (Finmap.mem_keys.mp (hr.freeNames_subset_keys hm))

/-- The channel on which a process acts first, if it is an action. -/
private def Proc.subject : Proc Atom → Option PiCalculus.Name
  | .output x _ _ | .input x _ | .selectLeft x _ | .selectRight x _ | .choice x _ _
  | .emptyOutput x | .emptyInput x _ | .emptyChoice x => some x
  | .link _ _ | .cut _ _ _ => none

/-- The proposition an action assigns to its subject has the connective of that action:
`⊗` for an output, `⅋` for an input, `⊕` for a selection, `&` for a choice, and `1`, `⊥`
and `⊤` for the empty actions. -/
private inductive Proc.SubjectType : Proc Atom → Logic.CLL.Proposition Atom → Prop
  | output {x : PiCalculus.Name} {p q : Proc Atom} {a b : Logic.CLL.Proposition Atom} :
      Proc.SubjectType (.output x p q) (.tensor a b)
  | input {x : PiCalculus.Name} {p : Proc Atom} {a b : Logic.CLL.Proposition Atom} :
      Proc.SubjectType (.input x p) (.parr a b)
  | selectLeft {x : PiCalculus.Name} {p : Proc Atom} {a b : Logic.CLL.Proposition Atom} :
      Proc.SubjectType (.selectLeft x p) (.oplus a b)
  | selectRight {x : PiCalculus.Name} {p : Proc Atom} {a b : Logic.CLL.Proposition Atom} :
      Proc.SubjectType (.selectRight x p) (.oplus a b)
  | choice {x : PiCalculus.Name} {p q : Proc Atom} {a b : Logic.CLL.Proposition Atom} :
      Proc.SubjectType (.choice x p q) (.with a b)
  | emptyOutput {x : PiCalculus.Name} : Proc.SubjectType (.emptyOutput x) .one
  | emptyInput {x : PiCalculus.Name} {p : Proc Atom} : Proc.SubjectType (.emptyInput x p) .bot
  | emptyChoice {x : PiCalculus.Name} : Proc.SubjectType (.emptyChoice x) .top

/-- A typed action finds its subject in its environment, at a proposition with the matching
connective. -/
private theorem HasType.subjectType_of_subject {C : Context Atom} {p : Proc Atom}
    (h : HasType C p) {x : PiCalculus.Name} (hx : p.subject = some x) :
    ∃ t, C.lookup x = some t ∧ p.SubjectType t := by
  cases h
  case ax | cut => cases hx
  all_goals
    cases hx
    exact ⟨_, Finmap.lookup_insert _, by constructor⟩

/-- The subject of a typed action is in its environment. -/
private theorem HasType.subject_mem {C : Context Atom} {p : Proc Atom} (h : HasType C p)
    {x : PiCalculus.Name} (hx : p.subject = some x) : x ∈ C := by
  obtain ⟨t, ht, -⟩ := h.subjectType_of_subject hx
  exact Finmap.mem_iff.mpr ⟨t, ht⟩

/-- In a cut premise, a channel other than the cut channel is the lift of an outer
channel. -/
private theorem exists_eq_liftName_of_mem_premise {G : Context Atom}
    {a : Logic.CLL.Proposition Atom} {y : PiCalculus.Name}
    (hy : y ∈ G.lift.insert (.var 0) a) (hne : y ≠ .var 0) :
    ∃ x, y = PiCalculus.liftName 0 x := by
  rcases Finmap.mem_insert.mp hy with rfl | hy
  · exact absurd rfl hne
  · obtain ⟨x, -, rfl⟩ := mem_lift.mp hy
    exact ⟨x, rfl⟩

/-- A typed process that is not a cut has a channel in its environment. -/
private theorem HasType.exists_mem_of_not_isCut {C : Context Atom} {q : Proc Atom}
    (h : HasType C q) (hq : ¬ q.IsCut) : ∃ k, k ∈ C := by
  cases hs : q.subject with
  | some y => exact ⟨y, h.subject_mem hs⟩
  | none =>
    cases q with
    | link w x =>
      obtain ⟨b, -, rfl⟩ := h.link_context
      exact ⟨x, Finmap.mem_insert.mpr (Or.inl rfl)⟩
    | cut b q₁ q₂ => exact absurd ⟨b, q₁, q₂, rfl⟩ hq
    | _ => cases hs

/-- A typed cut whose first component is not a cut and does not act on the cut channel
takes a step: an axiom cut when that component is a link, and a commuting conversion when
it acts on another channel. -/
private theorem HasType.cut_reducible_of_left {Γ : Context Atom}
    {a : Logic.CLL.Proposition Atom} {p q : Proc Atom} (h : HasType Γ (.cut a p q))
    (hp : ¬ p.IsCut) (hsub : p.subject ≠ some (.var 0)) : ∃ r, Step (.cut a p q) r := by
  obtain ⟨G, R, -, hpG, -, -⟩ := h.cut_premises
  have h0 : PiCalculus.Name.var 0 ∈ G.lift.insert (.var 0) a :=
    Finmap.mem_insert.mpr (Or.inl rfl)
  cases hs : p.subject with
  | none =>
    cases p with
    | cut b p₁ p₂ => exact absurd ⟨b, p₁, p₂, rfl⟩ hp
    | link w z =>
      obtain ⟨b, hwz, he⟩ := hpG.link_context
      have hw : w ∈ G.lift.insert (.var 0) a := by
        rw [he]
        exact Finmap.mem_insert.mpr (Or.inr (Finmap.mem_insert.mpr (Or.inl rfl)))
      have hz : z ∈ G.lift.insert (.var 0) a := by
        rw [he]
        exact Finmap.mem_insert.mpr (Or.inl rfl)
      rw [he, Finmap.mem_insert, Finmap.mem_insert] at h0
      rcases h0 with rfl | rfl | h0
      · obtain ⟨w₀, rfl⟩ := exists_eq_liftName_of_mem_premise hw hwz
        exact ⟨_, Step.axCut a w₀ q⟩
      · obtain ⟨z₀, rfl⟩ := exists_eq_liftName_of_mem_premise hz hwz.symm
        exact ⟨_, Step.axCutSymm a z₀ q⟩
      · exact absurd h0 Finmap.notMem_empty
    | _ => cases hs
  | some y =>
    have hne : y ≠ .var 0 := fun e => hsub (e ▸ hs)
    obtain ⟨x, rfl⟩ := exists_eq_liftName_of_mem_premise (hpG.subject_mem hs) hne
    cases p with
    | link w z => cases hs
    | cut b p₁ p₂ => cases hs
    | output y p₁ p₂ =>
      cases hs
      exact Step.commTensor_of_hasType h
    | input y p₁ =>
      cases hs
      exact ⟨_, Step.commParr a x p₁ q⟩
    | selectLeft y p₁ =>
      cases hs
      exact ⟨_, Step.commSelectLeft a x p₁ q⟩
    | selectRight y p₁ =>
      cases hs
      exact ⟨_, Step.commSelectRight a x p₁ q⟩
    | choice y p₁ p₂ =>
      cases hs
      exact ⟨_, Step.commChoice a x p₁ p₂ q⟩
    | emptyOutput y =>
      cases hs
      rw [hpG.emptyOutput_context, Finmap.mem_insert] at h0
      rcases h0 with h0 | h0
      · exact absurd h0.symm hne
      · exact absurd h0 Finmap.notMem_empty
    | emptyInput y p₁ =>
      cases hs
      exact ⟨_, Step.commBot a x p₁ q⟩
    | emptyChoice y =>
      cases hs
      exact ⟨_, Step.commTop a x q⟩

/-- A typed cut whose two components both act on the cut channel takes a principal step,
after cut symmetry when the dual connective comes first. -/
private theorem HasType.cut_reducible_principal {Γ : Context Atom}
    {a : Logic.CLL.Proposition Atom} {p q : Proc Atom} (h : HasType Γ (.cut a p q))
    (hp : p.subject = some (.var 0)) (hq : q.subject = some (.var 0)) :
    ∃ r, Step (.cut a p q) r := by
  obtain ⟨G, R, -, hpG, hqR, -⟩ := h.cut_premises
  obtain ⟨s, hs, tp⟩ := hpG.subjectType_of_subject hp
  obtain ⟨t, ht, tq⟩ := hqR.subjectType_of_subject hq
  rw [Finmap.lookup_insert, Option.some.injEq] at hs ht
  subst hs ht
  cases tp <;> simp only [Proc.subject, Option.some.injEq] at hp <;> subst hp <;>
    simp only [Logic.CLL.Proposition.dual] at tq <;> cases tq <;>
    simp only [Proc.subject, Option.some.injEq] at hq <;> subst hq
  · exact ⟨_, Step.tensorParr _ _ _ _ _⟩
  · exact ⟨_, Step.cong (Cong.swap _ _ _) (Step.tensorParr _ _ _ _ _) (Cong.refl _)⟩
  · exact ⟨_, Step.oplusWithLeft _ _ _ _ _⟩
  · exact ⟨_, Step.oplusWithRight _ _ _ _ _⟩
  · exact ⟨_, Step.cong (Cong.swap _ _ _) (Step.oplusWithLeft _ _ _ _ _) (Cong.refl _)⟩
  · exact ⟨_, Step.cong (Cong.swap _ _ _) (Step.oplusWithRight _ _ _ _ _) (Cong.refl _)⟩
  · obtain ⟨r₀, rfl⟩ := hqR.exists_liftAt_of_emptyInput_var_zero
    exact ⟨_, Step.oneBot r₀⟩
  · obtain ⟨r₀, rfl⟩ := hpG.exists_liftAt_of_emptyInput_var_zero
    exact ⟨_, Step.cong (Cong.swap _ _ _) (Step.oneBot r₀) (Cong.refl _)⟩

/-- A typed cut neither of whose components is a cut takes a step. -/
private theorem HasType.cut_reducible_of_not_isCut {Γ : Context Atom}
    {a : Logic.CLL.Proposition Atom} {p q : Proc Atom} (h : HasType Γ (.cut a p q))
    (hp : ¬ p.IsCut) (hq : ¬ q.IsCut) : ∃ r, Step (.cut a p q) r := by
  by_cases h₁ : p.subject = some (.var 0)
  swap
  · exact h.cut_reducible_of_left hp h₁
  by_cases h₂ : q.subject = some (.var 0)
  · exact h.cut_reducible_principal h₁ h₂
  have hs : HasType Γ (.cut a.dual q p) := (Cong.hasType_iff (Cong.swap a p q)).mp h
  obtain ⟨r, hr⟩ := hs.cut_reducible_of_left hq h₂
  exact ⟨r, Step.cong (Cong.swap a p q) hr (Cong.refl r)⟩

/-- Progress: every typed cut takes a reduction step. -/
theorem HasType.reducible_of_isCut {Γ : Context Atom} {p : Proc Atom}
    (h : HasType Γ p) (hc : p.IsCut) : Relation.Reducible Step p := by
  induction p generalizing Γ with
  | cut a p q ihp ihq =>
    obtain ⟨G, R, -, hp, hq, -⟩ := h.cut_premises
    by_cases hqc : q.IsCut
    · obtain ⟨q', hq'⟩ := ihq hq hqc
      exact ⟨_, Step.cutRight a p hq'⟩
    by_cases hpc : p.IsCut
    · obtain ⟨p', hp'⟩ := ihp hp hpc
      exact ⟨_, Step.cutLeft a hp' q⟩
    exact h.cut_reducible_of_not_isCut hpc hqc
  | _ =>
    obtain ⟨_, _, _, he⟩ := hc
    cases he

/-- **Top-level cut elimination** (Wadler, Theorem 2): if `P ⊢ Γ`, then
`P ⟹* Q` for some `Q` that is not a cut. The cut propositions are
unrestricted. Not being a cut constrains only the outermost constructor:
`Q` may still contain cuts guarded by a prefix. -/
theorem HasType.exists_steps_not_cut {Γ : Context Atom} {p : Proc Atom}
    (h : HasType Γ p) : ∃ q, Steps p q ∧ ¬ ∃ a q₁ q₂, q = .cut a q₁ q₂ := by
  obtain ⟨q, hpq, hnf⟩ := (Step.terminating.apply p).normalizable
  exact ⟨q, hpq, fun hc => hnf ((h.preservation_steps hpq).reducible_of_isCut hc)⟩

/-- Every typed process reduces to a normal form of one-step reduction, and
that normal form is not a cut. -/
theorem HasType.exists_steps_normal {Γ : Context Atom} {p : Proc Atom}
    (h : HasType Γ p) : ∃ q, Steps p q ∧ Relation.Normal Step q ∧ ¬ q.IsCut := by
  obtain ⟨q, hpq, hnf⟩ := (Step.terminating.apply p).normalizable
  exact ⟨q, hpq, hnf, fun hc => hnf ((h.preservation_steps hpq).reducible_of_isCut hc)⟩

/-- A typed process is a normal form of one-step reduction exactly when it is
not a cut. -/
theorem HasType.normal_iff_not_isCut {Γ : Context Atom} {p : Proc Atom}
    (h : HasType Γ p) : Relation.Normal Step p ↔ ¬ p.IsCut := by
  refine ⟨fun hn hc => hn (h.reducible_of_isCut hc), ?_⟩
  rintro hc ⟨q, hq⟩
  exact hc hq.isCut

/-- No process is typed in the empty environment. -/
theorem not_hasType_empty (p : Proc Atom) : ¬ HasType (∅ : Context Atom) p := by
  intro h
  obtain ⟨q, hpq, hq⟩ := h.exists_steps_not_cut
  obtain ⟨k, hk⟩ := (h.preservation_steps hpq).exists_mem_of_not_isCut hq
  exact Finmap.notMem_empty hk

end Cslib.ClassicalProcesses
