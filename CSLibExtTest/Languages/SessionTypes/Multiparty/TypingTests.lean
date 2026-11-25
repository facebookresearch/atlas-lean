/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.SessionTypes.Multiparty.Typing

/-!
# Multiparty process typing tests

A communication typed by projections and its synchronous step (binding via
`recv`), a choice whose bystander's projection reorders branches (typing up
to brace equality, which ordered typing alone rejects), negative tests for a
wrong peer, a wrong sort, a free variable, an absent selected label and an
active non-participant, and de Bruijn substitution under a nested receive.
Tests that only unfold definitions are proved; tests that go through a
statement of `Multiparty.Typing` are proved by applying that statement.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.SessionTypes.Multiparty

namespace TypingTests

/-- Participants for examples. -/
inductive Role where
  | alice : Role
  | bob : Role
  | carol : Role
  | dave : Role
deriving DecidableEq

/-- Payload sorts for examples. -/
inductive Srt where
  | nat : Srt
  | bool : Srt
deriving DecidableEq

/-- Values for examples. -/
inductive Val where
  | num (n : Nat) : Val
  | flag (b : Bool) : Val
deriving DecidableEq

/-- Choice labels for examples. -/
inductive Lbl where
  | ok : Lbl
  | quit : Lbl
  | x : Lbl
  | y : Lbl
deriving DecidableEq

/-- The sort of a value. -/
def sortOf : Val → Srt
  | .num _ => .nat
  | .flag _ => .bool

/-! ### 1. A communication: typing by projections and a synchronous step -/

/-- `alice → bob : ⟨nat⟩. bob → carol : {ok : bob → carol : ⟨nat⟩. end, quit : end}`. -/
def g1 : GlobalType Role Srt Lbl :=
  .msg .alice .bob .nat
    (.choice .bob .carol
      (.cons .ok (.msg .bob .carol .nat .end) (.cons .quit .end .nil)))

/-- A network implementing `g1`; `bob` forwards the received value. -/
def n1 : Net Role Val Lbl
  | .alice => .send .bob (.val (.num 5)) .inact
  | .bob => .recv .alice (.select .carol .ok (.send .carol (.var 0) .inact))
  | .carol => .branch .bob (.cons .ok (.recv .bob .inact) (.cons .quit .inact .nil))
  | .dave => .inact

/-- `n1` after `alice` sends `5` to `bob`. -/
def n1' : Net Role Val Lbl
  | .alice => .inact
  | .bob => .select .carol .ok (.send .carol (.val (.num 5)) .inact)
  | .carol => .branch .bob (.cons .ok (.recv .bob .inact) (.cons .quit .inact .nil))
  | .dave => .inact

theorem g1_wellFormed : g1.WellFormed := by decide

theorem n1_typedBy : Net.TypedBy sortOf g1 n1 := by
  refine ⟨g1_wellFormed, fun peer => ?_⟩
  cases peer
  · refine ⟨.send .bob .nat .end, by decide, _, ?_, LocalType.braceEq_refl _⟩
    exact .send (.val rfl) .inact
  · refine ⟨.recv .alice .nat (.select .carol
        (.cons .ok (.send .carol .nat .end) (.cons .quit .end .nil))), by decide,
      _, ?_, LocalType.braceEq_refl _⟩
    exact .recv (.select (by decide) (.send (.var rfl) .inact)
      (.cons (by decide) (.send .end) (.cons (by decide) .end .nil)))
  · refine ⟨.branch .bob (.cons .ok (.recv .bob .nat .end) (.cons .quit .end .nil)),
      by decide, _, ?_, LocalType.braceEq_refl _⟩
    exact .branch (.cons (.recv .inact) (.cons .inact .nil (by decide)) (by decide))
  · exact ⟨.end, by decide, _, .inact, LocalType.braceEq_refl _⟩

theorem n1_step : Net.Step sortOf n1 (.msg .alice .bob .nat) n1' := by
  have e : n1' = Function.update (Function.update n1 .alice .inact) .bob
      ((Proc.select .carol .ok (Proc.send .carol (.var 0) .inact)).subst (Val.num 5) 0) := by
    funext peer
    cases peer <;> rfl
  rw [e]
  exact Net.Step.msg (sender := Role.alice) (receiver := Role.bob) (value := Val.num 5)
    (by decide) rfl rfl

/-- The stepped receiver is typed by `bob`'s continuation, via substitution
(T2′). -/
theorem n1'_bob_hasType : HasType sortOf [] (n1' .bob)
    (.select .carol (.cons .ok (.send .carol .nat .end) (.cons .quit .end .nil))) :=
  HasType.subst_zero (s := Srt.nat) (value := Val.num 5)
    (proc := (Proc.select Role.carol Lbl.ok (.send Role.carol (.var 0) .inact) :
      Proc Role Val Lbl))
    (.of_hasType0 (.select (t := LocalType.send Role.carol Srt.nat .end) (by decide)
      (.send (.var rfl) .inact)
      (.cons (by decide) (.send .end) (.cons (by decide) .end .nil)))) rfl

/-! ### 2. Reordered bystander branches: typing up to brace equality -/

/-- `alice` chooses with `bob`, then picks for `carol` with branches listed in
opposite orders; `carol`'s projection is the first branch's (plain merging). -/
def g2 : GlobalType Role Srt Lbl :=
  .choice .alice .bob
    (.cons .ok (.choice .alice .carol (.cons .x .end (.cons .y .end .nil)))
      (.cons .quit (.choice .alice .carol (.cons .y .end (.cons .x .end .nil))) .nil))

/-- `carol`'s process lists its branches as in the `quit` arm. -/
def carol2 : Proc Role Val Lbl :=
  .branch .alice (.cons .y .inact (.cons .x .inact .nil))

/-- A network implementing `g2`. -/
def n2 : Net Role Val Lbl
  | .alice => .select .bob .ok (.select .carol .x .inact)
  | .bob => .branch .alice (.cons .ok .inact (.cons .quit .inact .nil))
  | .carol => carol2
  | .dave => .inact

theorem g2_wellFormed : g2.WellFormed := by decide

theorem g2_project_carol :
    g2.project .carol = some (.branch .alice (.cons .x .end (.cons .y .end .nil))) := by
  decide

/-- Ordered typing alone rejects `carol2` against its projection. -/
theorem carol2_not_hasType0 :
    ¬ HasType0 sortOf [] carol2 (.branch .alice (.cons .x .end (.cons .y .end .nil))) := by
  intro h
  cases h with
  | branch hbs => cases hbs

/-- Typing up to brace equality accepts it (T5 on data). -/
theorem carol2_hasType :
    HasType sortOf [] carol2 (.branch .alice (.cons .x .end (.cons .y .end .nil))) :=
  HasType.braceEq (t := .branch .alice (.cons .y .end (.cons .x .end .nil)))
    (.of_hasType0 (.branch (.cons .inact (.cons .inact .nil (by decide)) (by decide))))
    (by decide)

theorem n2_typedBy : Net.TypedBy sortOf g2 n2 := by
  refine ⟨g2_wellFormed, fun peer => ?_⟩
  cases peer
  · refine ⟨.select .bob
        (.cons .ok (.select .carol (.cons .x .end (.cons .y .end .nil)))
          (.cons .quit (.select .carol (.cons .y .end (.cons .x .end .nil))) .nil)),
      by decide, _, ?_, LocalType.braceEq_refl _⟩
    exact .select (t := .select .carol (.cons .x .end (.cons .y .end .nil))) (by decide)
      (.select (t := .end) (by decide) .inact
        (.cons (by decide) .end (.cons (by decide) .end .nil)))
      (.cons (by decide) (.select (.cons (by decide) .end (.cons (by decide) .end .nil)))
        (.cons (by decide) (.select (.cons (by decide) .end (.cons (by decide) .end .nil)))
          .nil))
  · refine ⟨.branch .alice (.cons .ok .end (.cons .quit .end .nil)), by decide,
      _, ?_, LocalType.braceEq_refl _⟩
    exact .branch (.cons .inact (.cons .inact .nil (by decide)) (by decide))
  · exact ⟨.branch .alice (.cons .x .end (.cons .y .end .nil)), g2_project_carol,
      .branch .alice (.cons .y .end (.cons .x .end .nil)),
      .branch (.cons .inact (.cons .inact .nil (by decide)) (by decide)), by decide⟩
  · exact ⟨.end, by decide, _, .inact, LocalType.braceEq_refl _⟩

theorem n2_can_choose :
    ∃ n2' : Net Role Val Lbl, Net.Step sortOf n2 (.choice .alice .bob .ok) n2' :=
  ⟨_, Net.Step.choice (cont := .inact) (by decide) rfl rfl (by decide)⟩

/-! ### 3-7. Negative and edge cases -/

/-- 3. Wrong peer. -/
theorem wrong_peer :
    ¬ HasType sortOf [] (.send .carol (.val (.num 1)) .inact : Proc Role Val Lbl)
      (.send .bob .nat .end) := by
  intro h
  obtain ⟨s, t', heq, -⟩ := h.send_inv
  cases heq

/-- 4. Wrong sort. -/
theorem wrong_sort :
    ¬ HasType sortOf [] (.send .bob (.val (.flag true)) .inact : Proc Role Val Lbl)
      (.send .bob .nat .end) := by
  intro h
  obtain ⟨s, t', heq, hs, -⟩ := h.send_inv
  cases heq
  cases hs with
  | val hv => exact absurd hv (by decide)

/-- 5. A free variable is untypable in the empty context, for every type. -/
theorem free_var_untypable (t : LocalType Role Srt Lbl) :
    ¬ HasType sortOf [] (.send .bob (.var 0) .inact : Proc Role Val Lbl) t := by
  intro h
  obtain ⟨s, t', -, hs, -⟩ := h.send_inv
  cases hs with
  | var hv => simp at hv

/-- 5. The same process is typable once the variable is bound. -/
theorem bound_var_hasType :
    HasType sortOf [.nat] (.send .bob (.var 0) .inact : Proc Role Val Lbl)
      (.send .bob .nat .end) :=
  ⟨_, .send (.var rfl) .inact, LocalType.braceEq_refl _⟩

/-- 6. An active non-participant breaks typing by projections. -/
theorem active_nonparticipant :
    ¬ Net.TypedBy sortOf g1 (Function.update n1 .dave (.send .alice (.val (.num 0)) .inact)) := by
  intro h
  have hd := h.inact_of_not_mem (peer := .dave) (by decide)
  simp at hd

/-- 7. Selecting a label the type does not offer is untypable. -/
theorem select_absent_label :
    ¬ HasType sortOf [] (.select .bob .quit .inact : Proc Role Val Lbl)
      (.select .bob (.cons .ok .end .nil)) := by
  intro h
  obtain ⟨bs, u, heq, hl, -⟩ := h.select_inv
  cases heq
  simp [LocalType.Branches.lookup] at hl

/-- 8. Repeated branch labels are not process syntax: a branch with a
duplicated label is untypable against every local type. -/
theorem dup_label_branch_untypable (t : LocalType Role Srt Lbl) :
    ¬ HasType sortOf []
      (.branch .alice (.cons .x .inact (.cons .x .inact .nil)) : Proc Role Val Lbl) t := by
  rintro ⟨t₀, h, -⟩
  cases h with
  | branch hbs =>
    cases hbs with
    | cons _ _ hfresh => exact hfresh (by decide)

/-- 9. A selection is untypable against a local selection type with a
repeated label, whatever the process: ordered typing requires a well-formed
branch list, and brace equality from a well-formed list never reaches one
with a repeated label. -/
theorem select_duplicate_type_label_untypable (proc : Proc Role Val Lbl) :
    ¬ HasType sortOf [] proc
      (.select .bob (.cons .ok .end (.cons .ok (.send .bob .nat .end) .nil))) := by
  rintro ⟨t₀, h, hb⟩
  cases h <;> simp only [LocalType.braceEq, Bool.false_eq_true] at hb
  rename_i hwf _
  simp only [Bool.and_eq_true] at hb
  cases hwf with
  | nil => simp [LocalType.Branches.braceEq] at hb
  | cons hnotin _ _ =>
    rename_i l _ tl _ _ _
    by_cases hl : l = Lbl.ok
    · subst hl
      cases tl with
      | nil =>
        simp [LocalType.Branches.braceEq, LocalType.Branches.lookup,
          LocalType.Branches.eraseLabel] at hb
      | cons l' _ _ =>
        by_cases hl' : l' = Lbl.ok
        · subst hl'
          simp [LocalType.Branches.labels, LocalType.Branches.entries] at hnotin
        · simp [LocalType.Branches.braceEq, LocalType.Branches.lookup,
            LocalType.Branches.eraseLabel, hl'] at hb
    · simp [LocalType.Branches.braceEq, LocalType.Branches.lookup, hl] at hb

/-! ### Binding -/

/-- Substitution under a nested receive replaces only the outer variable. -/
theorem subst_nested_recv :
    (Proc.recv .alice (.send .carol (.var 1) (.send .carol (.var 0) .inact)) :
      Proc Role Val Lbl).subst (.num 7) 0 =
    .recv .alice (.send .carol (.val (.num 7)) (.send .carol (.var 0) .inact)) := by
  decide

/-- Lifting skips variables bound below the cutoff. -/
theorem lift_skips_bound :
    (Proc.recv .alice (.send .carol (.var 0) (.send .carol (.var 1) .inact)) :
      Proc Role Val Lbl).lift 0 =
    .recv .alice (.send .carol (.var 0) (.send .carol (.var 2) .inact)) := by
  decide

end TypingTests

end Cslib.SessionTypes.Multiparty
