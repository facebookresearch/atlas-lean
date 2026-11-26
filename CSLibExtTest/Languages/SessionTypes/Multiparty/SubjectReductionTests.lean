/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.SessionTypes.Multiparty.SubjectReduction

/-!
# Multiparty subject reduction and session fidelity tests

Local fixtures only. Subject reduction on a message step; projection
completeness at a matched pair; a two-step trace; a non-participant that
stays inert after every step; one-step fidelity on a choice whose bystander
lists its branches in another order; fidelity and subject reduction for a
step under a choice prefix (congruence) with third-party merging of
reordered branches; the converse of fidelity failing for a typed network;
and a well-formed global type showing that the sender's projection alone
does not give a global step. Tests that go through a statement of
`Multiparty.SubjectReduction` are proved by applying that statement; every
other fact is proved directly.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.SessionTypes.Multiparty

namespace SubjectReductionTests

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

/-! ### 1. Subject reduction on a message step -/

/-- `alice → bob : ⟨nat⟩. bob → carol : {ok : bob → carol : ⟨nat⟩. end, quit : end}`;
`dave` does not participate. -/
def g1 : GlobalType Role Srt Lbl :=
  .msg .alice .bob .nat
    (.choice .bob .carol
      (.cons .ok (.msg .bob .carol .nat .end) (.cons .quit .end .nil)))

/-- `g1` after its first message. -/
def g1' : GlobalType Role Srt Lbl :=
  .choice .bob .carol (.cons .ok (.msg .bob .carol .nat .end) (.cons .quit .end .nil))

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

theorem g1_step : g1.Step (.msg .alice .bob .nat) g1' := .msg

/-- Projection completeness for a message, on `g1`. -/
theorem g1_step_of_project : ∃ G', g1.Step (.msg .alice .bob .nat) G' :=
  GlobalType.step_of_project_send_recv (t := .end)
    (u := .select .carol (.cons .ok (.send .carol .nat .end) (.cons .quit .end .nil)))
    (s' := .nat) (by decide) (by decide)

/-- Subject reduction: the stepped network is typed by the stepped global type. -/
theorem n1'_typedBy : Net.TypedBy sortOf g1' n1' :=
  Net.TypedBy.step_of_global n1_typedBy n1_step g1_step

/-! ### 2. A non-participant stays inert -/

/-- After the message step, typing by the stepped global type keeps `dave` inert. -/
theorem n1'_dave_inact : n1' .dave = .inact :=
  n1'_typedBy.inact_of_not_mem (by decide)

/-- After every step of the typed network `n1`, the non-participant `dave` is
still `inact`. -/
theorem n1_step_dave_inact {ℓ : GlobalType.Label Role Srt Lbl}
    {net' : Net Role Val Lbl} (h : Net.Step sortOf n1 ℓ net') : net' .dave = .inact := by
  obtain ⟨G', hG, hT⟩ := Net.TypedBy.step n1_typedBy h
  obtain ⟨-, hper⟩ := GlobalType.project_step_sound g1_wellFormed hG
  obtain ⟨t, t', ht, ht', hS, hR, hB⟩ := hper .dave
  have hd : g1.project .dave = some .end := by decide
  rw [hd, Option.some.injEq] at ht
  subst ht
  have hs : Role.dave ≠ ℓ.sender := fun e => nomatch hS e
  have hr : Role.dave ≠ ℓ.receiver := fun e => nomatch hR e
  have hbe := hB hs hr
  have hend : t' = .end := by
    cases t' <;> simp_all [LocalType.braceEq]
  obtain ⟨t'', hp, hty⟩ := hT.2 .dave
  rw [ht', Option.some.injEq] at hp
  subst hp hend
  exact hty.eq_inact_of_end

/-! ### 3. A two-step trace -/

/-- `n1'` after `bob` selects `ok` with `carol`. -/
def n1'' : Net Role Val Lbl
  | .alice => .inact
  | .bob => .send .carol (.val (.num 5)) .inact
  | .carol => .recv .bob .inact
  | .dave => .inact

theorem n1'_step : Net.Step sortOf n1' (.choice .bob .carol .ok) n1'' := by
  have e : n1'' = Function.update
      (Function.update n1' .bob (Proc.send .carol (.val (.num 5)) .inact)) .carol
      (Proc.recv .bob .inact) := by
    funext peer
    cases peer <;> rfl
  rw [e]
  exact Net.Step.choice (by decide) rfl rfl (by decide)

/-- The two-step trace of `n1`, in the network LTS. -/
theorem n1_trace :
    (Net.lts sortOf).MTr n1 [.msg .alice .bob .nat, .choice .bob .carol .ok] n1'' :=
  .stepL n1_step (.stepL n1'_step .refl)

/-- Trace fidelity: the trace is a trace of `g1`, ending at a global type that
types `n1''`. -/
theorem n1_trace_fidelity :
    ∃ G', GlobalType.lts.MTr g1 [.msg .alice .bob .nat, .choice .bob .carol .ok] G' ∧
      Net.TypedBy sortOf G' n1'' :=
  Net.TypedBy.mtr n1_typedBy n1_trace

/-! ### 4. One-step fidelity with a reordered bystander -/

/-- `alice` chooses with `bob`, then picks for `carol` with branches listed in
opposite orders; `carol`'s projection is the first branch's (plain merging). -/
def g2 : GlobalType Role Srt Lbl :=
  .choice .alice .bob
    (.cons .ok (.choice .alice .carol (.cons .x .end (.cons .y .end .nil)))
      (.cons .quit (.choice .alice .carol (.cons .y .end (.cons .x .end .nil))) .nil))

/-- A network implementing `g2`; `carol` lists its branches as in the `quit` arm. -/
def n2 : Net Role Val Lbl
  | .alice => .select .bob .ok (.select .carol .x .inact)
  | .bob => .branch .alice (.cons .ok .inact (.cons .quit .inact .nil))
  | .carol => .branch .alice (.cons .y .inact (.cons .x .inact .nil))
  | .dave => .inact

/-- `n2` after `alice` selects `ok` with `bob`. -/
def n2' : Net Role Val Lbl
  | .alice => .select .carol .x .inact
  | .bob => .inact
  | .carol => .branch .alice (.cons .y .inact (.cons .x .inact .nil))
  | .dave => .inact

theorem g2_wellFormed : g2.WellFormed := by decide

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
  · exact ⟨.branch .alice (.cons .x .end (.cons .y .end .nil)), by decide,
      .branch .alice (.cons .y .end (.cons .x .end .nil)),
      .branch (.cons .inact (.cons .inact .nil (by decide)) (by decide)), by decide⟩
  · exact ⟨.end, by decide, _, .inact, LocalType.braceEq_refl _⟩

theorem n2_step : Net.Step sortOf n2 (.choice .alice .bob .ok) n2' := by
  have e : n2' = Function.update
      (Function.update n2 .alice (Proc.select .carol .x .inact)) .bob Proc.inact := by
    funext peer
    cases peer <;> rfl
  rw [e]
  exact Net.Step.choice (by decide) rfl rfl (by decide)

/-- Fidelity: the choice step of `n2` is a step of `g2` whose target types `n2'`,
although `carol`'s process orders its branches differently from its projection. -/
theorem n2_fidelity :
    ∃ G', g2.Step (.choice .alice .bob .ok) G' ∧ Net.TypedBy sortOf G' n2' :=
  Net.TypedBy.step n2_typedBy n2_step

/-! ### 5. A step under a choice prefix (congruence) -/

/-- `alice → bob {ok : carol → dave {x, y}, quit : carol → dave {y, x}}`: the
inner choice is independent of the outer one, and its third-party projections
merge reordered branches. -/
def g4 : GlobalType Role Srt Lbl :=
  .choice .alice .bob
    (.cons .ok (.choice .carol .dave (.cons .x .end (.cons .y .end .nil)))
      (.cons .quit (.choice .carol .dave (.cons .y .end (.cons .x .end .nil))) .nil))

/-- `g4` after the inner choice of `x`, taken under the outer prefix. -/
def g4' : GlobalType Role Srt Lbl :=
  .choice .alice .bob (.cons .ok .end (.cons .quit .end .nil))

/-- A network implementing `g4`; `dave` lists its branches as in the `quit` arm. -/
def n4 : Net Role Val Lbl
  | .alice => .select .bob .ok .inact
  | .bob => .branch .alice (.cons .ok .inact (.cons .quit .inact .nil))
  | .carol => .select .dave .x .inact
  | .dave => .branch .carol (.cons .y .inact (.cons .x .inact .nil))

/-- `n4` after `carol` selects `x` with `dave`. -/
def n4' : Net Role Val Lbl
  | .alice => .select .bob .ok .inact
  | .bob => .branch .alice (.cons .ok .inact (.cons .quit .inact .nil))
  | .carol => .inact
  | .dave => .inact

theorem g4_wellFormed : g4.WellFormed := by decide

theorem g4_project_carol :
    g4.project .carol = some (.select .dave (.cons .x .end (.cons .y .end .nil))) := by
  decide

theorem g4_project_dave :
    g4.project .dave = some (.branch .carol (.cons .x .end (.cons .y .end .nil))) := by
  decide

theorem n4_typedBy : Net.TypedBy sortOf g4 n4 := by
  refine ⟨g4_wellFormed, fun peer => ?_⟩
  cases peer
  · refine ⟨.select .bob (.cons .ok .end (.cons .quit .end .nil)), by decide,
      _, ?_, LocalType.braceEq_refl _⟩
    exact .select (t := .end) (by decide) .inact
      (.cons (by decide) .end (.cons (by decide) .end .nil))
  · refine ⟨.branch .alice (.cons .ok .end (.cons .quit .end .nil)), by decide,
      _, ?_, LocalType.braceEq_refl _⟩
    exact .branch (.cons .inact (.cons .inact .nil (by decide)) (by decide))
  · refine ⟨.select .dave (.cons .x .end (.cons .y .end .nil)), g4_project_carol,
      _, ?_, LocalType.braceEq_refl _⟩
    exact .select (t := .end) (by decide) .inact
      (.cons (by decide) .end (.cons (by decide) .end .nil))
  · exact ⟨.branch .carol (.cons .x .end (.cons .y .end .nil)), g4_project_dave,
      .branch .carol (.cons .y .end (.cons .x .end .nil)),
      .branch (.cons .inact (.cons .inact .nil (by decide)) (by decide)), by decide⟩

theorem n4_step : Net.Step sortOf n4 (.choice .carol .dave .x) n4' := by
  have e : n4' = Function.update
      (Function.update n4 .carol Proc.inact) .dave Proc.inact := by
    funext peer
    cases peer <;> rfl
  rw [e]
  exact Net.Step.choice (by decide) rfl rfl (by decide)

/-- The global step is a choice-congruence step: every branch steps. -/
theorem g4_step : g4.Step (.choice .carol .dave .x) g4' :=
  .choiceCongr (.cons (.choice (by decide)) (.cons (.choice (by decide)) .nil))
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Projection completeness for a choice, under the congruence prefix. -/
theorem g4_step_of_project : ∃ G', g4.Step (.choice .carol .dave .x) G' :=
  GlobalType.step_of_project_select_branch g4_project_carol (by decide) g4_project_dave

/-- Fidelity for the congruence step. -/
theorem n4_fidelity :
    ∃ G', g4.Step (.choice .carol .dave .x) G' ∧ Net.TypedBy sortOf G' n4' :=
  Net.TypedBy.step n4_typedBy n4_step

/-- Subject reduction for the congruence step. -/
theorem n4'_typedBy : Net.TypedBy sortOf g4' n4' :=
  Net.TypedBy.step_of_global n4_typedBy n4_step g4_step

/-! ### 6. The converse of fidelity fails -/

/-- `n2` is typed by `g2` and `g2` can step on `quit`, but `n2`, whose `alice`
selects `ok`, has no `quit` step. -/
theorem converse_fails :
    Net.TypedBy sortOf g2 n2 ∧ (∃ G', g2.Step (.choice .alice .bob .quit) G') ∧
      ¬ ∃ net' : Net Role Val Lbl, Net.Step sortOf n2 (.choice .alice .bob .quit) net' := by
  refine ⟨n2_typedBy,
    ⟨.choice .alice .carol (.cons .y .end (.cons .x .end .nil)), .choice (by decide)⟩, ?_⟩
  rintro ⟨net', h⟩
  cases h with
  | choice _ hs _ _ => simp [n2] at hs

/-! ### 7. The sender's projection alone does not give a step -/

/-- `alice → bob {ok : carol → bob {x : end}}`. -/
def g3 : GlobalType Role Srt Lbl :=
  .choice .alice .bob (.cons .ok (.choice .carol .bob (.cons .x .end .nil)) .nil)

theorem g3_wellFormed : g3.WellFormed := by decide

/-- `carol` projects to a selection of `x` towards `bob`. -/
theorem g3_project_carol :
    g3.project .carol = some (.select .bob (.cons .x .end .nil)) := by
  decide

/-- Yet `g3` has no `carol → bob : x` step: `bob` is the outer receiver. -/
theorem g3_no_step : ¬ ∃ G', g3.Step (.choice .carol .bob .x) G' := by
  rintro ⟨G', h⟩
  cases h with
  | choiceCongr _ _ _ _ _ h => exact h rfl

end SubjectReductionTests

end Cslib.SessionTypes.Multiparty
