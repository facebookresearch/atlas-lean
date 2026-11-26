/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.TypeSafety

/-!
# Tests for the type-safety schema

Statement pins restate the contract of every public declaration of
`CSLibExt.Languages.TypeSafety` and are closed by the declaration itself, so a weakened or
drifted statement fails here. Concrete checks: boundary cases on a toy semantics showing that
the progress and preservation hypotheses cannot be dropped, including the anchor corollary on
a reachable stuck configuration; a closed value of the locally nameless STLC that reduces under
its binder, so values are not terminal under full β-reduction and no anchor semantics has full
β-steps with values as final states, while the relation-level schema still applies; the
calculus with references on an allocating program, where the store typing must grow; closed
terms of the intrinsically typed STLC through the anchor; and both structural-typing instances
on examples, with negative checks that their fields have content. Tests that go through a
statement of `TypeSafety` are proved by applying that statement.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace Cslib.Languages.TypeSafetyTests

open Cslib.Languages.TypeSafety

/-! ### Statement pins -/

/-- Pin: the stuck form of the schema. -/
theorem not_stuck_of_reflTransGen_pin :
    ∀ {State : Type u} {Ty : Type v} (Step : State → State → Prop) (Final : State → Prop)
      (HasType : State → Ty → Prop),
      (∀ {s : State} {A : Ty}, HasType s A → Final s ∨ ∃ s', Step s s') →
      (∀ A : Ty, Relation.Preserves Step (HasType · A)) →
      ∀ {s s' : State} {A : Ty}, HasType s A → Relation.ReflTransGen Step s s' →
        ¬ (¬ Final s' ∧ Relation.Normal Step s') :=
  @not_stuck_of_reflTransGen

/-- Pin: the final-or-step form of the schema. -/
theorem final_or_step_of_reflTransGen_pin :
    ∀ {State : Type u} {Ty : Type v} (Step : State → State → Prop) (Final : State → Prop)
      (HasType : State → Ty → Prop),
      (∀ {s : State} {A : Ty}, HasType s A → Final s ∨ ∃ s', Step s s') →
      (∀ A : Ty, Relation.Preserves Step (HasType · A)) →
      ∀ {s s' : State} {A : Ty}, HasType s A → Relation.ReflTransGen Step s s' →
        Final s' ∨ ∃ s'', Step s' s'' :=
  @final_or_step_of_reflTransGen

/-- Pin: multi-step preservation with growing worlds. -/
theorem exists_ext_of_reflTransGen_pin :
    ∀ {State : Type u} {Ty : Type v} {W : Type w} (Step : State → State → Prop)
      (ext : W → W → Prop) [IsPreorder W ext] (HasType : W → State → Ty → Prop),
      (∀ {w : W} {s s' : State} {A : Ty},
        HasType w s A → Step s s' → ∃ w', ext w w' ∧ HasType w' s' A) →
      ∀ {w : W} {s s' : State} {A : Ty}, HasType w s A → Relation.ReflTransGen Step s s' →
        ∃ w', ext w w' ∧ HasType w' s' A :=
  @exists_ext_of_reflTransGen

/-- Pin: safety with growing worlds. -/
theorem final_or_step_of_reflTransGen_ext_pin :
    ∀ {State : Type u} {Ty : Type v} {W : Type w} (Step : State → State → Prop)
      (Final : State → Prop) (ext : W → W → Prop) [IsPreorder W ext]
      (HasType : W → State → Ty → Prop),
      (∀ {w : W} {s : State} {A : Ty}, HasType w s A → Final s ∨ ∃ s', Step s s') →
      (∀ {w : W} {s s' : State} {A : Ty},
        HasType w s A → Step s s' → ∃ w', ext w w' ∧ HasType w' s' A) →
      ∀ {w : W} {s s' : State} {A : Ty}, HasType w s A → Relation.ReflTransGen Step s s' →
        Final s' ∨ ∃ s'', Step s' s'' :=
  @final_or_step_of_reflTransGen_ext

/-- Pin: the corollary over the anchor. -/
theorem opSem_safe_of_progress_preservation_pin :
    ∀ {Config : Type u} {Label : Type v} {Ty : Type w}
      (S : OperationalSemantics.OpSem Config Label) (HasType : Config → Ty → Prop),
      (∀ {c : Config} {A : Ty}, HasType c A → S.Final c ∨ ∃ c', S.Step c c') →
      (∀ A : Ty, Relation.Preserves S.Step (HasType · A)) →
      ∀ {c : Config} {A : Ty}, HasType c A → S.Safe c :=
  @Cslib.Languages.TypeSafety.OpSem.safe_of_progress_preservation

section StructuralPins

variable {Ctx : Type u} {Tm : Type v} {Ty : Type w} {Name : Type z}
  {HasType : Ctx → Tm → Ty → Prop} {bind : Ctx → Name → Ty → Ctx}
  {inst : Tm → Name → Tm → Tm} {Extends : Ctx → Ctx → Prop} {wk : Ctx → Ctx → Tm → Tm}

/-- Pin: the substitution field. -/
theorem structuralTyping_subst_pin (h : StructuralTyping HasType bind inst Extends wk) :
    ∀ {Γ : Ctx} {x : Name} {A B : Ty} {e v : Tm},
      HasType (bind Γ x A) e B → HasType Γ v A → HasType Γ (inst e x v) B :=
  h.subst

/-- Pin: the weakening field. -/
theorem structuralTyping_weaken_pin (h : StructuralTyping HasType bind inst Extends wk) :
    ∀ {Γ Δ : Ctx} {t : Tm} {A : Ty},
      Extends Γ Δ → HasType Γ t A → HasType Δ (wk Γ Δ t) A :=
  h.weaken

/-- Pin: the two fields are all the interface asks for. -/
theorem structuralTyping_mk_pin
    (hsubst : ∀ {Γ : Ctx} {x : Name} {A B : Ty} {e v : Tm},
      HasType (bind Γ x A) e B → HasType Γ v A → HasType Γ (inst e x v) B)
    (hweaken : ∀ {Γ Δ : Ctx} {t : Tm} {A : Ty},
      Extends Γ Δ → HasType Γ t A → HasType Δ (wk Γ Δ t) A) :
    StructuralTyping HasType bind inst Extends wk :=
  ⟨hsubst, hweaken⟩

end StructuralPins

section LocallyNamelessPins

open Cslib.LambdaCalculus.LocallyNameless Cslib.LambdaCalculus.LocallyNameless.Stlc
  Cslib.LambdaCalculus.LocallyNameless.Untyped

/-- Pin: the locally nameless STLC instance of the structural interface, with its data. -/
theorem structuralTyping_lnStlc_pin {Var : Type u} {Base : Type v} [DecidableEq Var]
    [HasFresh Var] :
    StructuralTyping (Typing (Var := Var) (Base := Base))
      (fun Γ (x : Var) σ => ⟨x, σ⟩ :: Γ) (fun t (x : Var) s => t[x := s])
      (fun Γ Δ => ∃ Θ, (Γ ++ Θ).Perm Δ ∧ Δ✓) (fun _ _ t => t) :=
  structuralTyping_lnStlc

/-- Pin: full β-safety for the locally nameless STLC, at the level of relations. -/
theorem lnStlc_value_or_step_pin :
    ∀ {Var : Type u} {Base : Type v} [HasFresh Var] [DecidableEq Var]
      {t t' : Term Var} {τ : Ty Base},
      Typing [] t τ → Relation.ReflTransGen Term.FullBeta t t' →
        t'.Value ∨ ∃ t'', Term.FullBeta t' t'' :=
  @lnStlc_value_or_step

end LocallyNamelessPins

section ReferencesPins

open Cslib.Languages.LambdaCalculus.References

/-- Pin: the references instance of the structural interface, with its data. -/
theorem structuralTyping_references_pin {Base : Type u} :
    StructuralTyping (fun (c : List (Ty Base) × List (Ty Base)) t T => HasType c.1 c.2 t T)
      (fun c (_ : Unit) A => (A :: c.1, c.2)) (fun t (_ : Unit) s => t.instantiate s)
      (fun c d => (∃ Θ, d.1 = Θ ++ c.1) ∧ c.2 <+: d.2)
      (fun c d t => t.rename (· + (d.1.length - c.1.length))) :=
  structuralTyping_references

end ReferencesPins

/-- Pin: safety of closed terms of the intrinsically typed STLC through the anchor. -/
theorem stlc_safe_pin :
    ∀ {Base : Type u} {A : LambdaCalculus.Stlc.Ty Base}
      (t : LambdaCalculus.Stlc.Tm ([] : List (LambdaCalculus.Stlc.Ty Base)) A),
      (OperationalSemantics.stlc (Base := Base) (A := A)).Safe t :=
  @stlc_safe

/-! ### Boundary checks on a toy semantics -/

/-- Toy configurations: `start` steps to `blocked`, which is stuck; `done` is final. -/
inductive ToyCfg where
  | start : ToyCfg
  | blocked : ToyCfg
  | done : ToyCfg

/-- Toy semantics with the single transition from `start` to `blocked`, final only at `done`;
the shape of the reachable-stuck toy of the anchor's tests. -/
def toy : OperationalSemantics.OpSem ToyCfg Unit where
  lts := { Tr := fun x _ y => x = .start ∧ y = .blocked }
  Final := fun c => c = .done
  final_terminal := by
    intro c hc μ s' h
    cases c <;> simp_all

theorem toy_step_iff {x y : ToyCfg} : toy.Step x y ↔ x = .start ∧ y = .blocked :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩

theorem toy_final_iff {c : ToyCfg} : toy.Final c ↔ c = .done :=
  Iff.rfl

/-- `blocked` is not final and has no step. -/
theorem toy_blocked_stuck : ¬ toy.Final .blocked ∧ Relation.Normal toy.Step .blocked := by
  refine ⟨fun h => ToyCfg.noConfusion (toy_final_iff.mp h), ?_⟩
  rintro ⟨y, hy⟩
  exact ToyCfg.noConfusion (toy_step_iff.mp hy).1

theorem toy_start_reaches_blocked : Relation.ReflTransGen toy.Step .start .blocked :=
  Relation.ReflTransGen.single (toy_step_iff.mpr ⟨rfl, rfl⟩)

/-- `done` has no step, so typing only `done` is preserved. -/
theorem toy_done_preserved : ∀ _ : Unit, Relation.Preserves toy.Step (· = ToyCfg.done) := by
  intro _ a c hac ha
  obtain ⟨rfl, -⟩ := toy_step_iff.mp hac
  cases ha

/-- The schema applied on the toy: typing only `done`, every reachable state is final or steps.
-/
theorem toy_done_final_or_step {s' : ToyCfg} (h : Relation.ReflTransGen toy.Step .done s') :
    toy.Final s' ∨ ∃ s'', toy.Step s' s'' :=
  final_or_step_of_reflTransGen toy.Step toy.Final (fun c (_ : Unit) => c = .done)
    (fun hs => Or.inl hs) toy_done_preserved (A := ()) rfl h

/-- The stuck form applied on the toy, with the same typing. -/
theorem toy_done_not_stuck {s' : ToyCfg} (h : Relation.ReflTransGen toy.Step .done s') :
    ¬ (¬ toy.Final s' ∧ Relation.Normal toy.Step s') :=
  not_stuck_of_reflTransGen toy.Step toy.Final (fun c (_ : Unit) => c = .done)
    (fun hs => Or.inl hs) toy_done_preserved (A := ()) rfl h

/-- The anchor corollary applied on the toy, with the same typing. -/
theorem toy_done_safe : toy.Safe .done :=
  Cslib.Languages.TypeSafety.OpSem.safe_of_progress_preservation toy
    (fun c (_ : Unit) => c = .done) (fun hc => Or.inl hc) toy_done_preserved (A := ()) rfl

/-- The trivial typing, which types every configuration, satisfies preservation but not
progress: `blocked` is neither final nor reducible. -/
theorem toy_trivial_not_progress : ¬ ∀ c : ToyCfg, toy.Final c ∨ ∃ c', toy.Step c c' := by
  intro h
  rcases h .blocked with hf | ⟨c', hc'⟩
  · exact toy_blocked_stuck.1 hf
  · exact toy_blocked_stuck.2 ⟨c', hc'⟩

/-- **The anchor corollary needs its progress hypothesis.** With the trivial typing every
configuration is typed and preservation holds, but `start` reaches the stuck `blocked`. -/
theorem opSem_safe_needs_progress :
    ¬ ∀ (HasType : ToyCfg → Unit → Prop),
      (∀ A : Unit, Relation.Preserves toy.Step (HasType · A)) →
      ∀ {c : ToyCfg} {A : Unit}, HasType c A → toy.Safe c := by
  intro h
  have hsafe : toy.Safe .start :=
    h (fun _ _ => True) (fun _ _ _ _ _ => trivial) (A := ()) trivial
  refine hsafe .blocked
    ((OperationalSemantics.OpSem.steps_iff_reflTransGen toy).mpr toy_start_reaches_blocked)
    ((OperationalSemantics.OpSem.stuck_iff toy).mpr ⟨toy_blocked_stuck.1, ?_⟩)
  intro μ s' htr
  exact toy_blocked_stuck.2 ⟨s', μ, htr⟩

/-- **The stuck form needs its progress hypothesis.** -/
theorem not_stuck_needs_progress :
    ¬ ∀ (HasType : ToyCfg → Unit → Prop),
      (∀ A : Unit, Relation.Preserves toy.Step (HasType · A)) →
      ∀ {s s' : ToyCfg} {A : Unit}, HasType s A → Relation.ReflTransGen toy.Step s s' →
        ¬ (¬ toy.Final s' ∧ Relation.Normal toy.Step s') := fun h =>
  h (fun _ _ => True) (fun _ _ _ _ _ => trivial) (A := ()) trivial toy_start_reaches_blocked
    toy_blocked_stuck

/-- **The schema needs its preservation hypothesis.** Typing only `start`, progress holds since
`start` steps, but `start` reaches `blocked`, which is neither final nor reducible. -/
theorem final_or_step_needs_preservation :
    ¬ ∀ (HasType : ToyCfg → Unit → Prop),
      (∀ {s : ToyCfg} {A : Unit}, HasType s A → toy.Final s ∨ ∃ s', toy.Step s s') →
      ∀ {s s' : ToyCfg} {A : Unit}, HasType s A → Relation.ReflTransGen toy.Step s s' →
        toy.Final s' ∨ ∃ s'', toy.Step s' s'' := by
  intro h
  rcases h (fun c (_ : Unit) => c = .start)
      (fun hs => Or.inr ⟨.blocked, toy_step_iff.mpr ⟨hs, rfl⟩⟩) (A := ()) rfl
      toy_start_reaches_blocked with hf | ⟨c, hc⟩
  · exact toy_blocked_stuck.1 hf
  · exact toy_blocked_stuck.2 ⟨c, hc⟩

/-! ### Full β-reduction in the locally nameless STLC -/

section LocallyNameless

open Cslib.LambdaCalculus.LocallyNameless Cslib.LambdaCalculus.LocallyNameless.Stlc
  Cslib.LambdaCalculus.LocallyNameless.Untyped

/-- The base type of the examples. -/
def b : Ty Unit := .base ()

/-- `λx. x`. -/
def idTm : Term ℕ := .abs (.bvar 0)

/-- `λx. (λy. y) x`: a value whose body is a β-redex. -/
def etaTm : Term ℕ := .abs (.app (.abs (.bvar 0)) (.bvar 0))

theorem idTm_lc : idTm.LC :=
  Term.LC.abs ∅ _ fun x _ => Term.LC.fvar x

theorem idTm_value : idTm.Value :=
  Term.Value.abs _ idTm_lc

theorem idTm_typing : Typing [] idTm (.arrow b b) :=
  Typing.abs ∅ fun _ _ => Typing.var (List.nodupKeys_singleton _) (List.mem_singleton_self _)

theorem etaTm_value : etaTm.Value :=
  Term.Value.abs _ (Term.LC.abs ∅ _ fun x _ => Term.LC.app idTm_lc (Term.LC.fvar x))

/-- The value `etaTm` reduces under its binder to `λx. x`. -/
theorem etaTm_step : Term.FullBeta etaTm idTm :=
  Term.Xi.abs ∅ fun x _ => Term.Xi.base (Term.Beta.beta idTm_lc (Term.LC.fvar x))

theorem etaTm_typing : Typing [] etaTm (.arrow b b) := by
  refine Typing.abs ∅ fun x _ => ?_
  refine Typing.app (σ := b) ?_
    (Typing.var (List.nodupKeys_singleton _) (List.mem_singleton_self _))
  refine Typing.abs {x} fun y hy => Typing.var ?_ (List.mem_cons_self ..)
  have hyx : y ≠ x := by simpa using hy
  simp [HasWellFormed.wf, List.nodupKeys_cons, hyx]

/-- **Values are not terminal under full β-reduction.** -/
theorem fullBeta_value_not_normal :
    ¬ ∀ t : Term ℕ, t.Value → Relation.Normal Term.FullBeta t := fun h =>
  h etaTm etaTm_value ⟨idTm, etaTm_step⟩

/-- **No anchor semantics has full β-steps with values as final states**: its final states
would have to be terminal, and `etaTm` is a value that steps. -/
theorem no_opSem_fullBeta_value (S : OperationalSemantics.OpSem (Term ℕ) Unit)
    (hstep : ∀ a c, S.Step a c ↔ Term.FullBeta a c) (hfinal : ∀ a, S.Final a ↔ a.Value) :
    False := by
  obtain ⟨μ, htr⟩ := (hstep etaTm idTm).mpr etaTm_step
  exact S.final_terminal ((hfinal etaTm).mpr etaTm_value) μ idTm htr

/-- **The full β instance is the schema at relation level, with final states that step.**
Instantiating `final_or_step_of_reflTransGen` with full β-steps, values as final states, closed
typing, and CSLib's `FullBeta.progress` and `FullBeta.preservation` gives the statement of
`lnStlc_value_or_step`. A schema that required final states to be terminal would need
`∀ t, t.Value → Relation.Normal Term.FullBeta t` here, refuted by `fullBeta_value_not_normal`. -/
theorem lnStlc_value_or_step_of_schema {t t' : Term ℕ} {τ : Ty Unit}
    (ht : Typing [] t τ) (hred : Relation.ReflTransGen Term.FullBeta t t') :
    t'.Value ∨ ∃ t'', Term.FullBeta t' t'' :=
  final_or_step_of_reflTransGen Term.FullBeta Term.Value (fun s (A : Ty Unit) => Typing [] s A)
    (fun hs => FullBeta.progress hs) (fun _ _ _ hab ha => FullBeta.preservation hab ha) ht hred

/-- The stuck form of the schema on the same instance: SF's soundness for full β. -/
theorem lnStlc_not_stuck_of_schema {t t' : Term ℕ} {τ : Ty Unit}
    (ht : Typing [] t τ) (hred : Relation.ReflTransGen Term.FullBeta t t') :
    ¬ (¬ t'.Value ∧ Relation.Normal Term.FullBeta t') :=
  not_stuck_of_reflTransGen Term.FullBeta Term.Value (fun s (A : Ty Unit) => Typing [] s A)
    (fun hs => FullBeta.progress hs) (fun _ _ _ hab ha => FullBeta.preservation hab ha) ht hred

/-- Full β-safety on the closed value `etaTm`, before and after its step under the binder. -/
theorem etaTm_value_or_step :
    (etaTm.Value ∨ ∃ t'', Term.FullBeta etaTm t'') ∧
      (idTm.Value ∨ ∃ t'', Term.FullBeta idTm t'') :=
  ⟨lnStlc_value_or_step etaTm_typing Relation.ReflTransGen.refl,
    lnStlc_value_or_step etaTm_typing (Relation.ReflTransGen.single etaTm_step)⟩

/-- Substitution through the interface: `x₀ : b → b ⊢ x₀ : b → b` and `⊢ λx. x : b → b` give
`⊢ x₀[x₀ := λx. x] : b → b`. -/
theorem lnStlc_subst_example : Typing [] ((Term.fvar 0)[0 := idTm]) (.arrow b b) :=
  structuralTyping_lnStlc.subst (Γ := []) (e := Term.fvar 0)
    (Typing.var (List.nodupKeys_singleton _) (List.mem_singleton_self _)) idTm_typing

theorem lnStlc_subst_example_term : (Term.fvar 0 : Term ℕ)[0 := idTm] = idTm :=
  rfl

/-- Weakening through the interface, by the one-binding block `[⟨0, b⟩]`. -/
theorem lnStlc_weaken_example : Typing [⟨0, b⟩] idTm (.arrow b b) :=
  structuralTyping_lnStlc.weaken ⟨[⟨0, b⟩], List.Perm.refl _, List.nodupKeys_singleton _⟩
    idTm_typing

/-- Exchange for the locally nameless STLC is weakening by the empty block. -/
theorem lnStlc_exchange_example {t : Term ℕ} {τ : Ty Unit}
    (h : Typing [⟨0, b⟩, ⟨1, b⟩] t τ) : Typing [⟨1, b⟩, ⟨0, b⟩] t τ :=
  structuralTyping_lnStlc.weaken
    ⟨[], List.Perm.swap _ _ _, by simp [HasWellFormed.wf, List.nodupKeys_cons]⟩ h

/-- **Weakening has content**: a trivial extension relation fails it. -/
theorem lnStlc_trivial_extends_fails :
    ¬ StructuralTyping (Typing (Var := ℕ) (Base := Unit)) (fun Γ (x : ℕ) σ => ⟨x, σ⟩ :: Γ)
      (fun t (x : ℕ) s => t[x := s]) (fun _ _ => True) (fun _ _ t => t) := by
  intro h
  have h' : Typing [] (Term.fvar 0) b := h.weaken (Γ := [⟨0, b⟩]) trivial
    (Typing.var (List.nodupKeys_singleton _) (List.mem_singleton_self _))
  cases h' with
  | var _ hmem => simp at hmem

/-- **Substitution has content**: an instantiation that drops its argument fails it. -/
theorem lnStlc_dropped_instantiation_fails :
    ¬ StructuralTyping (Typing (Var := ℕ) (Base := Unit)) (fun Γ (x : ℕ) σ => ⟨x, σ⟩ :: Γ)
      (fun t (_ : ℕ) _ => t) (fun Γ Δ => ∃ Θ, (Γ ++ Θ).Perm Δ ∧ Δ✓) (fun _ _ t => t) := by
  intro h
  have h' : Typing [] (Term.fvar 0) (.arrow b b) := h.subst (Γ := []) (e := Term.fvar 0)
    (Typing.var (List.nodupKeys_singleton _) (List.mem_singleton_self _)) idTm_typing
  cases h' with
  | var _ hmem => simp at hmem

end LocallyNameless

/-! ### The calculus with references -/

section References

open Cslib.Languages.LambdaCalculus.References

/-- An allocating program: `ref unit`. -/
def alloc : Term Unit := .ref .unit

theorem alloc_typing : HasType [] [] alloc (.ref .unit) :=
  .ref .unit

/-- `ref unit` in the empty store allocates location `0`. -/
theorem alloc_steps : Steps alloc [] (.loc 0) [.unit] :=
  Steps.single (.refValue .unit)

/-- The allocated location has no type under the empty store typing. -/
theorem loc0_not_typed_empty : ¬ HasType [] ([] : List (Ty Unit)) (.loc 0) (.ref .unit) := by
  intro h
  cases h with
  | loc hl => simp at hl

/-- **Store typings must be allowed to grow**: with equality as the world order, the
preservation hypothesis of the store-world schema fails at the allocation step. -/
theorem references_preservation_needs_growth :
    ¬ ∀ {S : List (Ty Unit)} {c c' : Term Unit × Store Unit} {T : Ty Unit},
      (HasType [] S c.1 T ∧ StoreTyped [] S c.2) → Step c.1 c.2 c'.1 c'.2 →
        ∃ S', S = S' ∧ HasType [] S' c'.1 T ∧ StoreTyped [] S' c'.2 := by
  intro h
  obtain ⟨S', hS, ht, -⟩ := h (S := []) (c := (alloc, [])) (c' := (.loc 0, [.unit]))
    ⟨alloc_typing, .nil⟩ (.refValue .unit)
  subst hS
  exact loc0_not_typed_empty ht

/-- **References through the store-world schema.** Instantiating `exists_ext_of_reflTransGen`
and `final_or_step_of_reflTransGen_ext` with configurations, store typings ordered by prefix,
the existing `progress` and `preservation` gives preservation under a store typing extended as a
prefix, and safety. -/
theorem references_of_world_schema {S : List (Ty Unit)} {t t' : Term Unit}
    {μ μ' : Store Unit} {T : Ty Unit}
    (ht : HasType [] S t T) (hμ : StoreTyped [] S μ) (h : Steps t μ t' μ') :
    (∃ S', S <+: S' ∧ HasType [] S' t' T ∧ StoreTyped [] S' μ') ∧
      (t'.Value ∨ ∃ t'' μ'', Step t' μ' t'' μ'') := by
  have hpres : ∀ {w : List (Ty Unit)} {s s' : Term Unit × Store Unit} {A : Ty Unit},
      (HasType [] w s.1 A ∧ StoreTyped [] w s.2) → Step s.1 s.2 s'.1 s'.2 →
        ∃ w', w <+: w' ∧ (HasType [] w' s'.1 A ∧ StoreTyped [] w' s'.2) :=
    fun hs hstep => Cslib.Languages.LambdaCalculus.References.preservation hs.1 hs.2 hstep
  have hprog : ∀ {w : List (Ty Unit)} {s : Term Unit × Store Unit} {A : Ty Unit},
      (HasType [] w s.1 A ∧ StoreTyped [] w s.2) →
        s.1.Value ∨ ∃ s' : Term Unit × Store Unit, Step s.1 s.2 s'.1 s'.2 := fun hs =>
    (progress hs.1 hs.2).imp id fun ⟨t', μ', h⟩ => ⟨(t', μ'), h⟩
  refine ⟨?_, ?_⟩
  · exact exists_ext_of_reflTransGen
      (fun c c' : Term Unit × Store Unit => Step c.1 c.2 c'.1 c'.2) (· <+: ·)
      (fun w c T => HasType [] w c.1 T ∧ StoreTyped [] w c.2) hpres
      (s := (t, μ)) (s' := (t', μ')) ⟨ht, hμ⟩ h
  · rcases final_or_step_of_reflTransGen_ext
        (fun c c' : Term Unit × Store Unit => Step c.1 c.2 c'.1 c'.2) (fun c => c.1.Value)
        (· <+: ·) (fun w c T => HasType [] w c.1 T ∧ StoreTyped [] w c.2) hprog hpres
        (s := (t, μ)) (s' := (t', μ')) ⟨ht, hμ⟩ h with hv | ⟨⟨t'', μ''⟩, h''⟩
    · exact Or.inl hv
    · exact Or.inr ⟨t'', μ'', h''⟩

/-- Preservation and safety for references on the allocating program. -/
theorem alloc_preservation_and_value_or_step :
    (∃ S', ([] : List (Ty Unit)) <+: S' ∧ HasType [] S' (.loc 0) (.ref .unit) ∧
        StoreTyped [] S' [.unit]) ∧
      ((Term.loc 0 : Term Unit).Value ∨
        ∃ (t'' : Term Unit) (μ'' : Store Unit), Step (.loc 0) [.unit] t'' μ'') :=
  references_of_world_schema alloc_typing .nil alloc_steps

/-- The two conjuncts have the types of the existing `Steps.preservation` (empty variable
context) and `typeSafety`. -/
theorem references_recovers_existing_shapes {S : List (Ty Unit)} {t t' : Term Unit}
    {μ μ' : Store Unit} {T : Ty Unit}
    (ht : HasType [] S t T) (hμ : StoreTyped [] S μ) (h : Steps t μ t' μ') :
    type_of% (Steps.preservation h ht hμ) ∧ type_of% (typeSafety ht hμ h) :=
  references_of_world_schema ht hμ h

/-- Substitution through the interface: `x₀ : Unit ⊢ x₀ : Unit` and `⊢ unit : Unit`. -/
theorem references_subst_example :
    HasType [] [] ((Term.var 0).instantiate .unit) (.unit : Ty Unit) :=
  structuralTyping_references.subst (Γ := ([], [])) (x := ()) (HasType.var rfl) HasType.unit

/-- Weakening through the interface shifts: adding `Ref Unit` innermost and extending the store
typing turns variable `0` into variable `1`. -/
theorem references_weaken_example :
    HasType [.ref .unit, .unit] [.unit] (.var 1) (.unit : Ty Unit) :=
  structuralTyping_references.weaken (Γ := ([.unit], [])) (Δ := ([.ref .unit, .unit], [.unit]))
    (t := .var 0) ⟨⟨[.ref .unit], rfl⟩, List.nil_prefix⟩ (HasType.var rfl)

/-- **De Bruijn weakening needs its shift**: with the identity action, weakening fails, while the
locally nameless instance uses the identity. -/
theorem references_identity_wk_fails :
    ¬ StructuralTyping (fun (c : List (Ty Unit) × List (Ty Unit)) t T => HasType c.1 c.2 t T)
      (fun c (_ : Unit) A => (A :: c.1, c.2)) (fun t (_ : Unit) s => t.instantiate s)
      (fun c d => (∃ Θ, d.1 = Θ ++ c.1) ∧ c.2 <+: d.2) (fun _ _ t => t) := by
  intro h
  have h' : HasType [.ref .unit, .unit] [] (.var 0) (.unit : Ty Unit) :=
    h.weaken (Γ := ([.unit], [])) (Δ := ([.ref .unit, .unit], [])) (t := .var 0)
      ⟨⟨[.ref .unit], rfl⟩, List.prefix_refl _⟩ (HasType.var rfl)
  cases h' with
  | var hx => simp at hx

end References

/-! ### The intrinsically typed STLC through the anchor -/

section Intrinsic

open Cslib.Languages.LambdaCalculus
open scoped CslibStlc

/-- Base type atom. -/
def bT : Stlc.Ty Unit := Stlc.Ty.base ()

/-- The identity at `bT`. -/
def idT : Stlc.Tm ([] : List (Stlc.Ty Unit)) (bT ⇒ bT) := .lam (.var .zero)

/-- A redex applying the identity combinator to `idT`. -/
def redexT : Stlc.Tm ([] : List (Stlc.Ty Unit)) (bT ⇒ bT) := .app (.lam (.var .zero)) idT

theorem idT_redexT_safe :
    (OperationalSemantics.stlc (A := bT ⇒ bT)).Safe idT ∧
      (OperationalSemantics.stlc (A := bT ⇒ bT)).Safe redexT :=
  ⟨stlc_safe idT, stlc_safe redexT⟩

/-- **The intrinsic STLC through the anchor corollary**, with the trivial typing: progress is
`Stlc.Step.progress`, and preservation holds by intrinsic typing. -/
theorem stlc_safe_of_schema {A : Stlc.Ty Unit} (t : Stlc.Tm ([] : List (Stlc.Ty Unit)) A) :
    (OperationalSemantics.stlc (A := A)).Safe t :=
  Cslib.Languages.TypeSafety.OpSem.safe_of_progress_preservation OperationalSemantics.stlc
    (fun _ (_ : Unit) => True)
    (fun {c} {_} _ => (Stlc.Step.progress c).imp id fun ⟨c', h⟩ =>
      ⟨c', OperationalSemantics.stlc_step_iff.mpr h⟩)
    (fun _ _ _ _ _ => trivial) (A := ()) trivial

end Intrinsic

end Cslib.Languages.TypeSafetyTests
