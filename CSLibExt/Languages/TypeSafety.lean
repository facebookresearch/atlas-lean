/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.OperationalSemantics
public import CSLibExt.Languages.LambdaCalculus.References.Preservation
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.Safety
import Cslib.Foundations.Relation.Preserves

/-!
# Type safety from progress and preservation

A syntactic type-safety schema stated over a one-step relation `Step`, a predicate `Final` on
states, and a typing predicate `HasType` chosen by the language. `Final` need not be terminal:
a final state may still step, as values do under full β-reduction, and a consumer may take as
final any state it accepts as an answer. From progress (every typed state is final or steps)
and preservation (each type is preserved by `Step`), no state reachable from a typed state is
stuck (`not_stuck_of_reflTransGen`), equivalently every reachable state is final or steps
(`final_or_step_of_reflTransGen`).

The store-world variant lets the typing of a state depend on a world, such as a store typing,
and lets a step move to a larger world in a preorder `ext`
(`exists_ext_of_reflTransGen`, `final_or_step_of_reflTransGen_ext`).
`OpSem.safe_of_progress_preservation` is the corollary over the operational-semantics anchor
`Cslib.Languages.OperationalSemantics.OpSem`, concluding `OpSem.Safe`.

`StructuralTyping` states the single-variable substitution lemma and weakening as properties of
a typing judgment over operations the language supplies: binding a variable in a context,
instantiating a variable by a term, a context-extension relation, and the action of weakening on
terms. There is no generic substitution operation.

The instances apply existing theorems: the locally nameless simply typed λ-calculus of CSLib
under full β-reduction, at the level of relations because its values reduce under binders, and
the closed fibre of the intrinsically typed STLC through the anchor.
Both the locally nameless STLC and the calculus with references satisfy `StructuralTyping`.

## References

* B. C. Pierce et al., *Software Foundations*, chapter `StlcProp`: `Theorem progress`,
  `Theorem preservation`, `Corollary type_soundness`, `Lemma substitution_preserves_typing`, and
  `Lemma weakening` (Programming Language Foundations edition).
* P. Sewell, *Semantics of Programming Languages*, Cambridge CST Part IB 2025-26: Theorem 4
  (Safety), Theorems 18-19 (Progress, Type Preservation), Lemma 20 (Substitution), and
  Theorems 24-25 (Type Preservation and Type Safety with store typings that grow).
* B. C. Pierce, *Types and Programming Languages*, Theorem 13.5.3 and Lemma 13.5.4.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace Cslib.Languages.TypeSafety

/-! ### The schema over a step relation -/

/-- **Typed states never reach a stuck state.** Let `Step` be a one-step relation on states,
`Final` a predicate on states that need not be terminal, and `HasType s A` a typing predicate.
Assume progress, every typed state is final or steps, and preservation, every step from a state
of type `A` reaches a state of type `A`. Then every state reachable from a typed state is not
stuck, that is, it is not a non-final normal form.

Source: Software Foundations, `StlcProp`, `Corollary type_soundness`, where
`stuck t := normal_form step t ∧ ¬ value t`. -/
theorem not_stuck_of_reflTransGen {State : Type u} {Ty : Type v}
    (Step : State → State → Prop) (Final : State → Prop) (HasType : State → Ty → Prop)
    (progress : ∀ {s : State} {A : Ty}, HasType s A → Final s ∨ ∃ s', Step s s')
    (preservation : ∀ A : Ty, Relation.Preserves Step (HasType · A)) :
    ∀ {s s' : State} {A : Ty}, HasType s A → Relation.ReflTransGen Step s s' →
      ¬ (¬ Final s' ∧ Relation.Normal Step s') := by
  rintro s s' A hs hss' ⟨hnf, hnormal⟩
  rcases progress (Relation.preserves_reflTransGen_iff.mpr (preservation A) hss' hs) with
    hfin | hstep
  · exact hnf hfin
  · exact hnormal hstep

/-- **Typed states reach only final or reducible states.** Under the hypotheses of
`not_stuck_of_reflTransGen` (progress, and preservation of each type by `Step`), every state
reachable from a typed state is final or takes a step.

Source: Sewell, *Semantics of Programming Languages*, Theorem 4 (Safety) and Theorem 25. -/
theorem final_or_step_of_reflTransGen {State : Type u} {Ty : Type v}
    (Step : State → State → Prop) (Final : State → Prop) (HasType : State → Ty → Prop)
    (progress : ∀ {s : State} {A : Ty}, HasType s A → Final s ∨ ∃ s', Step s s')
    (preservation : ∀ A : Ty, Relation.Preserves Step (HasType · A)) :
    ∀ {s s' : State} {A : Ty}, HasType s A → Relation.ReflTransGen Step s s' →
      Final s' ∨ ∃ s'', Step s' s'' := by
  intro s s' A hs hss'
  exact progress (Relation.preserves_reflTransGen_iff.mpr (preservation A) hss' hs)

/-! ### Store-world variant -/

/-- **Multi-step preservation with growing worlds.** Let `ext` be a preorder on worlds and
`HasType w s A` a typing predicate that depends on a world `w`. If every step from a state of
type `A` in world `w` reaches a state of type `A` in some world extending `w`, then every state
reachable from a state of type `A` in `w` has type `A` in some world extending `w`.

Source: Sewell, *Semantics of Programming Languages*, Theorem 24; Pierce, *Types and
Programming Languages*, Theorem 13.5.3. -/
theorem exists_ext_of_reflTransGen {State : Type u} {Ty : Type v} {W : Type w}
    (Step : State → State → Prop) (ext : W → W → Prop) [IsPreorder W ext]
    (HasType : W → State → Ty → Prop)
    (preservation : ∀ {w : W} {s s' : State} {A : Ty},
      HasType w s A → Step s s' → ∃ w', ext w w' ∧ HasType w' s' A) :
    ∀ {w : W} {s s' : State} {A : Ty}, HasType w s A → Relation.ReflTransGen Step s s' →
      ∃ w', ext w w' ∧ HasType w' s' A := by
  intro w s s' A hs hss'
  induction hss' with
  | refl => exact ⟨w, Std.Refl.refl w, hs⟩
  | tail _ hstep ih =>
    obtain ⟨w₁, hw₁, h₁⟩ := ih
    obtain ⟨w₂, hw₂, h₂⟩ := preservation h₁ hstep
    exact ⟨w₂, IsTrans.trans _ _ _ hw₁ hw₂, h₂⟩

/-- **Safety with growing worlds.** Under the hypotheses of `exists_ext_of_reflTransGen`, if
moreover every state typed in some world is final or steps, then every state reachable from a
typed state is final or takes a step.

Source: Sewell, *Semantics of Programming Languages*, Theorem 25 (Type Safety). -/
theorem final_or_step_of_reflTransGen_ext {State : Type u} {Ty : Type v} {W : Type w}
    (Step : State → State → Prop) (Final : State → Prop) (ext : W → W → Prop)
    [IsPreorder W ext] (HasType : W → State → Ty → Prop)
    (progress : ∀ {w : W} {s : State} {A : Ty}, HasType w s A → Final s ∨ ∃ s', Step s s')
    (preservation : ∀ {w : W} {s s' : State} {A : Ty},
      HasType w s A → Step s s' → ∃ w', ext w w' ∧ HasType w' s' A) :
    ∀ {w : W} {s s' : State} {A : Ty}, HasType w s A → Relation.ReflTransGen Step s s' →
      Final s' ∨ ∃ s'', Step s' s'' := by
  intro w s s' A hs hss'
  obtain ⟨_, _, hs'⟩ := exists_ext_of_reflTransGen Step ext HasType preservation hs hss'
  exact progress hs'

/-! ### Corollary over the operational-semantics anchor -/

/-- **Progress and preservation make the anchor safe.** For an operational semantics `S` in the
sense of the anchor and a typing predicate on its configurations, progress (every typed
configuration is final or steps) and preservation of each type by the unlabelled step imply
that every typed configuration is safe: no configuration reachable from it is stuck. -/
theorem OpSem.safe_of_progress_preservation {Config : Type u} {Label : Type v} {Ty : Type w}
    (S : OperationalSemantics.OpSem Config Label) (HasType : Config → Ty → Prop)
    (progress : ∀ {c : Config} {A : Ty}, HasType c A → S.Final c ∨ ∃ c', S.Step c c')
    (preservation : ∀ A : Ty, Relation.Preserves S.Step (HasType · A)) :
    ∀ {c : Config} {A : Ty}, HasType c A → S.Safe c := by
  intro c A hc d hcd hstuck
  obtain ⟨hnf, hterm⟩ := (OperationalSemantics.OpSem.stuck_iff S).mp hstuck
  refine not_stuck_of_reflTransGen S.Step S.Final HasType progress preservation hc
    ((OperationalSemantics.OpSem.steps_iff_reflTransGen S).mp hcd) ⟨hnf, ?_⟩
  rintro ⟨d', μ, htr⟩
  exact hterm μ d' htr

/-! ### Structural typing interface -/

/-- **Structural properties of a typing judgment.** For a typing judgment `HasType Γ t A` and
operations supplied by the language, namely `bind Γ x A` (the context `Γ` extended by a variable
`x` of type `A`), `inst e x v` (the term `e` with `x` instantiated by `v`), a context-extension
relation `Extends Γ Δ`, and the action `wk Γ Δ t` of weakening from `Γ` to `Δ` on terms: the
single-variable substitution lemma and weakening hold. A language whose contexts are finite maps
from names can take `wk` to be the identity; a de Bruijn language shifts variables. -/
structure StructuralTyping {Ctx : Type u} {Tm : Type v} {Ty : Type w} {Name : Type z}
    (HasType : Ctx → Tm → Ty → Prop) (bind : Ctx → Name → Ty → Ctx)
    (inst : Tm → Name → Tm → Tm) (Extends : Ctx → Ctx → Prop)
    (wk : Ctx → Ctx → Tm → Tm) : Prop where
  /-- **Substitution lemma.** If `e` has type `B` in `Γ` extended by `x` of type `A`, and `v`
  has type `A` in `Γ`, then `e` with `x` instantiated by `v` has type `B` in `Γ`.

  Source: Software Foundations, `StlcProp`, `Lemma substitution_preserves_typing`; Sewell,
  Lemma 20. -/
  subst : ∀ {Γ : Ctx} {x : Name} {A B : Ty} {e v : Tm},
    HasType (bind Γ x A) e B → HasType Γ v A → HasType Γ (inst e x v) B
  /-- **Weakening.** If `Γ` extends to `Δ` and `t` has type `A` in `Γ`, then the weakened term
  `wk Γ Δ t` has type `A` in `Δ`.

  Source: Software Foundations, `StlcProp`, `Lemma weakening`. -/
  weaken : ∀ {Γ Δ : Ctx} {t : Tm} {A : Ty},
    Extends Γ Δ → HasType Γ t A → HasType Δ (wk Γ Δ t) A

section LocallyNameless

open Cslib.LambdaCalculus.LocallyNameless Cslib.LambdaCalculus.LocallyNameless.Stlc
  Cslib.LambdaCalculus.LocallyNameless.Untyped

/-- **The locally nameless STLC has the structural properties.** CSLib's locally nameless
simply typed λ-calculus satisfies `StructuralTyping` with binding `⟨x, σ⟩ :: Γ`, instantiation
`t[x := s]`, the extension of `Γ` to every well-formed context `Δ` that is a permutation of
`Γ ++ Θ` for some `Θ`, and the identity action of weakening on terms. Substitution is CSLib's
`Typing.typing_subst_head`; weakening combines `Typing.weaken`, whose well-formedness side
condition the extension relation carries, with `Typing.perm`. -/
theorem structuralTyping_lnStlc {Var : Type u} {Base : Type v} [DecidableEq Var]
    [HasFresh Var] :
    StructuralTyping (Typing (Var := Var) (Base := Base))
      (fun Γ (x : Var) σ => ⟨x, σ⟩ :: Γ) (fun t (x : Var) s => t[x := s])
      (fun Γ Δ => ∃ Θ, (Γ ++ Θ).Perm Δ ∧ Δ✓) (fun _ _ t => t) where
  subst hbind hv := Typing.typing_subst_head hbind hv
  weaken := by
    rintro Γ Δ t A ⟨Θ, hperm, hwf⟩ ht
    exact (Typing.weaken ht ((List.perm_nodupKeys hperm).mpr hwf)).perm hperm

set_option linter.unusedDecidableInType false in
/-- **Full β-reduction in the locally nameless STLC is safe.** A closed term of type `τ` reduces
in any number of full β-steps only to values or to terms that reduce further. Full β-reduction
reduces under binders, so a value can still step; the statement is at the level of relations,
with values as the final states, and is not a statement about the anchor `OpSem`, whose final
states must be terminal. -/
theorem lnStlc_value_or_step {Var : Type u} {Base : Type v} [HasFresh Var] [DecidableEq Var]
    {t t' : Term Var} {τ : Ty Base} :
    Typing [] t τ → Relation.ReflTransGen Term.FullBeta t t' →
      t'.Value ∨ ∃ t'', Term.FullBeta t' t'' := by
  intro ht hred
  exact final_or_step_of_reflTransGen Term.FullBeta Term.Value
    (fun s (A : Ty Base) => Typing [] s A) (fun hs => FullBeta.progress hs)
    (fun _ _ _ hab ha => FullBeta.preservation hab ha) ht hred

end LocallyNameless

section References

open Cslib.Languages.LambdaCalculus.References

/-- **The lambda calculus with references has the structural properties.** The simply typed
λ-calculus with references satisfies `StructuralTyping` when a context pairs a variable context
`Γ` with a store typing `S`: binding adds a new innermost de Bruijn variable to `Γ`;
instantiation is `Term.instantiate`; `(Γ, S)` extends to `(Δ, S')` when `Δ = Θ ++ Γ` for a block
`Θ` of new innermost variables and `S` is a prefix of `S'`; and weakening shifts every free
variable by the length of `Θ`. Substitution is `HasType.instantiate`; weakening combines
`HasType.rename` with `HasType.extendStore`. -/
theorem structuralTyping_references {Base : Type u} :
    StructuralTyping (fun (c : List (Ty Base) × List (Ty Base)) t T => HasType c.1 c.2 t T)
      (fun c (_ : Unit) A => (A :: c.1, c.2)) (fun t (_ : Unit) s => t.instantiate s)
      (fun c d => (∃ Θ, d.1 = Θ ++ c.1) ∧ c.2 <+: d.2)
      (fun c d t => t.rename (· + (d.1.length - c.1.length))) where
  subst hbody hs := HasType.instantiate hbody hs
  weaken := by
    rintro ⟨Γ, S⟩ ⟨Δ, S'⟩ t A ⟨⟨Θ, hΔ⟩, hS⟩ ht
    dsimp only at hΔ hS ht ⊢
    subst hΔ
    refine (HasType.rename ht fun x B hx => ?_).extendStore hS
    rw [List.length_append, Nat.add_sub_cancel,
      List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel]
    exact hx

end References

section Intrinsic

open Cslib.Languages.LambdaCalculus

/-- **Closed terms of the intrinsically typed STLC are safe.** Every closed term of the
intrinsically typed simply typed λ-calculus is safe for the anchor's call-by-value semantics on
its closed fibre: no configuration it reaches is stuck. -/
theorem stlc_safe {Base : Type u} {A : Stlc.Ty Base}
    (t : Stlc.Tm ([] : List (Stlc.Ty Base)) A) :
    (OperationalSemantics.stlc (Base := Base) (A := A)).Safe t := by
  refine OpSem.safe_of_progress_preservation OperationalSemantics.stlc
    (fun _ (_ : Unit) => True) (fun {c} {_} _ => ?_) (fun _ _ _ _ _ => trivial) (A := ()) trivial
  rcases Stlc.Step.progress c with hv | ⟨c', hstep⟩
  · exact Or.inl hv
  · exact Or.inr ⟨c', OperationalSemantics.stlc_step_iff.mpr hstep⟩

end Intrinsic

end Cslib.Languages.TypeSafety
