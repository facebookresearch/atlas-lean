/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.FeatherweightJava.Structural
public import CSLibExt.Languages.TypeSafety
import Cslib.Foundations.Relation.Preserves

/-!
# Featherweight Java: subject reduction, progress and type soundness

Type soundness of Featherweight Java for the call-by-value, left-to-right relation `Step` of
`CSLibExt.Languages.FeatherweightJava.Basic`, after Igarashi, Pierce and Wadler (TOPLAS 2001),
Section 2.4.

* `CastStuck` and `ArgsCastStuck`: an expression, respectively an argument list, stuck at a
  failed cast in evaluation position: a cast `(T) (new K(v̄))` of a value for some classes `K`
  and `T` with `K ≮: T`. The constructors mirror the congruence rules of `Step` one for one;
  `CastStuck.not_step` and `CastStuck.not_value` show that such an expression neither steps nor
  is a value.
* `Typing.subject_reduction`: a step preserves typing up to subtyping (Theorem 2.4.1 for the
  call-by-value `Step`), with the argument-list companion `ArgsTyping.subject_reduction` and the
  multi-step form `Typing.subject_reduction_steps`.
* `Typing.progress`: a closed well-typed expression is a value, is stuck at a failed cast in
  evaluation position, or steps under the call-by-value `Step`, with the companion
  `ArgsTyping.progress`. It holds for every class table.
* `Typing.fields_of_fld_new` and `Typing.mbody_of_invk_new`: the redex facts of Theorem 2.4.2.
* `Typing.soundness`: a closed well-typed expression that reaches a normal form by `Steps` ends
  at a value typed at a subtype of the original type, or stuck at a failed cast in evaluation
  position (Theorem 2.4.3 for the call-by-value `Step`). It applies the schema
  `Cslib.Languages.TypeSafety.final_or_step_of_reflTransGen` with typing at a subtype.

TOPLAS states Theorems 2.4.1-2.4.3 for a nondeterministic relation closed under every
congruence; its footnote 2 points to a call-by-value variant in Pierce (2002). Every theorem here
is about the repository's call-by-value `Step`, whose evaluation contexts are those of Cornell
CS 4110 Lecture #30. The two soundness statements are not comparable: the call-by-value relation
reaches fewer expressions but has more normal forms. Theorem 2.4.3 prints `C <: D` in the
stuck branch; this should read `C ≮: D`, by Fig. 3 (R-Cast). The stuck cast there is
`(D) new C(ē)`, which R-Cast reduces whenever `C <: D`; `C` is the class of the object, not the
type of the original expression.

## References

* A. Igarashi, B. C. Pierce, P. Wadler, *Featherweight Java: A Minimal Core Calculus for Java
  and GJ*, ACM TOPLAS 23(3):396-450, 2001: Section 2.4 (Theorems 2.4.1-2.4.3, footnote 2) and
  Appendix A.1 (Lemmas A.1.1-A.1.4, proof of Theorem 2.4.1).
* *A Theory of Featherweight Java in Isabelle/HOL*, Archive of Formal Proofs, Sections 3.6-3.9;
  Section 3.8 strengthens the TOPLAS progress lemmas by a decomposition: a closed well-typed
  expression is a value or contains a potential redex. `Typing.progress` refines it to a
  three-way classification for the evaluation contexts of Lecture #30.
* Cornell CS 4110, Lecture #30 (Featherweight Java): evaluation contexts
  `E ::= [·] | E.f | E.m(ē) | v.m(v̄, E, ē) | new C(v̄, E, ē) | (C) E`.
-/

@[expose] public section
set_option autoImplicit false
namespace Cslib.FeatherweightJava

/-! ### Stuck casts -/

mutual
  /-- An expression stuck at a failed cast in evaluation position: a cast `(T) (new K(v̄))` of a
  value for some classes `K` and `T` with `K ≮: T`, under the evaluation contexts of the
  call-by-value `Step` (Lecture #30). The congruence constructors mirror those of `Step` one for
  one. This is the cast-failure case of TOPLAS Theorem 2.4.3, refined from "contains" to "in
  evaluation position". -/
  inductive CastStuck (ct : ClassTable) : Expr → Prop where
  | cast {C D : CName} {vs : Expr.Args} :
    ArgsValue vs → ¬ Subtype ct C D → CastStuck ct (.cast D (.new C vs))
  | fldCongr {e : Expr} {f : FName} :
    CastStuck ct e → CastStuck ct (.fld e f)
  | invkRecv {e : Expr} {m : MName} {args : Expr.Args} :
    CastStuck ct e → CastStuck ct (.invk e m args)
  | invkArgs {C : CName} {vs args : Expr.Args} {m : MName} :
    ArgsValue vs → ArgsCastStuck ct args → CastStuck ct (.invk (.new C vs) m args)
  | newArgs {C : CName} {args : Expr.Args} :
    ArgsCastStuck ct args → CastStuck ct (.new C args)
  | castCongr {C : CName} {e : Expr} :
    CastStuck ct e → CastStuck ct (.cast C e)

  /-- An argument list stuck at a failed cast in its leftmost non-value argument, as
  `ArgsStep` evaluates argument lists left to right under the call-by-value `Step`. -/
  inductive ArgsCastStuck (ct : ClassTable) : Expr.Args → Prop where
  | head {e : Expr} {args : Expr.Args} :
    CastStuck ct e → ArgsCastStuck ct (.cons e args)
  | tail {v : Expr} {args : Expr.Args} :
    Value v → ArgsCastStuck ct args → ArgsCastStuck ct (.cons v args)
end

/-! ### Normal forms -/

mutual
  /-- Values do not step under the call-by-value `Step`. -/
  theorem Value.not_step {ct : ClassTable} {e e' : Expr} (h : Value e) : ¬ Step ct e e' :=
    match h with
    | .new _ _ ha => fun hs => by
      cases hs with
      | newArgs hs => exact ArgsValue.not_argsStep ha hs

  /-- Value argument lists do not step under the call-by-value `ArgsStep`. -/
  theorem ArgsValue.not_argsStep {ct : ClassTable} {args args' : Expr.Args}
      (h : ArgsValue args) : ¬ ArgsStep ct args args' :=
    match h with
    | .nil => fun hs => by cases hs
    | .cons hv ha => fun hs => by
      cases hs with
      | head hs => exact Value.not_step hv hs
      | tail _ hs => exact ArgsValue.not_argsStep ha hs
end

mutual
  /-- An expression stuck at a failed cast is not a value. -/
  theorem CastStuck.not_value {ct : ClassTable} {e : Expr} (h : CastStuck ct e) : ¬ Value e :=
    match h with
    | .cast _ _ => fun hv => by cases hv
    | .fldCongr _ => fun hv => by cases hv
    | .invkRecv _ => fun hv => by cases hv
    | .invkArgs _ _ => fun hv => by cases hv
    | .newArgs ha => fun hv => by
      cases hv with
      | new _ _ hav => exact ArgsCastStuck.not_argsValue ha hav
    | .castCongr _ => fun hv => by cases hv

  /-- An argument list stuck at a failed cast is not a value list. -/
  theorem ArgsCastStuck.not_argsValue {ct : ClassTable} {args : Expr.Args}
      (h : ArgsCastStuck ct args) : ¬ ArgsValue args :=
    match h with
    | .head hc => fun hv => by
      cases hv with
      | cons hv _ => exact CastStuck.not_value hc hv
    | .tail _ ha => fun hv => by
      cases hv with
      | cons _ hav => exact ArgsCastStuck.not_argsValue ha hav
end

mutual
  /-- An expression stuck at a failed cast does not step under the call-by-value `Step`. -/
  theorem CastStuck.not_step {ct : ClassTable} {e e' : Expr} (h : CastStuck ct e) :
      ¬ Step ct e e' :=
    match h with
    | .cast hvs hn => fun hs => by
      cases hs with
      | cast _ hsub => exact hn hsub
      | castCongr hs => exact Value.not_step (.new _ _ hvs) hs
    | .fldCongr hc => fun hs => by
      cases hs with
      | proj hav _ _ => exact CastStuck.not_value hc (.new _ _ hav)
      | fldCongr hs => exact CastStuck.not_step hc hs
    | .invkRecv hc => fun hs => by
      cases hs with
      | invk hvs _ _ _ => exact CastStuck.not_value hc (.new _ _ hvs)
      | invkRecv hs => exact CastStuck.not_step hc hs
      | invkArgs hvs _ => exact CastStuck.not_value hc (.new _ _ hvs)
    | .invkArgs hvs ha => fun hs => by
      cases hs with
      | invk _ hus _ _ => exact ArgsCastStuck.not_argsValue ha hus
      | invkRecv hs => exact Value.not_step (.new _ _ hvs) hs
      | invkArgs _ hs => exact ArgsCastStuck.not_argsStep ha hs
    | .newArgs ha => fun hs => by
      cases hs with
      | newArgs hs => exact ArgsCastStuck.not_argsStep ha hs
    | .castCongr hc => fun hs => by
      cases hs with
      | cast hvs _ => exact CastStuck.not_value hc (.new _ _ hvs)
      | castCongr hs => exact CastStuck.not_step hc hs

  /-- An argument list stuck at a failed cast does not step under the call-by-value
  `ArgsStep`. -/
  theorem ArgsCastStuck.not_argsStep {ct : ClassTable} {args args' : Expr.Args}
      (h : ArgsCastStuck ct args) : ¬ ArgsStep ct args args' :=
    match h with
    | .head hc => fun hs => by
      cases hs with
      | head hs => exact CastStuck.not_step hc hs
      | tail hv _ => exact CastStuck.not_value hc hv
    | .tail hv ha => fun hs => by
      cases hs with
      | head hs => exact Value.not_step hv hs
      | tail _ hs => exact ArgsCastStuck.not_argsStep ha hs
end

/-! ### Inversion and lookup -/

/-- A typed argument list is as long as its expected type list. -/
theorem ArgsTyping.length_eq {ct : ClassTable} {Γ : Ctx} {args : Expr.Args}
    {Bs : List CName} (h : ArgsTyping ct Γ args Bs) : args.length = Bs.length :=
  by
    induction Bs generalizing args with
    | nil =>
      cases h
      rfl
    | cons B Bs ih =>
      cases h with
      | cons _ _ ht => simp only [Expr.Args.length, List.length_cons, ih ht]

/-- Inversion of T-New: an object creation types at its own class, with its arguments typed
against the class's fields. -/
theorem Typing.new_inv {ct : ClassTable} {Γ : Ctx} {C D : CName} {args : Expr.Args}
    (h : Typing ct Γ (.new C args) D) :
    D = C ∧ ∃ fs, fields ct C = some fs ∧ ArgsTyping ct Γ args (fs.map Prod.fst) :=
  by
    cases h with
    | new hf ha => exact ⟨rfl, _, hf, ha⟩

/-- Inversion of T-Field: a field access types at the declared type of the field in the
receiver's class. -/
theorem Typing.fld_inv {ct : ClassTable} {Γ : Ctx} {e : Expr} {f : FName} {Ci : CName}
    (h : Typing ct Γ (.fld e f) Ci) :
    ∃ C fs, Typing ct Γ e C ∧ fields ct C = some fs ∧ (Ci, f) ∈ fs :=
  by
    cases h with
    | field he hf hm => exact ⟨_, _, he, hf, hm⟩

/-- Inversion of T-Invk: an invocation types at the return type of the method type found in the
receiver's class, with its arguments typed against the parameter types. -/
theorem Typing.invk_inv {ct : ClassTable} {Γ : Ctx} {e : Expr} {m : MName} {args : Expr.Args}
    {B0 : CName} (h : Typing ct Γ (.invk e m args) B0) :
    ∃ C Bs, Typing ct Γ e C ∧ mtype ct m C = some (Bs, B0) ∧ ArgsTyping ct Γ args Bs :=
  by
    cases h with
    | invk he hm ha => exact ⟨_, _, he, hm, ha⟩

/-- Inversion of T-UCast, T-DCast and T-SCast: a cast types at its target class, and its
subject is typed. -/
theorem Typing.cast_inv {ct : ClassTable} {Γ : Ctx} {C D : CName} {e : Expr}
    (h : Typing ct Γ (.cast C e) D) : D = C ∧ ∃ D', Typing ct Γ e D' :=
  by
    cases h with
    | ucast he _ => exact ⟨rfl, _, he⟩
    | dcast he _ _ => exact ⟨rfl, _, he⟩
    | scast he _ _ => exact ⟨rfl, _, he⟩

/-- If field names are distinct and the arguments are typed against the declared field types,
the argument expression that `fieldValue` selects for a field `f` declared at type `Ci` types at
a subtype of `Ci` (the R-Field case of the proof of TOPLAS Theorem 2.4.1). The selected argument
need not be a value; `ArgsValue` is a premise of the step E-Proj, not of this lemma. -/
theorem fieldValue_typing {ct : ClassTable} {Γ : Ctx} {fs : List (CName × FName)}
    {args : Expr.Args} {Ci : CName} {f : FName} {v : Expr} (hnd : (fs.map Prod.snd).Nodup)
    (hmem : (Ci, f) ∈ fs) (hargs : ArgsTyping ct Γ args (fs.map Prod.fst))
    (hv : fieldValue fs args f = some v) :
    ∃ A, Typing ct Γ v A ∧ Subtype ct A Ci :=
  by
    induction fs generalizing args with
    | nil => exact absurd hmem List.not_mem_nil
    | cons p tl ih =>
      obtain ⟨Cp, g⟩ := p
      rw [List.map_cons] at hargs
      rw [List.map_cons, List.nodup_cons] at hnd
      cases hargs with
      | cons hu hsub hrest =>
        change (if g == f then some _ else fieldValue tl _ f) = some v at hv
        by_cases hg : g = f
        · subst hg
          simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hv
          subst hv
          rcases List.mem_cons.mp hmem with heq | htl
          · cases heq
            exact ⟨_, hu, hsub⟩
          · exact absurd (List.mem_map_of_mem (f := Prod.snd) htl) hnd.1
        · have hb : (g == f) = false := beq_eq_false_iff_ne.mpr hg
          simp only [hb, Bool.false_eq_true, ↓reduceIte] at hv
          rcases List.mem_cons.mp hmem with heq | htl
          · cases heq
            exact absurd rfl hg
          · exact ih hnd.2 htl hrest hv

/-- When a field occurs in the field list and there is one argument per field, `fieldValue`
returns an argument expression for it, not necessarily a value. -/
theorem exists_fieldValue {fs : List (CName × FName)} {args : Expr.Args} {Ci : CName}
    {f : FName} (hmem : (Ci, f) ∈ fs) (hlen : args.length = fs.length) :
    ∃ v, fieldValue fs args f = some v :=
  by
    induction fs generalizing args with
    | nil => exact absurd hmem List.not_mem_nil
    | cons p tl ih =>
      obtain ⟨Cp, g⟩ := p
      cases args with
      | nil => simp [Expr.Args.length] at hlen
      | cons u us =>
        by_cases hg : g = f
        · subst hg
          exact ⟨u, show (if g == g then some u else fieldValue tl us g) = some u by simp⟩
        · rcases List.mem_cons.mp hmem with heq | htl
          · cases heq
            exact absurd rfl hg
          · obtain ⟨v, hv⟩ := ih htl (by simpa [Expr.Args.length] using hlen)
            exact ⟨v, show (if g == f then some u else fieldValue tl us f) = some v by
              simp [hg, hv]⟩

/-- Any cast of a typed expression types at its target class, by T-UCast, T-DCast or T-SCast
(case RC-Cast of the proof of TOPLAS Theorem 2.4.1). -/
theorem Typing.recast {ct : ClassTable} {Γ : Ctx} {e : Expr} {C C' : CName}
    (h : Typing ct Γ e C') : Typing ct Γ (.cast C e) C :=
  by
    by_cases hup : Subtype ct C' C
    · exact .ucast h hup
    · by_cases hdown : Subtype ct C C'
      · exact .dcast h hdown (fun hc => hup (hc ▸ Relation.ReflTransGen.refl))
      · exact .scast h hdown hup

/-! ### Redex facts (TOPLAS Theorem 2.4.2) -/

/-- **TOPLAS Theorem 2.4.2 (1).** A typed field access on an object creation names a field of
that class: `fields(C0) = C̄ f̄` and `f ∈ f̄`. No class-table property is assumed. Progress for the
call-by-value `Step` uses it at the E-Proj redex; TOPLAS states it for every such subexpression
of a well-typed expression. -/
theorem Typing.fields_of_fld_new {ct : ClassTable} {Γ : Ctx} {C0 : CName} {es : Expr.Args}
    {f : FName} {C : CName} (h : Typing ct Γ (.fld (.new C0 es) f) C) :
    ∃ fs, fields ct C0 = some fs ∧ ∃ Ci, (Ci, f) ∈ fs :=
  by
    obtain ⟨C1, fs, hr, hf, hm⟩ := Typing.fld_inv h
    obtain ⟨rfl, -⟩ := Typing.new_inv hr
    exact ⟨fs, hf, C, hm⟩

/-- **TOPLAS Theorem 2.4.2 (2).** A typed invocation on an object creation finds a method body
whose parameter list matches the arguments: `mbody(m, C0) = x̄.e0` and `#(x̄) = #(d̄)`. No
class-table property is assumed. Progress for the call-by-value `Step` uses it at the E-Invk
redex; TOPLAS states it for every such subexpression of a well-typed expression. -/
theorem Typing.mbody_of_invk_new {ct : ClassTable} {Γ : Ctx} {C0 : CName} {es : Expr.Args}
    {m : MName} {ds : Expr.Args} {C : CName} (h : Typing ct Γ (.invk (.new C0 es) m ds) C) :
    ∃ xs e0, mbody ct m C0 = some (xs, e0) ∧ xs.length = ds.length :=
  by
    obtain ⟨C1, Bs, hr, hm, ha⟩ := Typing.invk_inv h
    obtain ⟨rfl, -⟩ := Typing.new_inv hr
    obtain ⟨xs, e0, hmb, hlen⟩ := mtype_mbody hm
    exact ⟨xs, e0, hmb, hlen.trans (ArgsTyping.length_eq ha).symm⟩

/-! ### Subject reduction (TOPLAS Theorem 2.4.1) -/

mutual
  /-- **Subject reduction for the call-by-value `Step`** (TOPLAS Theorem 2.4.1, whose relation
  is nondeterministic). In a valid class table and any context, a step from an expression of
  type `C` reaches an expression typed at a subtype of `C`. The type can shrink (an upcast
  steps to the object it casts, and a method body can type below the declared return type), and
  the stupid cast T-SCast is needed when a cast subject steps (TOPLAS p. 405). -/
  theorem Typing.subject_reduction {ct : ClassTable} (hct : ValidTable ct) {Γ : Ctx}
      {e e' : Expr} {C : CName} (h : Typing ct Γ e C) (hs : Step ct e e') :
      ∃ C', Typing ct Γ e' C' ∧ Subtype ct C' C :=
    match hs, h with
    | .proj _ hf hv, h => by
      obtain ⟨C0, fs0, hr, hf0, hm⟩ := Typing.fld_inv h
      obtain ⟨rfl, fs1, hf1, ha⟩ := Typing.new_inv hr
      cases hf.symm.trans hf0
      cases hf.symm.trans hf1
      exact fieldValue_typing (hct.1.fieldNamesNodup _ _ hf) hm ha hv
    | .invk _ _ hmb hlen, h => by
      obtain ⟨C0, Bs, hr, hmt, ha⟩ := Typing.invk_inv h
      obtain ⟨rfl, -⟩ := Typing.new_inv hr
      obtain ⟨D0, hsub, B, hB, hbody⟩ := method_body_typing hct.2 hmt hmb
      obtain ⟨C', hC', hsub'⟩ := Typing.subst_method_body hct.1
        (hlen.trans (ArgsTyping.length_eq ha)) hbody hr hsub ha
      exact ⟨C', hC', hsub'.trans hB⟩
    | .cast _ hsub, h => by
      obtain ⟨rfl, D', hr⟩ := Typing.cast_inv h
      obtain ⟨rfl, -⟩ := Typing.new_inv hr
      exact ⟨_, hr, hsub⟩
    | .fldCongr hs, h => by
      obtain ⟨C0, fs, hr, hf, hm⟩ := Typing.fld_inv h
      obtain ⟨C1, hr', hsub⟩ := Typing.subject_reduction hct hr hs
      obtain ⟨gs, hgs⟩ := fields_of_subtype hct.1 hsub hf
      exact ⟨_, .field hr' hgs (List.mem_append_left _ hm), Relation.ReflTransGen.refl⟩
    | .invkRecv hs, h => by
      obtain ⟨C0, Bs, hr, hmt, ha⟩ := Typing.invk_inv h
      obtain ⟨C1, hr', hsub⟩ := Typing.subject_reduction hct hr hs
      exact ⟨_, .invk hr' (mtype_of_subtype hct.1 hsub hmt) ha, Relation.ReflTransGen.refl⟩
    | .invkArgs _ hs, h => by
      obtain ⟨C0, Bs, hr, hmt, ha⟩ := Typing.invk_inv h
      exact ⟨_, .invk hr hmt (ArgsTyping.subject_reduction hct ha hs), Relation.ReflTransGen.refl⟩
    | .newArgs hs, h => by
      obtain ⟨rfl, fs, hf, ha⟩ := Typing.new_inv h
      exact ⟨_, .new hf (ArgsTyping.subject_reduction hct ha hs), Relation.ReflTransGen.refl⟩
    | .castCongr hs, h => by
      obtain ⟨rfl, D', hr⟩ := Typing.cast_inv h
      obtain ⟨D'', hr', -⟩ := Typing.subject_reduction hct hr hs
      exact ⟨_, Typing.recast hr', Relation.ReflTransGen.refl⟩

  /-- **Subject reduction for argument lists under the call-by-value `ArgsStep`.** In a valid
  class table, a step of a typed argument list keeps its expected type list. -/
  theorem ArgsTyping.subject_reduction {ct : ClassTable} (hct : ValidTable ct) {Γ : Ctx}
      {args args' : Expr.Args} {Bs : List CName} (h : ArgsTyping ct Γ args Bs)
      (hs : ArgsStep ct args args') : ArgsTyping ct Γ args' Bs :=
    match hs, h with
    | .head hs, .cons he hsub ha => by
      obtain ⟨A', he', hsub'⟩ := Typing.subject_reduction hct he hs
      exact .cons he' (hsub'.trans hsub) ha
    | .tail _ hs, .cons he hsub ha => .cons he hsub (ArgsTyping.subject_reduction hct ha hs)
end

/-- **Multi-step subject reduction for the call-by-value `Steps`.** In a valid class table and
any context, every expression reachable from an expression of type `C` is typed at a subtype
of `C`. -/
theorem Typing.subject_reduction_steps {ct : ClassTable} (hct : ValidTable ct) {Γ : Ctx}
    {e e' : Expr} {C : CName} (h : Typing ct Γ e C) (hs : Steps ct e e') :
    ∃ C', Typing ct Γ e' C' ∧ Subtype ct C' C :=
  (Relation.preserves_reflTransGen_iff
      (P := fun x => ∃ C', Typing ct Γ x C' ∧ Subtype ct C' C)).mpr
    (fun _ _ hab ⟨_, h1, hsub1⟩ => by
      obtain ⟨C2, h2, hsub2⟩ := Typing.subject_reduction hct h1 hab
      exact ⟨C2, h2, hsub2.trans hsub1⟩)
    hs ⟨C, h, Relation.ReflTransGen.refl⟩

/-! ### Progress -/

/-- Progress for a cast, from progress for its subject (helper for `Typing.progress`). -/
private theorem progress_cast {ct : ClassTable} {C : CName} {e : Expr}
    (ih : Value e ∨ CastStuck ct e ∨ ∃ e', Step ct e e') :
    Value (.cast C e) ∨ CastStuck ct (.cast C e) ∨ ∃ e', Step ct (.cast C e) e' := by
  rcases ih with hv | hc | ⟨_, hs⟩
  · cases hv with
    | new C1 vs hvs =>
      by_cases hsub : Subtype ct C1 C
      · exact Or.inr (Or.inr ⟨_, Step.cast hvs hsub⟩)
      · exact Or.inr (Or.inl (.cast hvs hsub))
  · exact Or.inr (Or.inl (.castCongr hc))
  · exact Or.inr (Or.inr ⟨_, .castCongr hs⟩)

mutual
  /-- **Progress for the call-by-value `Step`, modulo failed casts.** A closed well-typed
  expression is a value, is stuck at a failed cast in evaluation position, or steps. No
  class-table property is assumed. The Isabelle/HOL theory (Section 3.8) strengthens the TOPLAS
  progress lemmas (Theorem 2.4.2) by a decomposition: a closed well-typed expression is a value
  or contains a potential redex. This three-way classification refines it for the evaluation
  contexts of Lecture #30: the redex is in evaluation position, and a cast redex
  `(T) (new K(v̄))` steps when `K <: T` and is a failed cast otherwise. -/
  theorem Typing.progress {ct : ClassTable} {e : Expr} {C : CName}
      (h : Typing ct (fun _ => none) e C) : Value e ∨ CastStuck ct e ∨ ∃ e', Step ct e e' :=
    match h with
    | .var hx => by simp at hx
    | .field he hf hm => by
      rcases Typing.progress he with hv | hc | ⟨_, hs⟩
      · cases hv with
        | new C1 args hav =>
          obtain ⟨rfl, fs', hf', ha⟩ := Typing.new_inv he
          cases hf.symm.trans hf'
          obtain ⟨v, hv⟩ := exists_fieldValue hm ((ArgsTyping.length_eq ha).trans (by simp))
          exact Or.inr (Or.inr ⟨v, Step.proj hav hf hv⟩)
      · exact Or.inr (Or.inl (.fldCongr hc))
      · exact Or.inr (Or.inr ⟨_, .fldCongr hs⟩)
    | .invk he hm ha => by
      rcases Typing.progress he with hv | hc | ⟨_, hs⟩
      · cases hv with
        | new C1 vs hvs =>
          obtain ⟨rfl, -⟩ := Typing.new_inv he
          rcases ArgsTyping.progress ha with hav | hac | ⟨_, hs⟩
          · obtain ⟨xs, e0, hmb, hlen⟩ := mtype_mbody hm
            exact Or.inr (Or.inr
              ⟨_, Step.invk hvs hav hmb (hlen.trans (ArgsTyping.length_eq ha).symm)⟩)
          · exact Or.inr (Or.inl (.invkArgs hvs hac))
          · exact Or.inr (Or.inr ⟨_, .invkArgs hvs hs⟩)
      · exact Or.inr (Or.inl (.invkRecv hc))
      · exact Or.inr (Or.inr ⟨_, .invkRecv hs⟩)
    | .new _ ha => by
      rcases ArgsTyping.progress ha with hav | hac | ⟨_, hs⟩
      · exact Or.inl (.new _ _ hav)
      · exact Or.inr (Or.inl (.newArgs hac))
      · exact Or.inr (Or.inr ⟨_, .newArgs hs⟩)
    | .ucast he _ => progress_cast (Typing.progress he)
    | .dcast he _ _ => progress_cast (Typing.progress he)
    | .scast he _ _ => progress_cast (Typing.progress he)

  /-- **Progress for argument lists under the call-by-value `ArgsStep`.** A closed typed
  argument list is all values, is stuck at a failed cast in its leftmost non-value
  argument, or steps. No class-table property is assumed. -/
  theorem ArgsTyping.progress {ct : ClassTable} {args : Expr.Args} {Bs : List CName}
      (h : ArgsTyping ct (fun _ => none) args Bs) :
      ArgsValue args ∨ ArgsCastStuck ct args ∨ ∃ args', ArgsStep ct args args' :=
    match h with
    | .nil => Or.inl .nil
    | .cons he _ ha => by
      rcases Typing.progress he with hv | hc | ⟨_, hs⟩
      · rcases ArgsTyping.progress ha with hav | hac | ⟨_, hs⟩
        · exact Or.inl (.cons hv hav)
        · exact Or.inr (Or.inl (.tail hv hac))
        · exact Or.inr (Or.inr ⟨_, .tail hv hs⟩)
      · exact Or.inr (Or.inl (.head hc))
      · exact Or.inr (Or.inr ⟨_, .head hs⟩)
end

/-! ### Type soundness (TOPLAS Theorem 2.4.3) -/

/-- **Type soundness for the call-by-value `Step`** (TOPLAS Theorem 2.4.3, whose relation is
nondeterministic). In a valid class table, if a closed expression of type `C` reaches a normal
form `e'` by `Steps`, then `e'` is a value typed at some `D <: C`, or `e'` is stuck at a failed
cast in evaluation position: a cast `(T) (new K(v̄))` of a value for some classes `K` and `T`
with `K ≮: T`, independent of `C`. This refines TOPLAS's "an expression containing" such a
cast. The proof applies
`Cslib.Languages.TypeSafety.final_or_step_of_reflTransGen` with final states `Value` or
`CastStuck` and the typing predicate "typed at a subtype". -/
theorem Typing.soundness {ct : ClassTable} (hct : ValidTable ct) {e e' : Expr} {C : CName}
    (h : Typing ct (fun _ => none) e C) (hs : Steps ct e e') (hn : Relation.Normal (Step ct) e') :
    (Value e' ∧ ∃ D, Typing ct (fun _ => none) e' D ∧ Subtype ct D C) ∨ CastStuck ct e' :=
  by
    rcases Cslib.Languages.TypeSafety.final_or_step_of_reflTransGen (Step ct)
        (fun e => Value e ∨ CastStuck ct e)
        (fun e C => ∃ C', Typing ct (fun _ => none) e C' ∧ Subtype ct C' C)
        (fun ⟨_, h, _⟩ => by
          rcases Typing.progress h with hv | hc | hs
          · exact Or.inl (Or.inl hv)
          · exact Or.inl (Or.inr hc)
          · exact Or.inr hs)
        (fun _ _ _ hab ⟨_, h, hsub⟩ => by
          obtain ⟨C'', h', hsub'⟩ := Typing.subject_reduction hct h hab
          exact ⟨C'', h', hsub'.trans hsub⟩)
        ⟨C, h, Relation.ReflTransGen.refl⟩ hs with (hv | hc) | hstep
    · exact Or.inl ⟨hv, Typing.subject_reduction_steps hct h hs⟩
    · exact Or.inr hc
    · exact absurd hstep hn

end Cslib.FeatherweightJava
