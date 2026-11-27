/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.HindleyMilner.Semantics
public import CSLibExt.Languages.LambdaCalculus.HindleyMilner.AlgorithmW
public import CSLibExt.Languages.TypeSafety

/-!
# Type safety of let-polymorphism

Subject reduction, progress and type soundness for the call-by-value calculus with constants of
`CSLibExt/Languages/LambdaCalculus/HindleyMilner/Semantics.lean`, for the syntax-directed
Damas-Milner typing of `CSLibExt/Languages/LambdaCalculus/HindleyMilner/Typing.lean`, for a
signature of finitely many constants, under the hypotheses `Constants.Agrees` on the δ-relation.
The constants have a pure semantics, so no value restriction is used.

Soundness is not proved separately: it is the safety schema of
`CSLibExt/Languages/TypeSafety.lean` applied to the typing predicate `Constants.Typed`, both in
its relational form (`final_or_step_of_reflTransGen`) and over the operational-semantics anchor
(`OpSem.safe_of_progress_preservation`).

## Main results

- `Constants.Step.preservation` : subject reduction.
- `Constants.progress` : a typed, well-formed expression is a value or reduces.
- `Constants.IsValue.not_step` : values are irreducible.
- `Constants.typeSafety` : no typed program reduces to a stuck expression.
- `Constants.opSem`, `Constants.safe` : the calculus as an operational semantics, in which typed
  programs are safe.
- `Constants.typeSafety_of_W` : a program accepted by Algorithm W does not go wrong.

## References

- F. Pottier, D. Rémy, *The Essence of ML Type Inference*, chapter 10 of B. C. Pierce (ed.),
  *Advanced Topics in Types and Programming Languages*, MIT Press 2005: Theorems 10.5.8,
  10.5.10 and 10.5.11 and Corollary 10.5.9.
- R. Milner, *A theory of type polymorphism in programming*, J. Comput. Syst. Sci. 17(3), 1978,
  348-375: Theorem 1 (semantic soundness), of which these are the syntactic counterparts.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.HindleyMilner

open Cslib.Unification Cslib.Unification.Term
open Cslib.Languages.TypeSafety Cslib.Languages.OperationalSemantics

variable {B : Type u}

namespace Constants

variable {K : Constants B} {δ : Expr → Expr → Prop} {e e' : Expr} {τ : Ty B}

/-- A name outside the constant names is not bound by the initial context. -/
private theorem lookup_eq_none_of_not_mem {z : String} (hz : z ∉ K.names) :
    K.ctx.lookup z = none := by
  cases h : K.ctx.lookup z with
  | none => rfl
  | some σ => exact absurd (List.mem_toFinset.mpr (Ctx.mem_names_of_lookup h)) hz

/-- The free names of an expression typed in the initial context are constant names. -/
private theorem fv_subset_names (he : HasType K.ctx e τ) : e.fv ⊆ K.names := fun y hy ↦ by
  obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp (he.fv_subset y hy)
  exact List.mem_toFinset.mpr (Ctx.mem_names_of_lookup hσ)

/-- **Subject reduction.** Let $\delta$ agree with the signature $K$. If a well-formed expression
$e$ has type $\tau$ in the initial context and $e$ reduces to $e'$, then $e'$ is well formed and
has type $\tau$ in the initial context. -/
theorem Step.preservation (hK : K.Agrees δ) (he : HasType K.ctx e τ) (hwf : K.WF e)
    (hs : K.Step δ e e') : HasType K.ctx e' τ ∧ K.WF e' := by
  induction hs generalizing τ with
  | @beta z b v hv =>
    obtain ⟨τ₁, h₁, h₂⟩ := hasType_app_iff.mp he
    obtain ⟨τ₁', τ₂', heq, hb⟩ := hasType_lam_iff.mp h₁
    cases heq
    simp only [WF, Expr.bv, Finset.disjoint_union_left, Finset.disjoint_insert_left] at hwf
    have hd : Disjoint b.bv v.fv :=
      Finset.disjoint_of_subset_right (fv_subset_names h₂) hwf.1.2
    refine ⟨HasType.subst_mono (lookup_eq_none_of_not_mem hwf.1.1) h₂ hb hd, ?_⟩
    exact Finset.disjoint_of_subset_left (Expr.bv_subst_subset hd)
      (Finset.disjoint_union_left.mpr ⟨hwf.1.2, hwf.2⟩)
  | @letV z v b hv =>
    obtain ⟨τ₁, h₁, h₂⟩ := hasType_let_iff.mp he
    simp only [WF, Expr.bv, Finset.disjoint_insert_left, Finset.disjoint_union_left] at hwf
    have hd : Disjoint b.bv v.fv :=
      Finset.disjoint_of_subset_right (fv_subset_names h₁) hwf.2.2
    refine ⟨HasType.subst_gen (lookup_eq_none_of_not_mem hwf.1) h₁ h₂ hd, ?_⟩
    exact Finset.disjoint_of_subset_left (Expr.bv_subst_subset hd)
      (Finset.disjoint_union_left.mpr ⟨hwf.2.2, hwf.2.1⟩)
  | delta hδ => exact ⟨hK.preserve hδ he hwf, hK.wf hδ hwf⟩
  | appL _ ih =>
    obtain ⟨τ₁, h₁, h₂⟩ := hasType_app_iff.mp he
    simp only [WF, Expr.bv, Finset.disjoint_union_left] at hwf ⊢
    obtain ⟨h₁', hwf₁⟩ := ih h₁ hwf.1
    exact ⟨HasType.app h₁' h₂, hwf₁, hwf.2⟩
  | appR _ _ ih =>
    obtain ⟨τ₁, h₁, h₂⟩ := hasType_app_iff.mp he
    simp only [WF, Expr.bv, Finset.disjoint_union_left] at hwf ⊢
    obtain ⟨h₂', hwf₂⟩ := ih h₂ hwf.2
    exact ⟨HasType.app h₁ h₂', hwf.1, hwf₂⟩
  | letL _ ih =>
    obtain ⟨τ₁, h₁, h₂⟩ := hasType_let_iff.mp he
    simp only [WF, Expr.bv, Finset.disjoint_insert_left, Finset.disjoint_union_left] at hwf ⊢
    obtain ⟨h₁', hwf₁⟩ := ih h₁ hwf.2.1
    exact ⟨HasType.let_ h₁' h₂, hwf.1, hwf₁, hwf.2.2⟩

/-- The head of an application spine and its arguments, in order. -/
private def headArgs : Expr → Expr × List Expr
  | .app e₁ e₂ => ((headArgs e₁).1, (headArgs e₁).2 ++ [e₂])
  | e => (e, [])

/-- Applying to one more argument. -/
private theorem apps_concat (h a : Expr) (args : List Expr) :
    h.apps (args ++ [a]) = .app (h.apps args) a := by
  simp [Expr.apps, List.foldl_append]

/-- The spine of an application to a list of arguments. -/
private theorem headArgs_apps (h : Expr) (args : List Expr) :
    headArgs (h.apps args) = ((headArgs h).1, (headArgs h).2 ++ args) := by
  induction args generalizing h with
  | nil => simp [Expr.apps]
  | cons a as ih =>
    have : h.apps (a :: as) = (Expr.app h a).apps as := rfl
    rw [this, ih]
    simp [headArgs]

/-- An expression is its head applied to its arguments. -/
private theorem apps_headArgs (e : Expr) : (headArgs e).1.apps (headArgs e).2 = e := by
  induction e with
  | app e₁ e₂ ih₁ _ =>
    simp only [headArgs]
    rw [apps_concat, ih₁]
  | var _ => rfl
  | lam _ _ => rfl
  | let_ _ _ _ => rfl

/-- The spine of a constant application. -/
private theorem headArgs_var_apps (c : String) (args : List Expr) :
    headArgs ((Expr.var c).apps args) = (.var c, args) := by
  rw [headArgs_apps]
  simp [headArgs]

/-- A constant application that is an application splits off its last argument. -/
private theorem var_apps_eq_app {c : String} {args : List Expr} {e₁ e₂ : Expr}
    (h : (Expr.var c).apps args = .app e₁ e₂) :
    ∃ args₀, args = args₀ ++ [e₂] ∧ e₁ = (Expr.var c).apps args₀ := by
  have := congrArg headArgs h
  rw [headArgs_var_apps] at this
  simp only [headArgs, Prod.mk.injEq] at this
  refine ⟨(headArgs e₁).2, this.2, ?_⟩
  calc e₁ = (headArgs e₁).1.apps (headArgs e₁).2 := (apps_headArgs e₁).symm
    _ = (Expr.var c).apps (headArgs e₁).2 := by rw [← this.1]

/-- Values, case by case. -/
private theorem isValue_iff : K.IsValue e ↔
    (∃ z, e = .var z ∧ z ∉ K.names) ∨ (∃ z b, e = .lam z b) ∨
    ∃ c args, e = (Expr.var c).apps args ∧ c ∈ K.names ∧ (∀ a ∈ args, K.IsValue a) ∧
      (K.IsCtor c ∧ args.length ≤ K.arity c ∨ ¬ K.IsCtor c ∧ args.length < K.arity c) := by
  constructor
  · intro h
    cases h with
    | var hz => exact Or.inl ⟨_, rfl, hz⟩
    | lam => exact Or.inr (Or.inl ⟨_, _, rfl⟩)
    | const hc hargs hlen => exact Or.inr (Or.inr ⟨_, _, rfl, hc, hargs, hlen⟩)
  · rintro (⟨z, rfl, hz⟩ | ⟨z, b, rfl⟩ | ⟨c, args, rfl, hc, hargs, hlen⟩)
    · exact IsValue.var hz
    · exact IsValue.lam
    · exact IsValue.const hc hargs hlen

/-- **Progress.** Let $\delta$ agree with the signature $K$. If a well-formed expression $e$ has
a type in the initial context, then $e$ is a value or reduces. -/
theorem progress (hK : K.Agrees δ) (he : HasType K.ctx e τ) (hwf : K.WF e) :
    K.IsValue e ∨ ∃ e', K.Step δ e e' := by
  induction e generalizing τ with
  | var y =>
    obtain ⟨σ, ts, hy, rfl⟩ := hasType_var_iff.mp he
    have hc : y ∈ K.names := List.mem_toFinset.mpr (Ctx.mem_names_of_lookup hy)
    exact hK.progress (args := []) hc (by simp) he hwf
  | lam z b => exact Or.inl IsValue.lam
  | app e₁ e₂ ih₁ ih₂ =>
    obtain ⟨τ₁, h₁, h₂⟩ := hasType_app_iff.mp he
    have hwf' := hwf
    simp only [WF, Expr.bv, Finset.disjoint_union_left] at hwf'
    rcases ih₁ h₁ hwf'.1 with hv₁ | ⟨e₁', hs⟩
    · rcases ih₂ h₂ hwf'.2 with hv₂ | ⟨e₂', hs⟩
      · rcases isValue_iff.mp hv₁ with ⟨z, rfl, hz⟩ | ⟨z, b, rfl⟩ | ⟨c, args, rfl, hc, hargs, -⟩
        · obtain ⟨σ, ts, hσ, -⟩ := hasType_var_iff.mp h₁
          exact absurd (List.mem_toFinset.mpr (Ctx.mem_names_of_lookup hσ)) hz
        · exact Or.inr ⟨_, Step.beta hv₂⟩
        · rw [← apps_concat] at he hwf ⊢
          have hargs' : ∀ a ∈ args ++ [e₂], K.IsValue a := by
            intro a ha
            rcases List.mem_append.mp ha with ha | ha
            · exact hargs a ha
            · rw [List.mem_singleton.mp ha]
              exact hv₂
          exact hK.progress hc hargs' he hwf
      · exact Or.inr ⟨_, Step.appR hv₁ hs⟩
    · exact Or.inr ⟨_, Step.appL hs⟩
  | let_ z e₁ e₂ ih₁ _ =>
    obtain ⟨τ₁, h₁, -⟩ := hasType_let_iff.mp he
    have hwf' := hwf
    simp only [WF, Expr.bv, Finset.disjoint_insert_left, Finset.disjoint_union_left] at hwf'
    rcases ih₁ h₁ hwf'.2.1 with hv₁ | ⟨e₁', hs⟩
    · exact Or.inr ⟨_, Step.letV hv₁⟩
    · exact Or.inr ⟨_, Step.letL hs⟩

/-- **Values are irreducible.** Let $\delta$ agree with the signature $K$. A value does not
reduce. -/
theorem IsValue.not_step (hK : K.Agrees δ) (hv : K.IsValue e) : ¬ K.Step δ e e' := by
  intro hs
  induction hs with
  | @beta z b v _ =>
    rcases isValue_iff.mp hv with ⟨_, h, -⟩ | ⟨_, _, h⟩ | ⟨c, args, h, -⟩
    · cases h
    · cases h
    · obtain ⟨args₀, -, h'⟩ := var_apps_eq_app h.symm
      have := congrArg headArgs h'
      rw [headArgs_var_apps] at this
      simp [headArgs] at this
  | letV _ =>
    rcases isValue_iff.mp hv with ⟨_, h, -⟩ | ⟨_, _, h⟩ | ⟨c, args, h, -⟩
    · cases h
    · cases h
    · have := congrArg headArgs h
      rw [headArgs_var_apps] at this
      simp [headArgs] at this
  | delta hδ =>
    obtain ⟨c, args, rfl, hc, hctor, hlen, -⟩ := hK.redex hδ
    rcases isValue_iff.mp hv with ⟨z, h, hz⟩ | ⟨_, _, h⟩ | ⟨c', args', h, -, -, hlen'⟩
    · have := congrArg headArgs h
      rw [headArgs_var_apps] at this
      simp only [headArgs, Prod.mk.injEq, Expr.var.injEq] at this
      exact hz (this.1 ▸ hc)
    · have := congrArg headArgs h
      rw [headArgs_var_apps] at this
      simp [headArgs] at this
    · have := congrArg headArgs h
      rw [headArgs_var_apps, headArgs_var_apps] at this
      simp only [Prod.mk.injEq, Expr.var.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rcases hlen' with ⟨h₁, -⟩ | ⟨-, h₂⟩
      · exact hctor h₁
      · omega
  | @appL e₁ e₁' e₂ _ ih =>
    rcases isValue_iff.mp hv with ⟨_, h, -⟩ | ⟨_, _, h⟩ | ⟨c, args, h, hc, hargs, hlen⟩
    · cases h
    · cases h
    · obtain ⟨args₀, rfl, rfl⟩ := var_apps_eq_app h.symm
      refine ih (isValue_iff.mpr (Or.inr (Or.inr ⟨c, args₀, rfl, hc,
        fun a ha ↦ hargs a (List.mem_append_left _ ha), ?_⟩)))
      simp only [List.length_append, List.length_singleton] at hlen
      rcases hlen with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨h₁, by omega⟩
      · exact Or.inr ⟨h₁, by omega⟩
  | @appR v e₂ e₂' _ _ ih =>
    rcases isValue_iff.mp hv with ⟨_, h, -⟩ | ⟨_, _, h⟩ | ⟨c, args, h, -, hargs, -⟩
    · cases h
    · cases h
    · obtain ⟨args₀, rfl, -⟩ := var_apps_eq_app h.symm
      exact ih (hargs e₂ (List.mem_append_right _ (List.mem_singleton_self _)))
  | letL _ _ =>
    rcases isValue_iff.mp hv with ⟨_, h, -⟩ | ⟨_, _, h⟩ | ⟨c, args, h, -⟩
    · cases h
    · cases h
    · have := congrArg headArgs h
      rw [headArgs_var_apps] at this
      simp [headArgs] at this

/-- **Type soundness.** Let $K$ be a signature, with finitely many constants, and let $\delta$
agree with it. If a well-formed expression $e$ has type $\tau$ in the initial context, then every
expression $e'$ that $e$ reduces to in finitely many steps is a value or reduces: a typed program
does not go wrong. -/
theorem typeSafety (hK : K.Agrees δ) (he : HasType K.ctx e τ) (hwf : K.WF e)
    (hr : Relation.ReflTransGen (K.Step δ) e e') : K.IsValue e' ∨ ∃ e'', K.Step δ e' e'' :=
    final_or_step_of_reflTransGen (K.Step δ) K.IsValue K.Typed
      (fun he ↦ progress hK he.1 he.2)
      (by
        intro A a b hs ha
        exact Step.preservation hK ha.1 ha.2 hs)
      ⟨he, hwf⟩ hr

/-- **The calculus as an operational semantics.** For a δ-relation that agrees with the
signature $K$, the operational semantics whose configurations are expressions, with one label,
whose transitions are the reductions, and whose final configurations are the values; values are
terminal by `IsValue.not_step`. -/
def opSem (hK : K.Agrees δ) : OpSem Expr Unit where
  lts := { Tr := fun e _ e' => K.Step δ e e' }
  Final := K.IsValue
  final_terminal := fun hv _ _ h => IsValue.not_step hK hv h

/-- **Typed programs are safe.** Let $K$ be a signature, with finitely many constants, and let
$\delta$ agree with it. If a well-formed expression $e$ has type $\tau$ in the initial context,
then no configuration reachable from $e$ in `opSem hK` is stuck. -/
theorem safe (hK : K.Agrees δ) (he : HasType K.ctx e τ) (hwf : K.WF e) : (opSem hK).Safe e :=
    OpSem.safe_of_progress_preservation (opSem hK) K.Typed
      (fun he ↦ (progress hK he.1 he.2).imp id fun ⟨e', hs⟩ ↦ ⟨e', (), hs⟩)
      (by
        intro A a b hs ha
        obtain ⟨_, hs⟩ := hs
        exact Step.preservation hK ha.1 ha.2 hs)
      ⟨he, hwf⟩

/-- **Programs accepted by Algorithm W do not go wrong.** Let equality of base types be
decidable, let $K$ be a signature, with finitely many constants, and let $\delta$ agree with it.
If Algorithm W, run on the initial context and a well-formed expression $e$ with any counter
$n$, returns a substitution $s$, a monotype $\tau$ and a counter $n'$, then every expression that
$e$ reduces to in finitely many steps is a value or reduces. -/
theorem typeSafety_of_W [DecidableEq B] (hK : K.Agrees δ) {n n' : ℕ} {s : Subst B}
    (hW : W K.ctx e n = some (s, τ, n')) (hwf : K.WF e)
    (hr : Relation.ReflTransGen (K.Step δ) e e') : K.IsValue e' ∨ ∃ e'', K.Step δ e' e'' :=
  by
    have h := hasType_of_W_eq_some hW
    refine typeSafety hK (h.mono (Ctx.MoreGeneral.of_lookup_eq fun z ↦ ?_)) hwf hr
    rw [Ctx.lookup_subst_congr (t := Term.var) (fun x hx ↦ by simp [K.closed] at hx),
      Ctx.subst_var]

end Constants

end Cslib.HindleyMilner
