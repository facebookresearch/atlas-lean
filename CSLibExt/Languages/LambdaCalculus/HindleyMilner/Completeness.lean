/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Completeness of Algorithm W: principal types
-/
module

public import CSLibExt.Languages.LambdaCalculus.HindleyMilner.AlgorithmW

/-!
# Completeness of Algorithm W: principal types

If some substitution instance `u Γ` of a context types `e` with `τ'`, then Algorithm
W succeeds on `Γ` and `e`, and its answer is at least as general: there is `r` with
`u = s ≫ r` on the variables below the counter and `τ' = τ.subst r` (Damas and
Milner).  For closed expressions this gives principal types: `infer e` succeeds
exactly on typable expressions, and every type of `e` is an instance of the inferred
one.

The proof needs W's freshness invariants (`W_fresh`): when every free variable of `Γ`
is below `n`, W only produces types and substitution values over variables below the
returned counter.  It also needs the strong most-general-unifier property of `unify`
(`s' = s ≫ s'`) and the bound on the variables `unify` introduces
(`Unification.vars_unify_subset`, in `Foundations/Unification/Basic.lean`).

## Main results

- `W_fresh` : W's freshness invariants.
- `W_complete` : completeness of Algorithm W.
- `infer_isSome_iff`, `infer_principal` : `infer` succeeds exactly on typable closed
  expressions, and returns a principal type.

## References

- L. Damas, R. Milner, *Principal type-schemes for functional programs*, POPL 1982.
- W. Naraschewski, T. Nipkow, *Type inference verified: Algorithm W in
  Isabelle/HOL*, J. Automated Reasoning 23, 1999, 299-318.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.HindleyMilner

open Cslib.Unification Cslib.Unification.Term Cslib.Unification.Subst

variable {B : Type u}

/-! ### Variable bounds -/

/-- **Variables below a bound.** A term $t$ has all its variables below $n$ when every variable
$z$ occurring in $t$ satisfies $z < n$. -/
def VarsBelow (n : ℕ) (t : Term B) : Prop := ∀ z ∈ t.vars, z < n

theorem VarsBelow.subst {n m : ℕ} {t : Term B} {s : Subst B} (ht : VarsBelow n t)
    (hs : ∀ x < n, VarsBelow m (s x)) : VarsBelow m (t.subst s) := fun z hz ↦ by
  obtain ⟨y, hy, hzy⟩ := exists_of_mem_vars_subst hz
  exact hs y (ht y hy) z hzy

theorem VarsBelow.mono {n m : ℕ} {t : Term B} (ht : VarsBelow n t) (h : n ≤ m) :
    VarsBelow m t := fun z hz ↦ lt_of_lt_of_le (ht z hz) h

theorem Ctx.ftv_subst_below {Γ : Ctx B} {n m : ℕ} {s : Subst B} (hΓ : ∀ z ∈ Γ.ftv, z < n)
    (hs : ∀ x < n, VarsBelow m (s x)) : ∀ z ∈ (Γ.subst s).ftv, z < m := fun z hz ↦ by
  obtain ⟨y, hy, hzy⟩ := Ctx.mem_ftv_subst hz
  exact hs y (hΓ y hy) z hzy

theorem Scheme.mem_vars_inst {σ : Scheme B} {ts : ℕ → Ty B} {z : ℕ}
    (hz : z ∈ (σ.inst ts).vars) : z ∈ σ.vars ∨ ∃ i < σ.boundSup, z ∈ (ts i).vars := by
  induction σ with
  | var x => exact Or.inl hz
  | const c =>
    cases c with
    | inl b => simp [Scheme.inst, Scheme.eval, Term.vars] at hz
    | inr i => exact Or.inr ⟨i, by simp [Scheme.boundSup], hz⟩
  | node l r ihl ihr =>
    simp only [Scheme.inst, Scheme.eval, Term.vars, Finset.mem_union] at hz ihl ihr
    simp only [Term.vars, Finset.mem_union, Scheme.boundSup]
    rcases hz with hz | hz
    · rcases ihl hz with h | ⟨i, hi, h⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨i, by omega, h⟩
    · rcases ihr hz with h | ⟨i, hi, h⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨i, by omega, h⟩

theorem vars_gen_subset_ftv (Γ : Ctx B) (τ : Ty B) : (gen Γ τ).vars ⊆ Γ.ftv := by
  intro z hz
  rw [vars_gen, Finset.mem_filter] at hz
  exact hz.2

variable [DecidableEq B]

/-! ### Freshness invariants of W -/

/-- **Freshness invariants of Algorithm W.** Let $\Gamma$ be a typing context and $n$ a
natural number such that every free type variable of $\Gamma$ is less than $n$. If Algorithm W
succeeds on $\Gamma$ and an expression $e$ with counter $n$, returning a substitution $s$, a
monotype $\tau$ and a new counter $n'$, then $n \le n'$, every type variable of $\tau$ is less
than $n'$, and for every type variable $x < n$ every type variable of $s(x)$ is less than
$n'$. -/
theorem W_fresh {e : Expr} :
    ∀ {Γ : Ctx B} {n : ℕ} {s : Subst B} {τ : Ty B} {n' : ℕ}, (∀ z ∈ Γ.ftv, z < n) →
      W Γ e n = some (s, τ, n') →
      n ≤ n' ∧ VarsBelow n' τ ∧ ∀ x < n, VarsBelow n' (s x) := by
  induction e with
  | var x =>
    intro Γ n s τ n' hΓ h
    rw [W] at h
    obtain ⟨σ, hσ, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    refine ⟨Nat.le_add_right _ _, fun z hz ↦ ?_, fun x hx z hz ↦ ?_⟩
    · rcases Scheme.mem_vars_inst hz with h | ⟨i, hi, h⟩
      · exact lt_of_lt_of_le (hΓ z (Ctx.vars_subset_ftv_of_lookup hσ h)) (Nat.le_add_right _ _)
      · simp only [Term.vars, Finset.mem_singleton] at h
        omega
    · simp only [Term.vars, Finset.mem_singleton] at hz
      omega
  | lam x e ih =>
    intro Γ n s τ n' hΓ h
    rw [W] at h
    obtain ⟨⟨s₀, τ₀, n₀⟩, h₀, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hΓ' : ∀ z ∈ Ctx.ftv ((x, toScheme (Term.var n)) :: Γ), z < n + 1 := by
      intro z hz
      rcases Finset.mem_union.mp (Ctx.ftv_cons_subset _ _ _ hz) with hz | hz
      · simp only [vars_toScheme, Term.vars, Finset.mem_singleton] at hz
        omega
      · exact lt_of_lt_of_le (hΓ z hz) (Nat.le_succ _)
    obtain ⟨hle, hτ, hs⟩ := ih hΓ' h₀
    refine ⟨by omega, fun z hz ↦ ?_, fun y hy ↦ hs y (by omega)⟩
    simp only [Term.vars, Finset.mem_union, subst_var] at hz
    rcases hz with hz | hz
    · exact hs n (by omega) z hz
    · exact hτ z hz
  | app e₁ e₂ ih₁ ih₂ =>
    intro Γ n s τ n' hΓ h
    rw [W] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨s₁, τ₁, n₁⟩, h₁, ⟨s₂, τ₂, n₂⟩, h₂, s₃, h₃, he⟩ := h
    simp only [Prod.mk.injEq] at he h₂ h₃
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨hle₁, hτ₁, hs₁⟩ := ih₁ hΓ h₁
    obtain ⟨hle₂, hτ₂, hs₂⟩ := ih₂ (Ctx.ftv_subst_below hΓ hs₁) h₂
    -- the unified equation lives below `n₂ + 1`
    have hE : ∀ z ∈ eqVars [(τ₁.subst s₂, node τ₂ (Term.var n₂))], z < n₂ + 1 := by
      intro z hz
      simp only [eqVars, Finset.mem_union, Term.vars, Finset.mem_singleton,
        Finset.notMem_empty, or_false] at hz
      rcases hz with (hz | hz | rfl)
      · exact Nat.lt_succ_of_lt (hτ₁.subst hs₂ z hz)
      · exact Nat.lt_succ_of_lt (hτ₂ z hz)
      · omega
    have hs₃ : ∀ x < n₂ + 1, VarsBelow (n₂ + 1) (s₃ x) := fun x hx z hz ↦ by
      rcases Finset.mem_insert.mp (vars_unify_subset _ s₃ h₃ x hz) with rfl | h
      · exact hx
      · exact hE z h
    refine ⟨by omega, fun z hz ↦ ?_, fun x hx ↦ ?_⟩
    · exact hs₃ n₂ (by omega) z (by simpa using hz)
    · show VarsBelow (n₂ + 1) ((((s₁ x).subst s₂)).subst s₃)
      refine VarsBelow.subst ?_ hs₃
      exact ((hs₁ x hx).subst hs₂).mono (by omega)
  | let_ x e₁ e₂ ih₁ ih₂ =>
    intro Γ n s τ n' hΓ h
    rw [W] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨s₁, τ₁, n₁⟩, h₁, ⟨s₂, τ₂, n₂⟩, h₂, he⟩ := h
    simp only [Prod.mk.injEq] at he h₂
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨hle₁, hτ₁, hs₁⟩ := ih₁ hΓ h₁
    have hΓ₁ := Ctx.ftv_subst_below hΓ hs₁
    have hΓ' : ∀ z ∈ Ctx.ftv ((x, gen (Γ.subst s₁) τ₁) :: Γ.subst s₁), z < n₁ := by
      intro z hz
      rcases Finset.mem_union.mp (Ctx.ftv_cons_subset _ _ _ hz) with hz | hz
      · exact hΓ₁ z (vars_gen_subset_ftv _ _ hz)
      · exact hΓ₁ z hz
    obtain ⟨hle₂, hτ₂, hs₂⟩ := ih₂ hΓ' h₂
    exact ⟨by omega, hτ₂, fun y hy ↦ (hs₁ y hy).subst hs₂⟩

/-! ### Completeness -/

omit [DecidableEq B] in
theorem Scheme.eval_congr {σ : Scheme B} {f f' g : ℕ → Ty B} (h : ∀ x ∈ σ.vars, f x = f' x) :
    σ.eval f g = σ.eval f' g := by
  induction σ with
  | var x => exact h x (by simp [Term.vars])
  | const c => cases c <;> rfl
  | node l r ihl ihr =>
    simp only [Term.vars, Finset.mem_union] at h
    simp [Scheme.eval, ihl fun x hx ↦ h x (Or.inl hx), ihr fun x hx ↦ h x (Or.inr hx)]

omit [DecidableEq B] in
/-- **Substituting into a generalization is more general.** For a typing context $\Gamma$, a
monotype $\tau$ and a type substitution $r$, the scheme obtained by applying $r$ to the free
type variables of the generalization of $\tau$ in $\Gamma$ is more general than the
generalization of $r(\tau)$ in $r(\Gamma)$: every instance of the latter is an instance of the
former, and every free type variable of the former is a free type variable of the latter. -/
theorem substTy_gen_moreGeneral (Γ : Ctx B) (τ : Ty B) (r : Subst B) :
    ((gen Γ τ).substTy r).MoreGeneral (gen (Γ.subst r) (τ.subst r)) := by
  refine ⟨fun ts ↦ ⟨fun y ↦ (r y).subst fun z ↦
      if z ∈ (Γ.subst r).ftv then Term.var z else ts z, ?_⟩, ?_⟩
  · rw [inst_gen, Scheme.inst, eval_substTy, eval_gen, subst_subst]
    refine subst_congr fun y _ ↦ ?_
    by_cases hy : y ∈ Γ.ftv
    · simp only [hy, ↓reduceIte, subst_id]
      conv_lhs => rw [← subst_id (r y)]
      refine subst_congr fun z hz ↦ ?_
      have : z ∈ (Γ.subst r).ftv := Ctx.vars_subset_ftv_subst hy hz
      simp [this]
    · simp [hy]
  · intro z hz
    obtain ⟨y, hy, hzy⟩ := vars_substTy_subset r _ hz
    rw [vars_gen, Finset.mem_filter] at hy
    rw [vars_gen, Finset.mem_filter]
    exact ⟨vars_subset_vars_subst hy.1 hzy, Ctx.vars_subset_ftv_subst hy.2 hzy⟩

omit [DecidableEq B] in
theorem Ctx.lookup_subst_eq_of_agree {Γ : Ctx B} {n : ℕ} {u : Subst B} {s r : Subst B}
    (hΓ : ∀ z ∈ Γ.ftv, z < n) (h : ∀ x < n, u x = (s x).subst r) (y : String) :
    ((Γ.subst s).subst r).lookup y = (Γ.subst u).lookup y := by
  rw [Ctx.subst_subst]
  exact Ctx.lookup_subst_congr (fun x hx ↦ (h x (hΓ x hx)).symm) y

omit [DecidableEq B] in
/-- **Generalization depends only on the free variables of the context.** If two typing
contexts $\Gamma$ and $\Gamma'$ have the same free type variables, then for every monotype
$\tau$ the generalization of $\tau$ in $\Gamma$ equals the generalization of $\tau$ in
$\Gamma'$. -/
theorem gen_congr {Γ Γ' : Ctx B} (h : Γ.ftv = Γ'.ftv) (τ : Ty B) : gen Γ τ = gen Γ' τ := by
  simp only [gen, h]

/-- **Completeness of Algorithm W.** Let $\Gamma$ be a typing context and $n$ a natural number
such that every free type variable of $\Gamma$ is less than $n$. If, for some type substitution
$u$, an expression $e$ has a monotype $\tau'$ in the context $u(\Gamma)$, then Algorithm W
succeeds on $\Gamma$ and $e$ with counter $n$, returning a substitution $s$, a monotype $\tau$
and a new counter $n'$, and there is a type substitution $r$ such that $u(x) = r(s(x))$ for
every type variable $x < n$, and $\tau' = r(\tau)$.

This is the completeness theorem of Damas and Milner. -/
theorem W_complete {e : Expr} :
    ∀ {Γ : Ctx B} {n : ℕ} {u : Subst B} {τ' : Ty B}, (∀ z ∈ Γ.ftv, z < n) →
      HasType (Γ.subst u) e τ' →
      ∃ s τ n' r, W Γ e n = some (s, τ, n') ∧ (∀ x < n, u x = (s x).subst r) ∧
        τ' = τ.subst r := by
  induction e with
  | var x =>
    intro Γ n u τ' hΓ h
    obtain ⟨σ', ts', hσ', rfl⟩ := hasType_var_iff.mp h
    rw [Ctx.lookup_subst] at hσ'
    obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp hσ'
    refine ⟨Term.var, σ.inst fun i ↦ Term.var (n + i), n + σ.boundSup,
      fun z ↦ if z < n then u z else ts' (z - n), by rw [W, hσ]; rfl, ?_, ?_⟩
    · intro x hx
      simp [hx]
    · rw [Scheme.inst, Scheme.inst, eval_substTy, subst_eval]
      simp only [subst_var, subst_id, Nat.add_sub_cancel_left,
        show ∀ i, ¬ n + i < n from fun i ↦ by omega, ↓reduceIte]
      refine Scheme.eval_congr fun y hy ↦ ?_
      simp [hΓ y (Ctx.vars_subset_ftv_of_lookup hσ hy)]
  | lam x e ih =>
    intro Γ n u τ' hΓ h
    obtain ⟨τ₁', τ₂', rfl, hb⟩ := hasType_lam_iff.mp h
    let u' : Subst B := fun z ↦ if z = n then τ₁' else u z
    have hΓ' : ∀ z ∈ Ctx.ftv ((x, toScheme (Term.var n)) :: Γ), z < n + 1 := by
      intro z hz
      rcases Finset.mem_union.mp (Ctx.ftv_cons_subset _ _ _ hz) with hz | hz
      · simp only [vars_toScheme, Term.vars, Finset.mem_singleton] at hz
        omega
      · exact lt_of_lt_of_le (hΓ z hz) (Nat.le_succ _)
    have hctx : HasType (Ctx.subst u' ((x, toScheme (Term.var n)) :: Γ)) e τ₂' := by
      show HasType ((x, (toScheme (Term.var n)).substTy u') :: Γ.subst u') e τ₂'
      rw [← toScheme_subst, subst_var]
      have hu'n : u' n = τ₁' := by simp [u']
      rw [hu'n]
      refine hb.mono ((Ctx.MoreGeneral.of_lookup_eq fun y ↦ ?_).cons x
        (Scheme.MoreGeneral.refl _))
      exact Ctx.lookup_subst_congr (fun z hz ↦ by simp [u', show z ≠ n from (hΓ z hz).ne]) y
    obtain ⟨s, τ, n', r, hW, hsr, hτ⟩ := ih hΓ' hctx
    refine ⟨s, node ((Term.var n).subst s) τ, n', r, by rw [W, hW]; rfl, fun y hy ↦ ?_, ?_⟩
    · have := hsr y (by omega)
      simpa [u', hy.ne] using this
    · have := hsr n (by omega)
      simp only [u', ↓reduceIte] at this
      simp [this, hτ]
  | app e₁ e₂ ih₁ ih₂ =>
    intro Γ n u τ' hΓ h
    obtain ⟨τ₁', h₁, h₂⟩ := hasType_app_iff.mp h
    obtain ⟨s₁, τ₁, n₁, r₁, hW₁, hsr₁, hτ₁⟩ := ih₁ hΓ h₁
    obtain ⟨hle₁, hτ₁b, hs₁b⟩ := W_fresh hΓ hW₁
    have hΓ₁ := Ctx.ftv_subst_below hΓ hs₁b
    obtain ⟨s₂, τ₂, n₂, r₂, hW₂, hsr₂, hτ₂⟩ :=
      ih₂ hΓ₁ (h₂.mono (Ctx.MoreGeneral.of_lookup_eq (Ctx.lookup_subst_eq_of_agree hΓ hsr₁)))
    obtain ⟨hle₂, hτ₂b, hs₂b⟩ := W_fresh hΓ₁ hW₂
    let r₃ : Subst B := fun z ↦ if z = n₂ then τ' else r₂ z
    -- `r₃` agrees with `r₂` below `n₂`
    have hr₃ : ∀ {t : Ty B}, VarsBelow n₂ t → t.subst r₃ = t.subst r₂ := fun ht ↦
      subst_congr fun z hz ↦ by simp [r₃, (ht z hz).ne]
    -- `s₂ ≫ r₃` agrees with `r₁` below `n₁`
    have hr₁ : ∀ {t : Ty B}, VarsBelow n₁ t → t.subst r₁ = (t.subst s₂).subst r₃ := by
      intro t ht
      rw [subst_subst]
      refine subst_congr fun y hy ↦ ?_
      rw [hr₃ (hs₂b y (ht y hy)), hsr₂ y (ht y hy)]
    have hunif : Unifies r₃ [(τ₁.subst s₂, node τ₂ (Term.var n₂))] := by
      refine unifies_cons.mpr ⟨?_, unifies_nil _⟩
      simp only
      rw [← hr₁ hτ₁b, ← hτ₁, subst_node, hr₃ hτ₂b, ← hτ₂]
      simp [r₃]
    obtain ⟨s₃, hs₃⟩ := Option.isSome_iff_exists.mp (unify_isSome_iff.mpr ⟨r₃, hunif⟩)
    have hmgu := unify_eq_some_comp hs₃ hunif
    refine ⟨s₁ ≫ s₂ ≫ s₃, (Term.var n₂).subst s₃, n₂ + 1, r₃, ?_, fun x hx ↦ ?_, ?_⟩
    · simp [W, hW₁, hW₂, hs₃]
    · rw [hsr₁ x hx, hr₁ (hs₁b x hx)]
      conv_lhs => rw [hmgu, subst_comp]
      rfl
    · rw [← subst_comp, ← hmgu]
      simp [r₃]
  | let_ x e₁ e₂ ih₁ ih₂ =>
    intro Γ n u τ' hΓ h
    obtain ⟨τ₁', h₁, h₂⟩ := hasType_let_iff.mp h
    obtain ⟨s₁, τ₁, n₁, r₁, hW₁, hsr₁, hτ₁⟩ := ih₁ hΓ h₁
    obtain ⟨hle₁, hτ₁b, hs₁b⟩ := W_fresh hΓ hW₁
    have hΓ₁ := Ctx.ftv_subst_below hΓ hs₁b
    have hΓ' : ∀ z ∈ Ctx.ftv ((x, gen (Γ.subst s₁) τ₁) :: Γ.subst s₁), z < n₁ := by
      intro z hz
      rcases Finset.mem_union.mp (Ctx.ftv_cons_subset _ _ _ hz) with hz | hz
      · exact hΓ₁ z (vars_gen_subset_ftv _ _ hz)
      · exact hΓ₁ z hz
    have hagree := Ctx.lookup_subst_eq_of_agree hΓ hsr₁
    have h₂' : HasType (Ctx.subst r₁ ((x, gen (Γ.subst s₁) τ₁) :: Γ.subst s₁)) e₂ τ' := by
      show HasType ((x, (gen (Γ.subst s₁) τ₁).substTy r₁) :: (Γ.subst s₁).subst r₁) e₂ τ'
      refine h₂.mono ((Ctx.MoreGeneral.of_lookup_eq hagree).cons x ?_)
      have := substTy_gen_moreGeneral (Γ.subst s₁) τ₁ r₁
      rwa [gen_congr (Ctx.ftv_congr hagree), ← hτ₁] at this
    obtain ⟨s₂, τ₂, n₂, r₂, hW₂, hsr₂, hτ₂⟩ := ih₂ hΓ' h₂'
    obtain ⟨-, -, hs₂b⟩ := W_fresh hΓ' hW₂
    refine ⟨s₁ ≫ s₂, τ₂, n₂, r₂, by simp [W, hW₁, hW₂], fun y hy ↦ ?_, hτ₂⟩
    rw [hsr₁ y hy, comp, subst_subst]
    exact subst_congr fun z hz ↦ hsr₂ z (hs₁b y hy z hz)

/-! ### Principal types for closed expressions -/

/-- **Completeness of type inference for closed expressions.** If an expression $e$ has a
monotype $\tau'$ in the empty context, then type inference succeeds on $e$ and returns a
monotype $\tau$ of which $\tau'$ is a substitution instance: $\tau' = r(\tau)$ for some type
substitution $r$. -/
theorem infer_complete {e : Expr} {τ' : Ty B} (h : HasType [] e τ') :
    ∃ τ, infer e = some τ ∧ ∃ r, τ' = τ.subst r := by
  obtain ⟨s, τ, n', r, hW, -, hτ⟩ := W_complete (Γ := []) (n := 0) (u := Term.var)
    (by simp [Ctx.ftv]) (by simpa [Ctx.subst] using h)
  exact ⟨τ, by simp [infer, hW], r, hτ⟩

/-- **Type inference succeeds exactly on typable closed expressions.** Type inference succeeds
on an expression $e$ if and only if $e$ has some monotype in the empty context. -/
theorem infer_isSome_iff {e : Expr} :
    (infer (B := B) e).isSome ↔ ∃ τ : Ty B, HasType ([] : Ctx B) e τ := by
  constructor
  · intro h
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp h
    exact ⟨τ, hasType_of_infer_eq_some hτ⟩
  · rintro ⟨τ', h⟩
    obtain ⟨τ, hτ, -⟩ := infer_complete h
    simp [hτ]

/-- **Principal types**: the inferred type of a closed expression is one of its types, and
every type of it is an instance of the inferred one. -/
theorem infer_principal {e : Expr} {τ : Ty B} (h : infer e = some τ) :
    HasType [] e τ ∧ ∀ τ', HasType [] e τ' → ∃ r, τ' = τ.subst r := by
  refine ⟨hasType_of_infer_eq_some h, fun τ' h' ↦ ?_⟩
  obtain ⟨τ₀, hτ₀, r, hr⟩ := infer_complete h'
  rw [h, Option.some.injEq] at hτ₀
  exact ⟨r, hτ₀ ▸ hr⟩

end Cslib.HindleyMilner
