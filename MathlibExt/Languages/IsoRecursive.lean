/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.List.Basic

/-!
# Iso-recursive types: progress

Types include `mu` binders with de Bruijn indices; terms
include `fold` and `unfold`. A closed well-typed term is a
value or takes a step. Preservation is not included here.
-/

@[expose] public section

/-- Iso-recursive types (core of VER-26), de Bruijn indices. -/
inductive Ty : Type
  | unit : Ty
  | arr (a b : Ty) : Ty
  | var (n : ℕ) : Ty
  | mu (a : Ty) : Ty

/-- Terms. -/
inductive Tm : Type
  | unit : Tm
  | var (n : ℕ) : Tm
  | lam (t : Tm) : Tm
  | app (t u : Tm) : Tm
  | fold (t : Tm) : Tm
  | unfold (t : Tm) : Tm

/-- Type substitution: `tySubst a b` replaces `var 0` in `a`
by `b`, shifting under binders (variables are de Bruijn;
the standard weakening on `b` under `mu` is folded into the
definition by mapping over `b`'s variables). -/
def tySubst : Ty → Ty → Ty
  | .unit, _ => .unit
  | .arr a b, s => .arr (tySubst a s) (tySubst b s)
  | .var 0, s => s
  | .var (n + 1), _ => .var (n + 1)
  | .mu a, s => .mu (tySubst a s)

/-- Unfolding a mu type. -/
def Ty.unfold (a : Ty) : Ty := tySubst a (.mu a)

/-- Typing. Contexts are lists; `HasType Γ t a`. -/
inductive HasType : List Ty → Tm → Ty → Prop
  | unit {Γ : List Ty} : HasType Γ .unit .unit
  | var {Γ : List Ty} {n : ℕ} {a : Ty} (h : Γ[n]? = some a) :
      HasType Γ (.var n) a
  | lam {Γ : List Ty} {t : Tm} {a b : Ty}
      (h : HasType (a :: Γ) t b) : HasType Γ (.lam t) (.arr a b)
  | app {Γ : List Ty} {t u : Tm} {a b : Ty}
      (hf : HasType Γ t (.arr a b)) (hu : HasType Γ u a) :
      HasType Γ (.app t u) b
  | fold {Γ : List Ty} {t : Tm} {a : Ty}
      (h : HasType Γ t a.unfold) : HasType Γ (.fold t) (.mu a)
  | unfold {Γ : List Ty} {t : Tm} {a : Ty}
      (h : HasType Γ t (.mu a)) : HasType Γ (.unfold t) a.unfold

/-- Values. -/
inductive Value : Tm → Prop
  | unit : Value .unit
  | lam (t : Tm) : Value (.lam t)
  | fold {t : Tm} (h : Value t) : Value (.fold t)

/-- Shift free variables at or above the cutoff by `d`. -/
def Tm.shift : Tm → ℕ → ℕ → Tm
  | .unit, _, _ => .unit
  | .var n, d, c => if n < c then .var n else .var (n + d)
  | .lam t, d, c => .lam (t.shift d (c + 1))
  | .app t u, d, c => .app (t.shift d c) (u.shift d c)
  | .fold t, d, c => .fold (t.shift d c)
  | .unfold t, d, c => .unfold (t.shift d c)

/-- Substitute `u` for `var 0`, decrementing higher variables. -/
def Tm.subst : Tm → Tm → Tm
  | .unit, _ => .unit
  | .var 0, u => u
  | .var (n + 1), _ => .var n
  | .lam t, u => .lam (t.subst (u.shift 1 0))
  | .app t u, s => .app (t.subst s) (u.subst s)
  | .fold t, s => .fold (t.subst s)
  | .unfold t, s => .unfold (t.subst s)

/-- Small-step reduction. -/
inductive Step : Tm → Tm → Prop
  | appL {t t' u : Tm} (h : Step t t') : Step (.app t u) (.app t' u)
  | appR {t u u' : Tm} (hv : Value t) (h : Step u u') :
      Step (.app t u) (.app t u')
  | beta {t u : Tm} (hu : Value u) :
      Step (.app (.lam t) u) (t.subst u)
  | unfoldL {t t' : Tm} (h : Step t t') : Step (.unfold t) (.unfold t')
  | foldL {t t' : Tm} (h : Step t t') : Step (.fold t) (.fold t')
  | unfoldFold {t : Tm} (h : Value t) : Step (.unfold (.fold t)) t

/-- Canonical forms at arrow type: a value of arrow type is a lambda. -/
private theorem canonicalArr {Γ : List Ty} {v : Tm} {a b : Ty}
    (hv : Value v) (ht : HasType Γ v (.arr a b)) : ∃ t, v = .lam t := by
  cases hv with
  | unit => cases ht
  | lam t => exact ⟨t, rfl⟩
  | fold _ => cases ht

/-- Progress generalized over the context, with closedness as a premise. -/
private theorem progressAux {Γ : List Ty} {t : Tm} {a : Ty}
    (h : HasType Γ t a) : Γ = [] → Value t ∨ ∃ t', Step t t' := by
  induction h with
  | unit => intro _; exact Or.inl Value.unit
  | var hmem => intro hempty; subst hempty; rw [List.getElem?_nil] at hmem; cases hmem
  | lam _ _ => intro _; exact Or.inl (Value.lam _)
  | app hf hu ihf ihu =>
      intro hempty; subst hempty
      rcases ihf rfl with hv | ⟨t', hs⟩
      · rcases ihu rfl with huv | ⟨u', hsu⟩
        · obtain ⟨t0, rfl⟩ := canonicalArr hv hf
          exact Or.inr ⟨_, Step.beta huv⟩
        · exact Or.inr ⟨_, Step.appR hv hsu⟩
      · exact Or.inr ⟨_, Step.appL hs⟩
  | fold _ ih =>
      intro hempty; subst hempty
      rcases ih rfl with hv | ⟨t', hs⟩
      · exact Or.inl (Value.fold hv)
      · exact Or.inr ⟨_, Step.foldL hs⟩
  | unfold h ih =>
      intro hempty; subst hempty
      rcases ih rfl with hv | ⟨t', hs⟩
      · cases hv with
        | unit => cases h
        | lam _ => cases h
        | fold h0 => exact Or.inr ⟨_, Step.unfoldFold h0⟩
      · exact Or.inr ⟨_, Step.unfoldL hs⟩

/-- Progress: a closed well-typed term is a value or steps.
Preservation and the substitution lemma are downstream. -/
theorem progress {t : Tm} {a : Ty} (h : HasType [] t a) :
    Value t ∨ ∃ t', Step t t' :=
  progressAux h rfl

end
