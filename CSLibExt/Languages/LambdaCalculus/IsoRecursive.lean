/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# Iso-recursive types: progress

The call-by-value lambda calculus with `unit`, function types and
iso-recursive types `μX. a` of Pierce, *Types and Programming Languages*
(MIT Press, 2002), Chapter 20: `fold` and `unfold` convert between `μX. a`
and its unfolding `[X ↦ μX. a] a`. Pierce annotates `fold` and `unfold`
with the recursive type; here they are unannotated.

Types and terms use de Bruijn indices. `Ty.subst` and `Tm.subst` substitute
for variable `0`, shift the substituted type or term under binders so that its
free variables are not captured, and lower the remaining free variables by
one.

The main result, `progress`, states that a closed well-typed term is a value
or takes a step. Preservation is not proved here.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.IsoRecursive

/-- Types with de Bruijn type variables; `mu a` binds variable `0` in `a`. -/
inductive Ty : Type
  /-- The unit type. -/
  | unit : Ty
  /-- Function types. -/
  | arr (a b : Ty) : Ty
  /-- A de Bruijn type variable. -/
  | var (n : ℕ) : Ty
  /-- The recursive type `μX. a`, binding `X` as variable `0` in `a`. -/
  | mu (a : Ty) : Ty
  deriving DecidableEq, Repr

/-- Terms with de Bruijn variables; `lam t` binds variable `0` in `t`. -/
inductive Tm : Type
  /-- The unit value. -/
  | unit : Tm
  /-- A de Bruijn variable. -/
  | var (n : ℕ) : Tm
  /-- Abstraction, binding variable `0` in its body. -/
  | lam (t : Tm) : Tm
  /-- Application. -/
  | app (t u : Tm) : Tm
  /-- Folding into a recursive type. -/
  | fold (t : Tm) : Tm
  /-- Unfolding out of a recursive type. -/
  | unfold (t : Tm) : Tm
  deriving DecidableEq, Repr

/-- `a.shift d c` adds `d` to every type variable of `a` at or above the
cutoff `c`. -/
def Ty.shift : Ty → ℕ → ℕ → Ty
  | .unit, _, _ => .unit
  | .arr a b, d, c => .arr (a.shift d c) (b.shift d c)
  | .var n, d, c => if n < c then .var n else .var (n + d)
  | .mu a, d, c => .mu (a.shift d (c + 1))

/-- `a.substAt k s` replaces type variable `k` of `a` by `s`, shifted past the
`k` binders it is placed under, and lowers the type variables above `k` by
one. Descending through `mu` increments `k`. -/
def Ty.substAt : Ty → ℕ → Ty → Ty
  | .unit, _, _ => .unit
  | .arr a b, k, s => .arr (a.substAt k s) (b.substAt k s)
  | .var n, k, s =>
      if n < k then .var n else if n = k then s.shift k 0 else .var (n - 1)
  | .mu a, k, s => .mu (a.substAt (k + 1) s)

/-- `a.subst s` substitutes `s` for type variable `0` of `a`, the variable
bound by an enclosing `mu`, and lowers the other free type variables. -/
def Ty.subst (a s : Ty) : Ty := a.substAt 0 s

/-- The unfolding `[X ↦ μX. a] a` of the recursive type `μX. a` with body
`a`. -/
def Ty.unfold (a : Ty) : Ty := a.subst (.mu a)

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

/-- `t.shift d c` adds `d` to every variable of `t` at or above the cutoff
`c`. -/
def Tm.shift : Tm → ℕ → ℕ → Tm
  | .unit, _, _ => .unit
  | .var n, d, c => if n < c then .var n else .var (n + d)
  | .lam t, d, c => .lam (t.shift d (c + 1))
  | .app t u, d, c => .app (t.shift d c) (u.shift d c)
  | .fold t, d, c => .fold (t.shift d c)
  | .unfold t, d, c => .unfold (t.shift d c)

/-- `t.substAt k u` replaces variable `k` of `t` by `u`, shifted past the `k`
binders it is placed under, and lowers the variables above `k` by one.
Descending through `lam` increments `k`. -/
def Tm.substAt : Tm → ℕ → Tm → Tm
  | .unit, _, _ => .unit
  | .var n, k, u =>
      if n < k then .var n else if n = k then u.shift k 0 else .var (n - 1)
  | .lam t, k, u => .lam (t.substAt (k + 1) u)
  | .app t t', k, u => .app (t.substAt k u) (t'.substAt k u)
  | .fold t, k, u => .fold (t.substAt k u)
  | .unfold t, k, u => .unfold (t.substAt k u)

/-- `t.subst u` substitutes `u` for variable `0` of `t`, the variable bound
by an enclosing `lam`, and lowers the other free variables: the result of
applying `lam t` to `u`. -/
def Tm.subst (t u : Tm) : Tm := t.substAt 0 u

/-- Call-by-value small-step reduction. -/
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

/-- Progress: a closed well-typed term is a value or takes a step. -/
theorem progress {t : Tm} {a : Ty} (h : HasType [] t a) :
    Value t ∨ ∃ t', Step t t' :=
  progressAux h rfl

end Cslib.Languages.LambdaCalculus.IsoRecursive
