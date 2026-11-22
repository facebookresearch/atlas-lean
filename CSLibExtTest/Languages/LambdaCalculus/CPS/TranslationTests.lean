/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.CPS.Translation

/-!
# Tests for the call-by-value CPS translation

* The type translation at a function type; the constructor equations of
  `cps` used for rewriting.
* `x : ℕ ⊢ (λy. y) x` and the higher-order `f : ℕ → ℕ, x : ℕ ⊢ f (f x)`:
  their CPS translations, run with the identity continuation in related
  environments, compute the direct-style values. Each is checked twice: by
  evaluation (`rfl`) and through `cps_denote_base_id`.
* A CPS environment entry that is not related to the direct-style one breaks
  the conclusion, so the environment hypothesis of `cps_correct` is needed.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.CPS.Tests

open scoped CslibStlc

/-- The single base type, interpreted as `ℕ`. -/
abbrev N : Ty Unit := .base ()

/-- Interpretation of the base type. -/
abbrev I : Unit → Type := fun _ => Nat

example (R : Ty Unit) : cpsTy R (N ⇒ N) = (N ⇒ ((N ⇒ R) ⇒ R)) := rfl

/-- The constructor equations compute the translation of a variable and of an
identity function. -/
example (R : Ty Unit) :
    cps R (.var (.zero : Var [N] N)) = .lam (.app (.var .zero) (.var (.succ .zero))) := by
  rw [cps_var, cpsVar_zero]

example (R : Ty Unit) :
    cps R (.lam (.var .zero) : Tm [] (N ⇒ N)) =
      .lam (.app (.var .zero)
        (Tm.weaken (.lam (.lam (.app (.var .zero) (.var (.succ .zero))))))) := by
  rw [cps_lam, cps_var, cpsVar_zero]

/-- `x : N ⊢ (λy : N. y) x : N`. -/
def idApp : Tm [N] N := .app (.lam (.var .zero)) (.var .zero)

/-- The empty environment. -/
def ε : Env I [] := fun x => nomatch x

/-- The empty environments are related. -/
theorem εRel : EnvRel N ε ε := fun x => nomatch x

/-- The environment `x ↦ n`, for both the source and the CPS context. -/
def env (n : Nat) : Env I [N] := Env.cons (I := I) (A := N) n ε

theorem envRel (n : Nat) : EnvRel N (env n) (env n) :=
  EnvRel.cons (I := I) (A := N) N εRel (a := (n : Nat)) (a' := (n : Nat)) rfl

example : Tm.denote I (cps N idApp) (env 5) id = (5 : Nat) := rfl

example (n : Nat) : Tm.denote I (cps N idApp) (env n) id = (n : Nat) :=
  cps_denote_base_id idApp (envRel n)

/-- `f : N → N, x : N ⊢ f (f x) : N`. -/
def twice : Tm [N ⇒ N, N] N := .app (.var .zero) (.app (.var .zero) (.var (.succ .zero)))

/-- Source environment: `f ↦ succ`, `x ↦ n`. -/
def twiceEnv (n : Nat) : Env I [N ⇒ N, N] :=
  Env.cons (I := I) (A := N ⇒ N) Nat.succ (Env.cons (I := I) (A := N) n ε)

/-- The CPS form of `succ`: pass `a + 1` to the continuation. -/
def succCPS : Ty.denote I (cpsTy N (N ⇒ N)) := fun (a : Nat) (k : Nat → Nat) => k (a + 1)

/-- CPS environment: `f ↦ succCPS`, `x ↦ n`. -/
def twiceEnv' (n : Nat) : Env I ([N ⇒ N, N].map (cpsTy N)) :=
  Env.cons (I := I) (A := cpsTy N (N ⇒ N)) succCPS (Env.cons (I := I) (A := N) n ε)

theorem rel_succ : Rel N I (N ⇒ N) Nat.succ succCPS := by
  refine (rel_arr N N N _ _).mpr ?_
  show ∀ a a' : Nat, a = a' →
    ∃ b' : Nat, Nat.succ a = b' ∧ ∀ k : Nat → Nat, succCPS a' k = k b'
  rintro a a' rfl
  exact ⟨a + 1, rfl, fun _ => rfl⟩

theorem twiceEnvRel (n : Nat) : EnvRel N (twiceEnv n) (twiceEnv' n) :=
  EnvRel.cons (I := I) N
    (EnvRel.cons (I := I) (A := N) N εRel (a := (n : Nat)) (a' := (n : Nat)) rfl)
    rel_succ

example : Tm.denote I (cps N twice) (twiceEnv' 3) id = (5 : Nat) := rfl

example (n : Nat) : Tm.denote I (cps N twice) (twiceEnv' n) id = (n + 2 : Nat) :=
  cps_denote_base_id twice (twiceEnvRel n)

/-- An unrelated CPS entry for `f` (it ignores its continuation) changes the
result: the environment hypothesis of `cps_correct` is not removable. -/
def badEnv' (n : Nat) : Env I ([N ⇒ N, N].map (cpsTy N)) :=
  Env.cons (I := I) (A := cpsTy N (N ⇒ N)) (fun (_ : Nat) (_ : Nat → Nat) => (0 : Nat))
    (Env.cons (I := I) (A := N) n ε)

example : Tm.denote I (cps N twice) (badEnv' 3) id = (0 : Nat) := rfl

example : Tm.denote I twice (twiceEnv 3) = (5 : Nat) := rfl

end Cslib.Languages.LambdaCalculus.Stlc.CPS.Tests
