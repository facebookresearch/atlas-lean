/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Call-by-value CPS translation of the simply typed lambda calculus
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Denotational

/-!
# Call-by-value CPS translation and its denotational correctness

The call-by-value continuation-passing-style translation of Plotkin
(*Call-by-name, call-by-value and the λ-calculus*, TCS 1, 1975), in the
typed form of Meyer and Wand (*Continuation semantics in typed
lambda-calculi*, Logics of Programs 1985), on the intrinsically typed de
Bruijn STLC of `../DeBruijn/Stlc/`. For a fixed answer type `R`:

* types: `⟦b⟧ = b` and `⟦A → B⟧ = ⟦A⟧ → (⟦B⟧ → R) → R`; a term of type `A`
  becomes a computation of type `(⟦A⟧ → R) → R` (`compTy`);
* terms: `⟦x⟧ = λk. k x`, `⟦λx. M⟧ = λk. k (λx. ⟦M⟧)`, and
  `⟦M N⟧ = λk. ⟦M⟧ (λm. ⟦N⟧ (λn. m n k))`.

Because terms are intrinsically typed, `cps` is type preserving by
construction: it maps `Tm Γ A` to `Tm (Γ.map (cpsTy R)) (compTy R A)`.

Correctness is the Meyer–Wand theorem for the set-theoretic semantics
(`Tm.denote`): for related environments, the denotation of `⟦M⟧` applied to
any continuation `k` is `k v'` for a value `v'` related to the denotation of
`M`, where `Rel` is the logical relation that is equality at base types
(`cps_correct`). For terms of base type this says that running the
translation with continuation `k` returns `k` of the original value
(`cps_denote_base`), and with the identity continuation it returns the
original value (`cps_denote_base_id`). Pure STLC has no closed terms of base
type, so these are stated for open terms in related environments.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.CPS

open scoped CslibStlc

universe u v

variable {Base : Type u}

/-- The call-by-value CPS translation of types, for answer type `R`. -/
def cpsTy (R : Ty Base) : Ty Base → Ty Base
  | .base b => .base b
  | .arr A B => cpsTy R A ⇒ ((cpsTy R B ⇒ R) ⇒ R)

/-- The type of CPS computations returning a value of type `A`:
`(⟦A⟧ → R) → R`. -/
abbrev compTy (R : Ty Base) (A : Ty Base) : Ty Base :=
  (cpsTy R A ⇒ R) ⇒ R

@[simp] theorem cpsTy_base (R : Ty Base) (b : Base) : cpsTy R (.base b) = .base b := rfl

@[simp] theorem cpsTy_arr (R A B : Ty Base) :
    cpsTy R (A ⇒ B) = cpsTy R A ⇒ compTy R B := rfl

variable (R : Ty Base)

/-- The translation of a variable: the same position in the translated
context. -/
def cpsVar : {Γ : List (Ty Base)} → {A : Ty Base} →
    Var Γ A → Var (Γ.map (cpsTy R)) (cpsTy R A)
  | _, _, .zero => .zero
  | _, _, .succ x => .succ (cpsVar x)

/-- The call-by-value CPS translation of terms. -/
def cps : {Γ : List (Ty Base)} → {A : Ty Base} →
    Tm Γ A → Tm (Γ.map (cpsTy R)) (compTy R A)
  | _, _, .var x => .lam (.app (.var .zero) (.var (.succ (cpsVar R x))))
  | _, _, .lam body => .lam (.app (.var .zero) (Tm.weaken (.lam (cps body))))
  | _, _, .app f a =>
      .lam (.app (Tm.weaken (cps f))
        (.lam (.app (Tm.weaken (Tm.weaken (cps a)))
          (.lam (.app (.app (.var (.succ .zero)) (.var .zero))
            (.var (.succ (.succ .zero))))))))

section Equations

variable {Γ : List (Ty Base)} {A B : Ty Base}

@[simp] theorem cpsVar_zero : cpsVar R (.zero : Var (A :: Γ) A) = .zero := rfl

@[simp] theorem cpsVar_succ (x : Var Γ A) :
    cpsVar R (.succ x : Var (B :: Γ) A) = .succ (cpsVar R x) := rfl

@[simp] theorem cps_var (x : Var Γ A) :
    cps R (.var x) = .lam (.app (.var .zero) (.var (.succ (cpsVar R x)))) := rfl

@[simp] theorem cps_lam (body : Tm (A :: Γ) B) :
    cps R (.lam body) =
      .lam (.app (.var .zero) (Tm.weaken (.lam (cps R body)))) := rfl

@[simp] theorem cps_app (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) :
    cps R (.app f a) =
      .lam (.app (Tm.weaken (cps R f))
        (.lam (.app (Tm.weaken (Tm.weaken (cps R a)))
          (.lam (.app (.app (.var (.succ .zero)) (.var .zero))
            (.var (.succ (.succ .zero)))))))) := rfl

end Equations

variable {I : Base → Type v}

/-- The logical relation between direct-style values of type `A` and values of
the CPS type `⟦A⟧`: equality at base types; at function types, related
arguments give a CPS function that passes a related result to every
continuation. -/
def Rel (I : Base → Type v) : (A : Ty Base) → Ty.denote I A → Ty.denote I (cpsTy R A) → Prop
  | .base _, a, a' => a = a'
  | .arr A B, f, f' => ∀ a a', Rel I A a a' →
      ∃ b', Rel I B (f a) b' ∧ ∀ k, f' a' k = k b'

@[simp] theorem rel_base (b : Base) (a : I b) (a' : Ty.denote I (cpsTy R (.base b))) :
    Rel R I (.base b) a a' ↔ a = a' := Iff.rfl

theorem rel_arr (A B : Ty Base) (f : Ty.denote I (A ⇒ B))
    (f' : Ty.denote I (cpsTy R (A ⇒ B))) :
    Rel R I (A ⇒ B) f f' ↔ ∀ a a', Rel R I A a a' →
      ∃ b', Rel R I B (f a) b' ∧ ∀ k, f' a' k = k b' := Iff.rfl

/-- Environments related variable by variable. -/
def EnvRel {Γ : List (Ty Base)} (η : Env I Γ) (η' : Env I (Γ.map (cpsTy R))) : Prop :=
  ∀ {A} (x : Var Γ A), Rel R I A (η x) (η' (cpsVar R x))

theorem EnvRel.cons {Γ : List (Ty Base)} {A : Ty Base} {η : Env I Γ}
    {η' : Env I (Γ.map (cpsTy R))} (hη : EnvRel R η η') {a : Ty.denote I A}
    {a' : Ty.denote I (cpsTy R A)} (ha : Rel R I A a a') :
    EnvRel R (Env.cons a η) (Env.cons (Γ := Γ.map (cpsTy R)) a' η') := by
  intro B x
  cases x with
  | zero => exact ha
  | succ x => exact hη x

/-- Denotational correctness of the CPS translation (Meyer–Wand): in related
environments, the translation of `t` applied to any continuation `k` is `k v'`
for a single value `v'` related to the denotation of `t`. -/
theorem cps_correct {Γ : List (Ty Base)} {A : Ty Base} (t : Tm Γ A) {η : Env I Γ}
    {η' : Env I (Γ.map (cpsTy R))} (hη : EnvRel R η η') :
    ∃ v', Rel R I A (Tm.denote I t η) v' ∧
      ∀ k, Tm.denote I (cps R t) η' k = k v' := by
  induction t with
  | var x => exact ⟨η' (cpsVar R x), hη x, fun _ => rfl⟩
  | @lam A B Γ body ih =>
      refine ⟨Tm.denote I (.lam (cps R body)) η', ?_, ?_⟩
      · intro a a' ha
        exact ih (hη.cons R ha)
      · intro k
        exact congrArg k (Tm.denote_weaken I (.lam (cps R body)) k η')
  | @app A B Γ f a ihf iha =>
      obtain ⟨f', hf, hfk⟩ := ihf hη
      obtain ⟨a', ha, hak⟩ := iha hη
      obtain ⟨b', hb, hbk⟩ := hf _ _ ha
      refine ⟨b', hb, fun k => ?_⟩
      have hwa : ∀ m : Ty.denote I (cpsTy R (A ⇒ B)),
          Tm.denote I (Tm.weaken (B := cpsTy R (A ⇒ B)) (Tm.weaken (B := cpsTy R B ⇒ R) (cps R a)))
            (Env.cons m (Env.cons k η')) = Tm.denote I (cps R a) η' := fun m =>
        (Tm.denote_weaken I _ m (Env.cons k η')).trans (Tm.denote_weaken I (cps R a) k η')
      have hstep : Tm.denote I (cps R (.app f a)) η' k =
          Tm.denote I (cps R f) η' (fun m => Tm.denote I (cps R a) η' (fun n => m n k)) := by
        refine (congrFun (Tm.denote_weaken I (cps R f) k η') _).trans ?_
        refine congrArg (Tm.denote I (cps R f) η') (funext fun m => ?_)
        exact congrFun (hwa m) _
      exact hstep.trans ((hfk _).trans ((hak _).trans (hbk k)))

/-- At a base type the relation is equality, so the CPS translation of a term
of base type passes exactly the term's value to the continuation. -/
theorem cps_denote_base {Γ : List (Ty Base)} {b : Base} (t : Tm Γ (.base b))
    {η : Env I Γ} {η' : Env I (Γ.map (cpsTy R))} (hη : EnvRel R η η')
    (k : Ty.denote I (cpsTy R (.base b) ⇒ R)) :
    Tm.denote I (cps R t) η' k = k (Tm.denote I t η) := by
  obtain ⟨v', hv, hk⟩ := cps_correct R t hη
  rw [hk k]
  exact congrArg k hv.symm

/-- With the answer type equal to the term's base type, running the CPS
translation with the identity continuation returns the term's value. -/
theorem cps_denote_base_id {Γ : List (Ty Base)} {b : Base} (t : Tm Γ (.base b))
    {η : Env I Γ} {η' : Env I (Γ.map (cpsTy (.base b)))} (hη : EnvRel (.base b) η η') :
    Tm.denote I (cps (.base b) t) η' id = Tm.denote I t η :=
  cps_denote_base (.base b) t hη id

end Cslib.Languages.LambdaCalculus.Stlc.CPS
