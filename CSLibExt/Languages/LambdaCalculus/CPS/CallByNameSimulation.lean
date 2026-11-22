/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Operational correctness of the call-by-name CPS translation
-/
module

public import CSLibExt.Languages.LambdaCalculus.CPS.CallByName
public import CSLibExt.Languages.LambdaCalculus.CPS.Simulation

/-!
# Operational correctness of the call-by-name CPS translation

Plotkin's simulation theorem for the call-by-name translation (*Call-by-name,
call-by-value and the λ-calculus*, TCS 1, 1975), in big-step form, for the
typed translation `cbn` of `CallByName.lean`.

`EvalN` is call-by-name big-step evaluation of the simply typed lambda
calculus: a β-redex is contracted without evaluating its argument. For a
closed program `M` with `M ⇓ₙ λx. N` and every continuation value `K`, the
translated program `⟦M⟧ K`, run under the call-by-value semantics `Stlc.Eval`,
evaluates to `w` exactly when `K (λx. ⟦N⟧)` does (`cbn_simulation`). So
call-by-value evaluation of the translation simulates call-by-name evaluation
of the source. The induction proves the general form `cbn_evalN`: if
`M ⇓ₙ V`, then `⟦M⟧ K` and `⟦V⟧ K` have the same results.

The proof needs the translation to commute with renaming (`cbn_rename`) and
with substitution (`cbn_subst`, `cbn_instantiate`); unlike the call-by-value
case, a variable stands for a computation, so substituting a term `a` for a
variable substitutes its translation `⟦a⟧` and no value restriction is needed.
Closed translated terms are values (`cbn_value`), which is what lets the
call-by-value target pass an argument computation unevaluated.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.CPS

open scoped CslibStlc

universe u

variable {Base : Type u}

/-- Call-by-name big-step evaluation: evaluate the function to an abstraction
and evaluate the body instantiated with the unevaluated argument. -/
inductive EvalN {Γ : List (Ty Base)} : {A : Ty Base} → Tm Γ A → Tm Γ A → Prop
  | lam {A B : Ty Base} (body : Tm (A :: Γ) B) : EvalN (.lam body) (.lam body)
  | app {A B : Ty Base} {f : Tm Γ (A ⇒ B)} {a : Tm Γ A} {body : Tm (A :: Γ) B}
      {v : Tm Γ B} (hf : EvalN f (.lam body)) (hb : EvalN (Tm.instantiate body a) v) :
      EvalN (.app f a) v

variable (R : Ty Base)

/-- A renaming of source contexts, transported to the translated contexts. -/
def cbnRen : {Γ Δ : List (Ty Base)} → Ren Γ Δ →
    Ren (Γ.map (cbnComp R)) (Δ.map (cbnComp R))
  | [], _, _, _, x => nomatch x
  | _ :: _, _, ρ, _, .zero => cbnVar R (ρ .zero)
  | _ :: _, _, ρ, _, .succ y => cbnRen (fun x => ρ (.succ x)) y

variable {R}
variable {Γ Δ : List (Ty Base)} {A B : Ty Base}

@[simp] theorem cbnRen_cbnVar (ρ : Ren Γ Δ) (x : Var Γ A) :
    cbnRen R ρ (cbnVar R x) = cbnVar R (ρ x) := by
  induction x generalizing Δ with
  | zero => rfl
  | succ x ih => exact ih (fun y => ρ (.succ y))

theorem cbnRen_succ (ρ : Ren Γ Δ) {T : Ty Base} (y : Var (Γ.map (cbnComp R)) T) :
    cbnRen R (fun x => (ρ x).succ (B := B)) y = (cbnRen R ρ y).succ := by
  induction Γ generalizing Δ with
  | nil => exact nomatch y
  | cons C Γ ih =>
      cases y with
      | zero => rfl
      | succ y => exact ih (fun x => ρ (.succ x)) y

theorem cbnRen_id {T : Ty Base} (y : Var (Γ.map (cbnComp R)) T) :
    cbnRen R (Var.id : Ren Γ Γ) y = y := by
  induction Γ with
  | nil => exact nomatch y
  | cons C Γ ih =>
      cases y with
      | zero => rfl
      | succ y =>
          change cbnRen R (fun x => (Var.id x).succ (B := C)) y = _
          rw [cbnRen_succ]
          exact congrArg Var.succ (ih y)

theorem cbnRen_lift (ρ : Ren Γ Δ) {T : Ty Base} (y : Var ((A :: Γ).map (cbnComp R)) T) :
    cbnRen R (Var.lift ρ) y = Var.lift (cbnRen R ρ) y := by
  cases y with
  | zero => rfl
  | succ y => exact cbnRen_succ ρ y

/-- The translation commutes with renaming. -/
theorem cbn_rename (ρ : Ren Γ Δ) (t : Tm Γ A) :
    cbn R (Tm.rename ρ t) = Tm.rename (cbnRen R ρ) (cbn R t) := by
  induction t generalizing Δ with
  | var x => simp
  | @lam A B Γ body ih =>
      simp only [Tm.rename_lam, cbn_lam, Tm.rename_app, Tm.rename_var, Var.lift_zero, ih]
      refine congrArg (fun t => Tm.lam (Tm.app (Tm.var Var.zero) t)) ?_
      refine Eq.trans ?_ (Tm.rename_weaken (cbnRen R ρ)
        (Tm.lam (cbn R body) : Tm (Γ.map (cbnComp R)) (cbnTy R (A ⇒ B)))).symm
      exact congrArg Tm.weaken (congrArg Tm.lam (Tm.rename_congr (fun y => cbnRen_lift ρ y) _))
  | app f a ihf iha =>
      simp only [Tm.rename_lam, cbn_app, Tm.rename_app, Tm.rename_var, ihf, iha]
      rw [Tm.rename_weaken, Tm.rename_weaken, Tm.rename_weaken]
      rfl

theorem cbnRen_weaken {T : Ty Base} (y : Var (Γ.map (cbnComp R)) T) :
    cbnRen R (fun x => Var.succ (B := B) x) y = y.succ :=
  (cbnRen_succ Var.id y).trans (congrArg Var.succ (cbnRen_id y))

/-- Weakening commutes with the translation. -/
theorem cbn_weaken (t : Tm Γ A) :
    cbn R (Tm.weaken (B := B) t) = Tm.weaken (cbn R t) := by
  rw [Tm.weaken, cbn_rename, Tm.weaken]
  exact Tm.rename_congr (fun y => cbnRen_weaken y) _

/-- The translation commutes with substitution: if `τ` maps each translated
variable to the translation of the term `σ` substitutes for it, then
`⟦M[σ]⟧ = ⟦M⟧[τ]`. -/
theorem cbn_subst (t : Tm Γ A) {σ : Sub Γ Δ}
    {τ : Sub (Γ.map (cbnComp R)) (Δ.map (cbnComp R))}
    (hτ : ∀ {B} (x : Var Γ B), τ (cbnVar R x) = cbn R (σ x)) :
    cbn R (Tm.subst σ t) = Tm.subst τ (cbn R t) := by
  induction t generalizing Δ with
  | var x => exact (hτ x).symm
  | @lam A B Γ body ih =>
      simp only [Tm.subst_lam, cbn_lam, Tm.subst_app, Tm.subst_var, Sub.lift_zero]
      refine congrArg (fun t => Tm.lam (Tm.app (Tm.var Var.zero) t)) ?_
      refine Eq.trans ?_ (Tm.subst_lift_weaken τ
        (Tm.lam (cbn R body) : Tm (Γ.map (cbnComp R)) (cbnTy R (A ⇒ B)))).symm
      have hlift : ∀ {C} (x : Var (A :: Γ) C),
          Sub.lift τ (cbnVar R x) = cbn R (Sub.lift σ x) := by
        intro C x
        cases x with
        | zero => rfl
        | succ x =>
            simp only [cbnVar_succ, Sub.lift_succ]
            rw [hτ x, cbn_weaken]
      exact congrArg Tm.weaken (congrArg Tm.lam (ih (Δ := A :: Δ)
        (τ := (Sub.lift (A := cbnComp R A) τ :
          Sub ((A :: Γ).map (cbnComp R)) ((A :: Δ).map (cbnComp R)))) hlift))
  | app f a ihf iha =>
      simp only [Tm.subst_lam, cbn_app, Tm.subst_app, Tm.subst_var, ihf hτ, iha hτ]
      rw [Tm.subst_lift_weaken, Tm.subst_lift_weaken, Tm.subst_lift_weaken]
      rfl

/-- Instantiation commutes with the translation. -/
theorem cbn_instantiate (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    cbn R (Tm.instantiate body a) = Tm.instantiate (cbn R body) (cbn R a) := by
  refine cbn_subst body fun x => ?_
  cases x with
  | zero => rfl
  | succ x => rfl

/-- The translation of a closed term is a value. -/
theorem cbn_value : (t : Tm [] A) → Value (cbn R t)
  | .var x => nomatch x
  | .lam _ => .lam _
  | .app _ _ => .lam _

section Instantiate

variable {Ξ : List (Ty Base)} {W V Z : Ty Base}

/-! The administrative reductions of the translation of an application, at
generic types. -/

theorem instantiate_cbnApp₁ (F : Tm Ξ (((W ⇒ ((V ⇒ Z) ⇒ Z)) ⇒ Z) ⇒ Z)) (N : Tm Ξ W)
    (K : Tm Ξ (V ⇒ Z)) :
    Tm.instantiate (.app (Tm.weaken F)
        (.lam (.app (.app (.var .zero) (Tm.weaken (Tm.weaken N))) (.var (.succ .zero))))) K =
      .app F (.lam (.app (.app (.var .zero) (Tm.weaken N)) (Tm.weaken K))) := by
  simp [Tm.instantiate, Tm.subst_lift_weaken]

theorem instantiate_cbnApp₂ (N : Tm Ξ W) (K : Tm Ξ (V ⇒ Z))
    (P : Tm Ξ (W ⇒ ((V ⇒ Z) ⇒ Z))) :
    Tm.instantiate (.app (.app (.var .zero) (Tm.weaken N)) (Tm.weaken K)) P =
      .app (.app P N) K := by
  simp [Tm.instantiate]

end Instantiate

/-- The translation of an abstraction passes `λx. ⟦N⟧` to its continuation. -/
theorem eval_cbn_lam_iff (body : Tm (A :: Γ) B)
    {K : Tm (Γ.map (cbnComp R)) (cbnTy R (A ⇒ B) ⇒ R)} (hK : Value K) (w : Tm _ R) :
    Eval (.app (cbn R (.lam body)) K) w ↔ Eval (.app K (.lam (cbn R body))) w :=
  (eval_app_lam_iff hK).trans
    (iff_of_eq (congrArg (Eval · w) (instantiate_ret (Tm.lam (cbn R body)) K)))

/-- Call-by-name evaluation is preserved by the translation: if `M ⇓ₙ V` for
closed `M`, then `⟦M⟧ K` and `⟦V⟧ K` have the same call-by-value results for
every continuation value `K`. -/
theorem cbn_evalN {T : Ty Base} {M V : Tm [] T} (h : EvalN M V)
    (K : Tm ([].map (cbnComp R)) (cbnTy R T ⇒ R)) (hK : Value K) (w : Tm [] R) :
    Eval (.app (cbn R M) K) w ↔ Eval (.app (cbn R V) K) w := by
  induction h generalizing w with
  | lam body => exact Iff.rfl
  | @app A' B' f a body' v hf hb ihf ihb =>
      refine (eval_app_lam_iff hK).trans ?_
      refine (iff_of_eq (congrArg (Eval · w) (instantiate_cbnApp₁ (cbn R f) (cbn R a) K))).trans ?_
      refine (ihf _ (.lam _) w).trans ?_
      refine (eval_cbn_lam_iff body' (.lam _) w).trans ?_
      refine (eval_app_lam_iff (.lam _)).trans ?_
      refine (iff_of_eq (congrArg (Eval · w)
        (instantiate_cbnApp₂ (cbn R a) K (Tm.lam (cbn R body'))))).trans ?_
      refine (eval_app_congr_fun (fun u => eval_app_lam_iff (cbn_value a))).trans ?_
      refine (iff_of_eq (congrArg (fun t => Eval (.app t K) w)
        (cbn_instantiate body' a).symm)).trans ?_
      exact ihb K hK w

/-- Plotkin's simulation theorem for the call-by-name translation, big-step
form: if the closed program `M` evaluates by name to `λx. N`, then for every
continuation value `K`, `⟦M⟧ K` evaluates by value to `w` exactly when
`K (λx. ⟦N⟧)` does. -/
theorem cbn_simulation {M : Tm [] (A ⇒ B)} {body : Tm [A] B} (h : EvalN M (.lam body))
    (K : Tm ([].map (cbnComp R)) (cbnTy R (A ⇒ B) ⇒ R)) (hK : Value K) (w : Tm [] R) :
    Eval (.app (cbn R M) K) w ↔ Eval (.app K (.lam (cbn R body))) w :=
  (cbn_evalN h K hK w).trans (eval_cbn_lam_iff body hK w)

end Cslib.Languages.LambdaCalculus.Stlc.CPS
