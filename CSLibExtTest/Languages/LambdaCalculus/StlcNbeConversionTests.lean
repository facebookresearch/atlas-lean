/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeConversion

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.NbeConversionTests

open scoped CslibStlc

abbrev Atom := Ty.base (Base := Unit) ()

variable {Γ Δ Θ : List (Ty Unit)}

abbrev idBody : Tm [Atom] Atom := .var .zero

abbrev idTm : Tm [] (Atom ⇒ Atom) := .lam idBody

/-- The computational beta theorem reduces the closed identity redex. -/
example (a : Tm [] Atom) :
    normalizeTm (.app idTm a) = normalizeTm a := by
  simpa [idTm, idBody, Tm.instantiate] using normalizeTm_beta idBody a

/-- Eta expansion has the same computed representative as its function. -/
example (f : Tm [Atom] (Atom ⇒ Atom)) :
    normalizeTm (.lam (.app (Tm.weaken f) (.var .zero))) = normalizeTm f :=
  normalizeTm_eta f

/-- Root beta is a declarative beta-eta conversion. -/
example (body : Tm (Atom :: Γ) Atom) (a : Tm Γ Atom) :
    BetaEtaEq (.app (.lam body) a) (Tm.instantiate body a) :=
  .beta body a

/-- Compatible conversion reaches beta redexes below an application. -/
example (body : Tm (Atom :: Γ) (Atom ⇒ Atom)) (a b : Tm Γ Atom) :
    BetaEtaEq (.app (.app (.lam body) a) b)
      (.app (Tm.instantiate body a) b) :=
  (BetaEtaEq.beta body a).app_left b

/-- Typed contexts transport root beta conversion to arbitrary depth. -/
example (body : Tm (Atom :: Γ) Atom) (a : Tm Γ Atom)
    (C : TmCtx Γ Atom Δ Atom) :
    BetaEtaEq (C.plug (.app (.lam body) a))
      (C.plug (Tm.instantiate body a)) :=
  BetaEtaEq.context_beta C body a

/-- Renaming preserves declarative conversion. -/
example {t u : Tm Γ Atom} (h : BetaEtaEq t u) (ρ : Ren Γ Δ) :
    BetaEtaEq (Tm.rename ρ t) (Tm.rename ρ u) :=
  h.rename ρ

/-- Simultaneous substitution preserves declarative conversion. -/
example {t u : Tm Γ Atom} (h : BetaEtaEq t u) (σ : Sub Γ Δ) :
    BetaEtaEq (Tm.subst σ t) (Tm.subst σ u) :=
  h.subst σ

/-- Every declarative derivation is sound in every same-universe model. -/
example {t u : Tm Γ Atom} (h : BetaEtaEq t u) : ModelEq t u :=
  h.modelEq

/-- A root beta contraction is one directed compatible step. -/
example (body : Tm (Atom :: Γ) Atom) (a : Tm Γ Atom) :
    BetaEtaStep (.app (.lam body) a) (Tm.instantiate body a) :=
  .beta body a

/-- A contraction may occur in argument position. -/
example (f : Tm Γ (Atom ⇒ Atom)) (body : Tm (Atom :: Γ) Atom)
    (a : Tm Γ Atom) :
    BetaEtaStep (.app f (.app (.lam body) a))
      (.app f (Tm.instantiate body a)) :=
  .appArg f (.beta body a)

/-- Directed compatible reduction closes transitively. -/
example {t u v : Tm Γ Atom} (h₁ : BetaEtaStep t u)
    (h₂ : BetaEtaStep u v) : BetaEtaSteps t v :=
  (BetaEtaSteps.single h₁).step_right h₂

/-- Multi-step reduction is stable under typed contexts. -/
example {t u : Tm Γ Atom} (h : BetaEtaSteps t u)
    (C : TmCtx Γ Atom Δ Atom) :
    BetaEtaSteps (C.plug t) (C.plug u) :=
  h.context C

/-- Reducing both sides to one term supplies a declarative conversion. -/
example {t u v : Tm Γ Atom} (ht : BetaEtaSteps t v)
    (hu : BetaEtaSteps u v) : BetaEtaEq t u :=
  (show BetaEtaJoin t u from ⟨v, ht, hu⟩).betaEtaEq

/-- A directed step embeds as a forward zigzag edge. -/
example {t u : Tm Γ Atom} (h : BetaEtaStep t u) :
    BetaEtaZigzag t u :=
  BetaEtaZigzag.of_step h

/-- A directed step can also be traversed backwards. -/
example {t u : Tm Γ Atom} (h : BetaEtaStep t u) :
    BetaEtaZigzag u t :=
  BetaEtaZigzag.of_step_symm h

/-- Declarative conversion and explicit zigzags are interchangeable. -/
example {t u : Tm Γ Atom} : BetaEtaEq t u ↔ BetaEtaZigzag t u :=
  betaEtaEq_iff_zigzag

/-- Explicit conversion paths survive simultaneous substitution. -/
example {t u : Tm Γ Atom} (h : BetaEtaZigzag t u) (σ : Sub Γ Δ) :
    BetaEtaZigzag (Tm.subst σ t) (Tm.subst σ u) :=
  h.subst σ

/-- Pointwise paths are preserved while extending substitutions. -/
example {a b : Tm Δ Atom} {s t : Sub Γ Δ}
    (hab : BetaEtaZigzag a b) (hst : SubBetaEtaZigzag s t) :
    SubBetaEtaZigzag (Sub.cons a s) (Sub.cons b t) :=
  hst.cons hab

/-- Lifting pointwise substitution paths handles the bound variable
reflexively and weakens every free-variable path. -/
example {σ τ : Sub Γ Δ} (h : SubBetaEtaZigzag σ τ) :
    SubBetaEtaZigzag (Sub.lift (A := Atom) σ) (Sub.lift τ) :=
  h.lift

/-- Pointwise paths compose through substitution composition. -/
example {σ σ' : Sub Γ Δ} {τ τ' : Sub Δ Θ}
    (hσ : SubBetaEtaZigzag σ σ') (hτ : SubBetaEtaZigzag τ τ') :
    SubBetaEtaZigzag (Sub.comp σ τ) (Sub.comp σ' τ') :=
  hσ.comp_congr hτ

/-- Pointwise-related images give a path after substitution into a term. -/
example (t : Tm Γ Atom) {σ τ : Sub Γ Δ}
    (h : SubBetaEtaZigzag σ τ) :
    BetaEtaZigzag (Tm.subst σ t) (Tm.subst τ t) :=
  BetaEtaZigzag.subst_pointwise t h

/-- Declarative and path presentations also coincide pointwise for
substitutions. -/
example {σ τ : Sub Γ Δ} : SubBetaEtaEq σ τ ↔ SubBetaEtaZigzag σ τ :=
  subBetaEtaEq_iff_zigzag

/-- Beta-eta conversion is an upstream lawful congruence. -/
example : IsEquiv (Tm [Atom] Atom) BetaEtaEq := inferInstance

/-- The generic upstream congruence law lifts beta through a typed context. -/
example (C : TmCtx Γ Atom Γ Atom) (body : Tm (Atom :: Γ) Atom) (a : Tm Γ Atom) :
    BetaEtaEq (C.plug (.app (.lam body) a)) (C.plug (Tm.instantiate body a)) :=
  (LawfulCongruence.covariant (r := @BetaEtaEq Unit Γ Atom)).elim C (.beta body a)

#print axioms BetaEtaEq.instLawfulCongruence
#print axioms normalizeNf_beta
#print axioms normalizeNf_eta
#print axioms BetaEtaEq.modelEq
#print axioms BetaEtaStep.subst
#print axioms BetaEtaSteps.modelEq
#print axioms BetaEtaJoin.modelEq
#print axioms BetaEtaZigzag.of_betaEtaEq
#print axioms BetaEtaZigzag.subst_congr

section NativeCovariance

open scoped Cslib

universe u

variable {Base : Type u} {Γ : List (Ty Base)} {A : Ty Base}

/-- Beta-eta conversion is a lawful congruence at an arbitrary base universe. -/
example : Cslib.LawfulCongruence (@BetaEtaEq Base Γ A) := inferInstance

/-- A declarative conversion is a congruence edge. -/
example {t s : Tm Γ A} (h : BetaEtaEq t s) : t ≡[BetaEtaEq] s := h

/-- The native context action lifts conversion through a typed context. -/
example {t s : Tm Γ A} (h : BetaEtaEq t s) (C : TmCtx Γ A Γ A) :
    BetaEtaEq (C<[t] : Tm Γ A) (C<[s] : Tm Γ A) :=
  CovariantClass.elim (M := Cslib.HasContext.Context (Tm Γ A))
    (μ := fun c t => (c<[t] : Tm Γ A)) (r := @BetaEtaEq Base Γ A) C h

end NativeCovariance

/-- The generic context action lifts a beta equation beneath an application,
through a context that renames the function. -/
example (a : Tm [Atom] Atom) :
    BetaEtaEq
      ((TmCtx.appArg (Tm.weaken idTm) .hole : TmCtx [Atom] Atom [Atom] Atom)<[
        (Tm.app (Tm.weaken idTm) a : Tm [Atom] Atom)] : Tm [Atom] Atom)
      ((TmCtx.appArg (Tm.weaken idTm) .hole : TmCtx [Atom] Atom [Atom] Atom)<[a] :
        Tm [Atom] Atom) :=
  CovariantClass.elim (M := Cslib.HasContext.Context (Tm [Atom] Atom))
    (μ := fun c t => (c<[t] : Tm [Atom] Atom)) (r := @BetaEtaEq Unit [Atom] Atom) _
    (BetaEtaEq.beta (.var .zero) a)

end Cslib.Languages.LambdaCalculus.Stlc.NbeConversionTests
