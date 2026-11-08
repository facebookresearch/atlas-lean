/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Typed term contexts for STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Equational

/-!
# Typed term contexts for STLC

This file formalizes one-hole contexts for intrinsically typed STLC terms.
The input and output contexts and types are all tracked by indices, so plugging
is scope-aware and type preserving.  A `lam` context intentionally binds the
leading variable of its hole context.  Contexts compose, plugging respects
composition, and semantic equality is a congruence for every typed context.

The final section packages equality in every same-universe set-theoretic
interpretation as a model-independent equational theory and lifts beta and eta
through contexts.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u v

variable {Base : Type u}
variable {A B C D : Ty Base}
variable {Γ Δ Θ Ξ : List (Ty Base)}

/-- A well-typed term with one hole.  The first context and type describe the
hole; the second context and type describe the term produced after plugging. -/
inductive TmCtx {Base : Type u} (Γ : List (Ty Base)) (A : Ty Base) :
    (Δ : List (Ty Base)) → (B : Ty Base) → Type u where
  | hole : TmCtx Γ A Γ A
  | appFun {Δ : List (Ty Base)} {B C : Ty Base}
      (ctx : TmCtx Γ A Δ (B ⇒ C)) (a : Tm Δ B) : TmCtx Γ A Δ C
  | appArg {Δ : List (Ty Base)} {B C : Ty Base}
      (f : Tm Δ (B ⇒ C)) (ctx : TmCtx Γ A Δ B) : TmCtx Γ A Δ C
  | lam {Δ : List (Ty Base)} {B C : Ty Base}
      (ctx : TmCtx Γ A (B :: Δ) C) : TmCtx Γ A Δ (B ⇒ C)

namespace TmCtx

/-- Fill the unique hole of a typed context. -/
def plug {Δ : List (Ty Base)} {B : Ty Base} : TmCtx Γ A Δ B → Tm Γ A → Tm Δ B
  | .hole, t => t
  | .appFun C a, t => .app (plug C t) a
  | .appArg f C, t => .app f (plug C t)
  | .lam C, t => .lam (plug C t)

@[simp]
theorem plug_hole (t : Tm Γ A) : plug .hole t = t := rfl

@[simp]
theorem plug_appFun (C : TmCtx Γ A Δ (B ⇒ C)) (a : Tm Δ B) (t : Tm Γ A) :
    plug (.appFun C a) t = .app (plug C t) a := rfl

@[simp]
theorem plug_appArg (f : Tm Δ (B ⇒ C)) (C : TmCtx Γ A Δ B) (t : Tm Γ A) :
    plug (.appArg f C) t = .app f (plug C t) := rfl

@[simp]
theorem plug_lam (C : TmCtx Γ A (B :: Δ) C) (t : Tm Γ A) :
    plug (.lam C) t = .lam (plug C t) := rfl

/-- Replace the hole of an outer context by an inner context. -/
def comp {Δ Θ : List (Ty Base)} {B C : Ty Base} :
    TmCtx Δ B Θ C → TmCtx Γ A Δ B → TmCtx Γ A Θ C
  | .hole, inner => inner
  | .appFun outer a, inner => .appFun (comp outer inner) a
  | .appArg f outer, inner => .appArg f (comp outer inner)
  | .lam outer, inner => .lam (comp outer inner)

@[simp]
theorem hole_comp (C : TmCtx Γ A Δ B) : comp .hole C = C := rfl

@[simp]
theorem comp_hole (C : TmCtx Γ A Δ B) : comp C .hole = C := by
  induction C <;> simp [comp, *]

/-- Plugging into composed contexts is the same as plugging twice. -/
theorem plug_comp (outer : TmCtx Δ B Θ C) (inner : TmCtx Γ A Δ B) (t : Tm Γ A) :
    plug (comp outer inner) t = plug outer (plug inner t) := by
  induction outer <;> simp [comp, plug, *]

/-- Composition of typed contexts is associative. -/
theorem comp_assoc (outer : TmCtx Θ C Ξ D) (middle : TmCtx Δ B Θ C)
    (inner : TmCtx Γ A Δ B) :
    comp (comp outer middle) inner = comp outer (comp middle inner) := by
  induction outer <;> simp [comp, *]

/-- Every typed context preserves equality in a fixed model. -/
theorem semEq {I : Base → Type v} (C : TmCtx Γ A Δ B) {t u : Tm Γ A}
    (h : SemEq I t u) : SemEq I (plug C t) (plug C u) := by
  induction C with
  | hole => exact h
  | appFun C a ih => exact SemEq.app ih (SemEq.refl I a)
  | appArg f C ih => exact SemEq.app (SemEq.refl I f) ih
  | lam C ih => exact SemEq.lam ih

end TmCtx

/-- Equality in every same-universe set-theoretic interpretation of the base
types.  Unlike `SemEq`, this relation does not choose a particular model. -/
def ModelEq (t u : Tm Γ A) : Prop :=
  ∀ I : Base → Type u, SemEq I t u

namespace ModelEq

theorem refl (t : Tm Γ A) : ModelEq t t := fun I ↦ SemEq.refl I t

theorem symm {t u : Tm Γ A} (h : ModelEq t u) : ModelEq u t :=
  fun I ↦ (h I).symm

theorem trans {t u w : Tm Γ A} (htu : ModelEq t u) (huw : ModelEq u w) :
    ModelEq t w := fun I ↦ (htu I).trans (huw I)

/-- Model equality is a congruence for every typed one-hole context. -/
theorem context (C : TmCtx Γ A Δ B) {t u : Tm Γ A} (h : ModelEq t u) :
    ModelEq (C.plug t) (C.plug u) := fun I ↦ C.semEq (h I)

/-- Beta equality holds independently of the interpretation of base types. -/
theorem beta (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    ModelEq (.app (.lam body) a) (Tm.instantiate body a) :=
  fun I ↦ SemEq.beta I body a

/-- Eta equality holds independently of the interpretation of base types. -/
theorem eta (f : Tm Γ (A ⇒ B)) :
    ModelEq (.lam (.app (Tm.weaken f) (.var .zero))) f :=
  fun I ↦ SemEq.eta I f

/-- A beta equation remains valid inside an arbitrary typed context. -/
theorem context_beta (C : TmCtx Γ B Δ C) (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    ModelEq (C.plug (.app (.lam body) a)) (C.plug (Tm.instantiate body a)) :=
  context C (beta body a)

/-- An eta equation remains valid inside an arbitrary typed context. -/
theorem context_eta (C : TmCtx Γ (A ⇒ B) Δ C) (f : Tm Γ (A ⇒ B)) :
    ModelEq (C.plug (.lam (.app (Tm.weaken f) (.var .zero))) ) (C.plug f) :=
  context C (eta f)

theorem equivalence : Equivalence (@ModelEq Base A Γ) := ⟨refl, symm, trans⟩

end ModelEq

end Cslib.Languages.LambdaCalculus.Stlc
