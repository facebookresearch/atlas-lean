/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PCF: denotational equality implies contextual equivalence
-/
module

public import CSLibExt.Languages.LambdaCalculus.PCF.Adequacy

/-!
# Contextual equivalence

The standard corollary of adequacy (Plotkin 1977; Streicher 2006): terms with the
same denotation cannot be told apart by any program context. A context
`Ctx Γ A Δ B` is a term of type `B` in context `Δ` with one hole that expects a
term of type `A` in context `Γ`; holes may sit under binders, which then bind
variables of the plugged term, and the `rename` former carries the plugged
term into the scope at its position along a renaming (for example, a closed
term weakened under a fresh binder, as in `(λx. ifz x [·] zero) zero`). So
every program context, with the hole's free variables mapped into scope, is
a `Ctx`. Two terms are contextually equivalent
(`CtxEquiv`) when every closed context of ground type gives the same numeral
results for both.

* `denote_plug_congr`: denotational equality is a congruence for plugging.
* `ctxEquiv_of_denote_eq`: equal denotations imply contextual equivalence
  (compositionality, then soundness and adequacy on the closed program).
* `denote_plug_mono`, `ctxApprox_of_denote_le`: the same for approximation:
  if the denotation of `t` is below that of `u` in every environment, every
  numeral a closed ground context computes with `t` it also computes with `u`.
* `Ctx.comp`, `Ctx.plug_comp`: composition of contexts; with it, contextual
  equivalence and approximation are (pre)congruences (`CtxEquiv.congr`,
  `CtxApprox.congr`).
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.PCF

open scoped CslibStlc
open OmegaCompletePartialOrder

/-- One-hole contexts: `Ctx Γ A Δ B` turns a term `Tm Γ A` into a term `Tm Δ B`. -/
inductive Ctx (Γ : List Ty) (A : Ty) : List Ty → Ty → Type where
  | hole : Ctx Γ A Γ A
  | lam {Δ : List Ty} {B C : Ty} : Ctx Γ A (B :: Δ) C → Ctx Γ A Δ (B ⇒ C)
  | appL {Δ : List Ty} {B C : Ty} : Ctx Γ A Δ (B ⇒ C) → Tm Δ B → Ctx Γ A Δ C
  | appR {Δ : List Ty} {B C : Ty} : Tm Δ (B ⇒ C) → Ctx Γ A Δ B → Ctx Γ A Δ C
  | succ {Δ : List Ty} : Ctx Γ A Δ .nat → Ctx Γ A Δ .nat
  | pred {Δ : List Ty} : Ctx Γ A Δ .nat → Ctx Γ A Δ .nat
  | ifzTest {Δ : List Ty} : Ctx Γ A Δ .nat → Tm Δ .nat → Tm Δ .nat → Ctx Γ A Δ .nat
  | ifzThen {Δ : List Ty} : Tm Δ .nat → Ctx Γ A Δ .nat → Tm Δ .nat → Ctx Γ A Δ .nat
  | ifzElse {Δ : List Ty} : Tm Δ .nat → Tm Δ .nat → Ctx Γ A Δ .nat → Ctx Γ A Δ .nat
  | fix {Δ : List Ty} {B : Ty} : Ctx Γ A Δ (B ⇒ B) → Ctx Γ A Δ B
  | rename {Δ Δ' : List Ty} {B : Ty} : Ren Δ Δ' → Ctx Γ A Δ B → Ctx Γ A Δ' B

namespace Ctx

variable {Γ : List Ty} {A : Ty}

/-- Plug a term into the hole of a context. -/
def plug : {Δ : List Ty} → {B : Ty} → Ctx Γ A Δ B → Tm Γ A → Tm Δ B
  | _, _, .hole, t => t
  | _, _, .lam c, t => .lam (c.plug t)
  | _, _, .appL c a, t => .app (c.plug t) a
  | _, _, .appR f c, t => .app f (c.plug t)
  | _, _, .succ c, t => .succ (c.plug t)
  | _, _, .pred c, t => .pred (c.plug t)
  | _, _, .ifzTest c s₁ s₂, t => .ifz (c.plug t) s₁ s₂
  | _, _, .ifzThen r c s₂, t => .ifz r (c.plug t) s₂
  | _, _, .ifzElse r s₁ c, t => .ifz r s₁ (c.plug t)
  | _, _, .fix c, t => .fix (c.plug t)
  | _, _, .rename ρ c, t => Tm.rename ρ (c.plug t)

variable {Δ : List Ty} {B C : Ty}

@[simp] theorem plug_hole (t : Tm Γ A) : (hole : Ctx Γ A Γ A).plug t = t := rfl

@[simp] theorem plug_lam (c : Ctx Γ A (B :: Δ) C) (t : Tm Γ A) :
    (lam c).plug t = .lam (c.plug t) := rfl

@[simp] theorem plug_appL (c : Ctx Γ A Δ (B ⇒ C)) (a : Tm Δ B) (t : Tm Γ A) :
    (appL c a).plug t = .app (c.plug t) a := rfl

@[simp] theorem plug_appR (f : Tm Δ (B ⇒ C)) (c : Ctx Γ A Δ B) (t : Tm Γ A) :
    (appR f c).plug t = .app f (c.plug t) := rfl

@[simp] theorem plug_succ (c : Ctx Γ A Δ .nat) (t : Tm Γ A) :
    (succ c).plug t = .succ (c.plug t) := rfl

@[simp] theorem plug_pred (c : Ctx Γ A Δ .nat) (t : Tm Γ A) :
    (pred c).plug t = .pred (c.plug t) := rfl

@[simp] theorem plug_ifzTest (c : Ctx Γ A Δ .nat) (s₁ s₂ : Tm Δ .nat) (t : Tm Γ A) :
    (ifzTest c s₁ s₂).plug t = .ifz (c.plug t) s₁ s₂ := rfl

@[simp] theorem plug_ifzThen (r : Tm Δ .nat) (c : Ctx Γ A Δ .nat) (s₂ : Tm Δ .nat)
    (t : Tm Γ A) : (ifzThen r c s₂).plug t = .ifz r (c.plug t) s₂ := rfl

@[simp] theorem plug_ifzElse (r s₁ : Tm Δ .nat) (c : Ctx Γ A Δ .nat) (t : Tm Γ A) :
    (ifzElse r s₁ c).plug t = .ifz r s₁ (c.plug t) := rfl

@[simp] theorem plug_fix (c : Ctx Γ A Δ (B ⇒ B)) (t : Tm Γ A) :
    (fix c).plug t = .fix (c.plug t) := rfl

@[simp] theorem plug_rename {Δ' : List Ty} (ρ : Ren Δ Δ') (c : Ctx Γ A Δ B) (t : Tm Γ A) :
    (rename ρ c).plug t = Tm.rename ρ (c.plug t) := rfl

/-- Replace the hole of an outer context by an inner context. -/
def comp {Δ Θ : List Ty} {B C : Ty} : Ctx Δ B Θ C → Ctx Γ A Δ B → Ctx Γ A Θ C
  | .hole, inner => inner
  | .lam outer, inner => .lam (comp outer inner)
  | .appL outer a, inner => .appL (comp outer inner) a
  | .appR f outer, inner => .appR f (comp outer inner)
  | .succ outer, inner => .succ (comp outer inner)
  | .pred outer, inner => .pred (comp outer inner)
  | .ifzTest outer s₁ s₂, inner => .ifzTest (comp outer inner) s₁ s₂
  | .ifzThen r outer s₂, inner => .ifzThen r (comp outer inner) s₂
  | .ifzElse r s₁ outer, inner => .ifzElse r s₁ (comp outer inner)
  | .fix outer, inner => .fix (comp outer inner)
  | .rename ρ outer, inner => .rename ρ (comp outer inner)

@[simp] theorem hole_comp (c : Ctx Γ A Δ B) : comp .hole c = c := rfl

@[simp] theorem comp_hole (c : Ctx Γ A Δ B) : comp c .hole = c := by
  induction c <;> simp [comp, *]

/-- Plugging into a composed context is plugging twice. -/
theorem plug_comp {Θ : List Ty} (outer : Ctx Δ B Θ C) (inner : Ctx Γ A Δ B) (t : Tm Γ A) :
    (comp outer inner).plug t = outer.plug (inner.plug t) := by
  induction outer <;> simp [comp, *]

/-- Composition of contexts is associative. -/
theorem comp_assoc {Θ Ξ : List Ty} {D : Ty} (outer : Ctx Θ C Ξ D) (middle : Ctx Δ B Θ C)
    (inner : Ctx Γ A Δ B) : comp (comp outer middle) inner = comp outer (comp middle inner) := by
  induction outer <;> simp [comp, *]

end Ctx

namespace Tm

/-- Contextual equivalence: every closed context of ground type evaluates to
the same numerals with either term in its hole. -/
def CtxEquiv {Γ : List Ty} {A : Ty} (t u : Tm Γ A) : Prop :=
  ∀ (C : Ctx Γ A [] .nat) (n : ℕ), Eval (C.plug t) (numeral n) ↔ Eval (C.plug u) (numeral n)

/-- Denotational equality is a congruence for plugging into contexts. -/
theorem denote_plug_congr {Γ Δ : List Ty} {A B : Ty} (C : Ctx Γ A Δ B) {t u : Tm Γ A}
    (h : denote t = denote u) : denote (C.plug t) = denote (C.plug u) := by
  induction C with
  | hole => exact h
  | lam c ih =>
      refine ContinuousHom.ext _ _ fun η => ContinuousHom.ext _ _ fun d => ?_
      rw [Ctx.plug, Ctx.plug, denote_lam, denote_lam, ih]
  | appL c a ih =>
      refine ContinuousHom.ext _ _ fun η => ?_
      rw [Ctx.plug, Ctx.plug, denote_app, denote_app, ih]
  | appR f c ih =>
      refine ContinuousHom.ext _ _ fun η => ?_
      rw [Ctx.plug, Ctx.plug, denote_app, denote_app, ih]
  | succ c ih =>
      refine ContinuousHom.ext _ _ fun η => ?_
      rw [Ctx.plug, Ctx.plug, denote_succ, denote_succ, ih]
  | pred c ih =>
      refine ContinuousHom.ext _ _ fun η => ?_
      rw [Ctx.plug, Ctx.plug, denote_pred, denote_pred, ih]
  | ifzTest c s₁ s₂ ih =>
      refine ContinuousHom.ext _ _ fun η => ?_
      rw [Ctx.plug, Ctx.plug, denote_ifz, denote_ifz, ih]
  | ifzThen r c s₂ ih =>
      refine ContinuousHom.ext _ _ fun η => ?_
      rw [Ctx.plug, Ctx.plug, denote_ifz, denote_ifz, ih]
  | ifzElse r s₁ c ih =>
      refine ContinuousHom.ext _ _ fun η => ?_
      rw [Ctx.plug, Ctx.plug, denote_ifz, denote_ifz, ih]
  | fix c ih =>
      refine ContinuousHom.ext _ _ fun η => ?_
      rw [Ctx.plug, Ctx.plug, denote_fix, denote_fix, ih]
  | rename ρ c ih =>
      refine ContinuousHom.ext _ _ fun η => ?_
      rw [Ctx.plug, Ctx.plug, denote_rename, denote_rename, ih]

/-- Terms with the same denotation are contextually equivalent. -/
theorem ctxEquiv_of_denote_eq {Γ : List Ty} {A : Ty} {t u : Tm Γ A}
    (h : denote t = denote u) : CtxEquiv t u := by
  intro C n
  rw [eval_numeral_iff, eval_numeral_iff, denote_plug_congr C h]

/-- Contextual approximation: whatever numeral a closed ground context computes
with `t` in its hole, it computes with `u` too. -/
def CtxApprox {Γ : List Ty} {A : Ty} (t u : Tm Γ A) : Prop :=
  ∀ (C : Ctx Γ A [] .nat) (n : ℕ), Eval (C.plug t) (numeral n) → Eval (C.plug u) (numeral n)

/-- Denotational approximation is preserved by plugging into contexts. -/
theorem denote_plug_mono {Γ Δ : List Ty} {A B : Ty} (C : Ctx Γ A Δ B) {t u : Tm Γ A}
    (h : ∀ η, denote t η ≤ denote u η) : ∀ η, denote (C.plug t) η ≤ denote (C.plug u) η := by
  induction C with
  | hole => exact h
  | lam c ih =>
      intro η
      rw [Ctx.plug, Ctx.plug]
      exact fun d => ih (η, d)
  | appL c a ih =>
      intro η
      rw [Ctx.plug, Ctx.plug, denote_app, denote_app]
      exact ih η _
  | appR f c ih =>
      intro η
      rw [Ctx.plug, Ctx.plug, denote_app, denote_app]
      exact (denote f η).monotone (ih η)
  | succ c ih =>
      intro η
      rw [Ctx.plug, Ctx.plug, denote_succ, denote_succ]
      exact monotone_id.partMap (ih η)
  | pred c ih =>
      intro η
      rw [Ctx.plug, Ctx.plug, denote_pred, denote_pred]
      exact monotone_id.partMap (ih η)
  | ifzTest c s₁ s₂ ih =>
      intro η
      rw [Ctx.plug, Ctx.plug, denote_ifz, denote_ifz]
      exact monotone_id.partBind monotone_const (ih η)
  | ifzThen r c s₂ ih =>
      intro η
      rw [Ctx.plug, Ctx.plug, denote_ifz, denote_ifz]
      refine monotone_const.partBind
        (g := fun (x : Part ℕ) n => if n = 0 then x else (denote s₂ η : Part ℕ))
        (fun x y hxy n => ?_) (ih η)
      dsimp only
      split
      · exact hxy
      · exact le_rfl
  | ifzElse r s₁ c ih =>
      intro η
      rw [Ctx.plug, Ctx.plug, denote_ifz, denote_ifz]
      refine monotone_const.partBind
        (g := fun (x : Part ℕ) n => if n = 0 then (denote s₁ η : Part ℕ) else x)
        (fun x y hxy n => ?_) (ih η)
      dsimp only
      split
      · exact le_rfl
      · exact hxy
  | fix c ih =>
      intro η
      rw [Ctx.plug, Ctx.plug, denote_fix, denote_fix]
      exact ContinuousHom.lfp_mono (ih η)
  | rename ρ c ih =>
      intro η
      rw [Ctx.plug, Ctx.plug, denote_rename, denote_rename]
      exact ih _

/-- Denotational approximation implies contextual approximation. -/
theorem ctxApprox_of_denote_le {Γ : List Ty} {A : Ty} {t u : Tm Γ A}
    (h : ∀ η, denote t η ≤ denote u η) : CtxApprox t u := by
  intro C n ht
  apply adequacy
  have hmem : n ∈ (denote (C.plug t) PUnit.unit : Part ℕ) := by
    rw [ht.denote_numeral]
    exact Part.mem_some n
  exact denote_plug_mono C h PUnit.unit n hmem

/-- Contextual equivalence is an equivalence relation. -/
theorem CtxEquiv.refl {Γ : List Ty} {A : Ty} (t : Tm Γ A) : CtxEquiv t t :=
  fun _ _ => Iff.rfl

theorem CtxEquiv.symm {Γ : List Ty} {A : Ty} {t u : Tm Γ A} (h : CtxEquiv t u) :
    CtxEquiv u t :=
  fun C n => (h C n).symm

theorem CtxEquiv.trans {Γ : List Ty} {A : Ty} {t u v : Tm Γ A} (h₁ : CtxEquiv t u)
    (h₂ : CtxEquiv u v) : CtxEquiv t v :=
  fun C n => (h₁ C n).trans (h₂ C n)

/-- Contextual equivalence is a congruence: it is preserved by plugging into
any context. -/
theorem CtxEquiv.congr {Γ Δ : List Ty} {A B : Ty} {t u : Tm Γ A} (h : CtxEquiv t u)
    (D : Ctx Γ A Δ B) : CtxEquiv (D.plug t) (D.plug u) := fun C n => by
  rw [← Ctx.plug_comp, ← Ctx.plug_comp]
  exact h (C.comp D) n

/-- Contextual approximation is a preorder and a precongruence. -/
theorem CtxApprox.refl {Γ : List Ty} {A : Ty} (t : Tm Γ A) : CtxApprox t t :=
  fun _ _ h => h

theorem CtxApprox.trans {Γ : List Ty} {A : Ty} {t u v : Tm Γ A} (h₁ : CtxApprox t u)
    (h₂ : CtxApprox u v) : CtxApprox t v :=
  fun C n h => h₂ C n (h₁ C n h)

theorem CtxApprox.congr {Γ Δ : List Ty} {A B : Ty} {t u : Tm Γ A} (h : CtxApprox t u)
    (D : Ctx Γ A Δ B) : CtxApprox (D.plug t) (D.plug u) := fun C n => by
  rw [← Ctx.plug_comp, ← Ctx.plug_comp]
  exact h (C.comp D) n

/-- Contextual equivalence is mutual contextual approximation. -/
theorem ctxEquiv_iff_ctxApprox {Γ : List Ty} {A : Ty} {t u : Tm Γ A} :
    CtxEquiv t u ↔ CtxApprox t u ∧ CtxApprox u t :=
  ⟨fun h => ⟨fun C n => (h C n).mp, fun C n => (h C n).mpr⟩,
    fun ⟨h₁, h₂⟩ C n => ⟨h₁ C n, h₂ C n⟩⟩

end Tm

end Cslib.Languages.LambdaCalculus.PCF
