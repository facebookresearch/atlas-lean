/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.PCF.ContextualEquivalence
public import CSLibExtTest.Languages.LambdaCalculus.PCF.DenotationalTests

/-!
# Tests for contextual equivalence in PCF

* `pred (succ x) ≅ x` for an open `x : nat`: an equivalence of open terms,
  established from denotations.
* `(λx. x) zero ≅ zero` (β), and `Ω ≅ fix (λx. succ x)`: both denote `⊥`.
* `Ω ⊑ zero`: `⊥` approximates everything, so `Ω` contextually approximates
  every ground term.
* `zero` and `succ zero` are not contextually equivalent (the empty context
  separates them), nor are the open terms `x` and `zero` (the context
  `(λx. [·]) 1` separates them).
* Plugging: the context `λx. [·]` plugged with `x` is the identity function;
  composing contexts and plugging twice agree (`Ctx.plug_comp`).
* Congruence: `pred (succ x) ≅ x` gives `λx. pred (succ x) ≅ λx. x`, and
  equivalence splits into two approximations.
* Closed holes under fresh binders (the `rename` former): the context
  `(λx. ifz x [·] zero) zero` separates `Ω` from `1`, and congruence lifts
  `Ω ≅ fix (λx. succ x)` to `λy. Ω ≅ λy. fix (λx. succ x)`.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.PCF.Tests

open scoped CslibStlc
open OmegaCompletePartialOrder Tm

/-- `pred (succ x) ≅ x` for a free variable `x : nat`. -/
theorem predSucc_ctxEquiv :
    CtxEquiv (.pred (.succ (.var .zero)) : Tm [Ty.nat] .nat) (.var .zero) := by
  apply ctxEquiv_of_denote_eq
  refine ContinuousHom.ext _ _ fun η => ?_
  rw [denote_pred, denote_succ, Part.map_map]
  exact Part.map_id' (fun _ => rfl) _

/-- β: `(λx. x) zero ≅ zero`. -/
example : CtxEquiv (.app (.lam (.var .zero)) .zero : Tm [] .nat) .zero :=
  ctxEquiv_of_denote_eq (ContinuousHom.ext _ _ fun _ => rfl)

/-- `fix (λx. succ x)` denotes `⊥`. -/
theorem fixSucc_denote :
    denote (.fix (.lam (.succ (.var .zero))) : Tm [] .nat) ε = ⊥ := by
  rw [denote_fix]
  refine le_antisymm (ContinuousHom.lfp_le _ ?_) bot_le
  intro n hn
  rw [denote_lam, denote_succ] at hn
  obtain ⟨m, hm, -⟩ := (Part.mem_map_iff _).mp hn
  exact absurd hm (Part.notMem_none m)

/-- Two diverging programs are contextually equivalent. -/
theorem omega_ctxEquiv_fixSucc : CtxEquiv omega (.fix (.lam (.succ (.var .zero)))) :=
  ctxEquiv_of_denote_eq (ContinuousHom.ext _ _ fun η =>
    (show denote omega η = ⊥ from omega_denote).trans (fixSucc_denote).symm)

/-- `Ω` contextually approximates `zero`. -/
example : CtxApprox omega .zero :=
  ctxApprox_of_denote_le fun η => (show denote omega η = ⊥ from omega_denote) ▸ bot_le

/-- The empty context separates `zero` from `succ zero`. -/
example : ¬ CtxEquiv (.zero : Tm [] .nat) (.succ .zero) := fun h => by
  have := (h .hole 0).mp Eval.zero
  exact absurd (numeral_injective (Eval.deterministic (Eval.succ (n := 0) Eval.zero) this))
    (by decide)

/-- On open terms the relation is not trivial either: the context `(λx. [·]) 1`
separates the variable `x` from `zero`. -/
example : ¬ CtxEquiv (.var .zero : Tm [Ty.nat] .nat) .zero := fun h => by
  have hx : Eval ((Ctx.appL (Ctx.lam .hole) (.succ .zero)).plug (.var .zero) : Tm [] .nat)
      (numeral 1) :=
    .app .lam (.succ (n := 0) .zero)
  have h0 : Eval ((Ctx.appL (Ctx.lam .hole) (.succ .zero)).plug .zero : Tm [] .nat)
      (numeral 0) :=
    .app .lam .zero
  have := (h (Ctx.appL (Ctx.lam .hole) (.succ .zero)) 1).mp hx
  exact absurd (numeral_injective (Eval.deterministic h0 this)) (by decide)

/-- Plugging under a binder captures the bound variable. -/
example : (Ctx.lam .hole : Ctx [Ty.nat] Ty.nat [] (Ty.nat ⇒ Ty.nat)).plug (.var .zero) =
    .lam (.var .zero) := rfl

/-- Congruence: from `pred (succ x) ≅ x`, the closed functions
`λx. pred (succ x)` and `λx. x` are contextually equivalent. -/
example : CtxEquiv (.lam (.pred (.succ (.var .zero))) : Tm [] (Ty.nat ⇒ Ty.nat))
    (.lam (.var .zero)) :=
  predSucc_ctxEquiv.congr (.lam .hole)

/-- Composing contexts: `(λx. [·]) 1` after `succ [·]` plugs to
`(λx. succ x) 1`. -/
example : ((Ctx.appL (.lam .hole) (Tm.numeral 1) : Ctx [Ty.nat] Ty.nat [] Ty.nat).comp
      (.succ .hole)).plug (.var .zero) =
    .app (.lam (.succ (.var .zero))) (Tm.numeral 1) := by
  rw [Ctx.plug_comp]
  rfl

/-- A closed hole under a fresh binder: `(λx. ifz x [·] zero) zero`, where the
`rename` former weakens the plugged closed term into the scope of `x`. -/
def ifzCtx : Ctx [] .nat [] .nat :=
  .appL (.lam (.ifzThen (.var .zero) (.rename .succ .hole) .zero)) .zero

example (t : Tm [] .nat) :
    ifzCtx.plug t = .app (.lam (.ifz (.var .zero) (Tm.weaken t) .zero)) .zero := rfl

/-- The context computes with its hole: plugging `Ω` diverges, plugging `1`
returns `1`, so it separates `Ω` from `1`. -/
example : ¬ CtxEquiv omega (Tm.numeral 1 : Tm [] .nat) := fun h => by
  have h1 : Eval (ifzCtx.plug (Tm.numeral 1)) (Tm.numeral 1) :=
    .app .lam (show Eval (.ifz .zero (Tm.numeral 1) .zero) (Tm.numeral 1) from
      .ifzZero .zero (Eval.numeral 1))
  have h0 := (h ifzCtx 1).mpr h1
  cases h0 with
  | app hf hb =>
      cases hf
      change Eval (.ifz .zero omega .zero) (Tm.numeral 1) at hb
      cases hb with
      | ifzZero _ hs =>
          have := hs.denote_numeral ε
          rw [omega_denote] at this
          exact Part.notMem_none 1 (this ▸ Part.mem_some 1)
      | ifzSucc ht _ => cases ht

/-- Congruence under a fresh binder: from `Ω ≅ fix (λx. succ x)` (closed), the
functions `λy. Ω` and `λy. fix (λx. succ x)` are contextually equivalent. -/
example : CtxEquiv (.lam (Tm.weaken omega) : Tm [] (Ty.nat ⇒ Ty.nat))
    (.lam (Tm.weaken (.fix (.lam (.succ (.var .zero)))))) :=
  omega_ctxEquiv_fixSucc.congr (.lam (.rename .succ .hole))

/-- Approximation is the one-directional half of equivalence. -/
example : CtxApprox (.var .zero : Tm [Ty.nat] .nat) (.pred (.succ (.var .zero))) :=
  (ctxEquiv_iff_ctxApprox.mp predSucc_ctxEquiv).2

end Cslib.Languages.LambdaCalculus.PCF.Tests
