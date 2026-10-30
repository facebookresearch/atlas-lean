/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.CPS.CallByName

/-!
# Tests for the call-by-name CPS translation

* The type translation at a function type: arguments and results are
  computations.
* The translation of an application passes the argument's translation, a
  computation, unevaluated.
* `x : ℕ ⊢ (λy. y) x` and `f : ℕ → ℕ, x : ℕ ⊢ f (f x)`: run with the identity
  continuation in related environments, the translations compute the
  direct-style values, by evaluation (`rfl`) and through `cbn_denote_base_id`.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.CPS.CbnTests

open scoped CslibStlc

abbrev N : Ty Unit := .base ()

abbrev I : Unit → Type := fun _ => Nat

example (R : Ty Unit) :
    cbnTy R (N ⇒ N) = (((N ⇒ R) ⇒ R) ⇒ ((N ⇒ R) ⇒ R)) := rfl

/-- `⟦f a⟧ = λk. ⟦f⟧ (λm. m ⟦a⟧ k)`: the argument is the computation `⟦a⟧`. -/
example (R : Ty Unit) (f : Tm [N ⇒ N, N] (N ⇒ N)) (a : Tm [N ⇒ N, N] N) :
    cbn R (.app f a) =
      .lam (.app (Tm.weaken (cbn R f))
        (.lam (.app (.app (.var .zero) (Tm.weaken (Tm.weaken (cbn R a))))
          (.var (.succ .zero))))) := cbn_app R f a

/-- The empty environment. -/
def ε : Env I [] := fun x => nomatch x

/-- `x ↦ 5`, and its call-by-name counterpart `x ↦ (λk. k 5)`. -/
def η₁ : Env I [N] := Env.cons (I := I) (A := N) (5 : Nat) ε

/-- The computation `λk. k n`. -/
def ret (n : Nat) : Ty.denote I (cbnComp N N) := fun (k : Nat → Nat) => k n

def η₁' : Env I ([N].map (cbnComp N)) := Env.cons (I := I) (A := cbnComp N N) (ret 5) ε

theorem η₁_rel : CbnEnvRel N η₁ η₁' := by
  intro A x
  cases x with
  | zero => exact ⟨(5 : Nat), rfl, fun _ => rfl⟩
  | succ x => exact nomatch x

/-- `(λy. y) x`. -/
def idApp : Tm [N] N := .app (.lam (.var .zero)) (.var .zero)

example : Tm.denote I (cbn N idApp) η₁' id = (5 : Nat) := rfl

example : Tm.denote I (cbn N idApp) η₁' id = Tm.denote I idApp η₁ :=
  cbn_denote_base_id idApp η₁_rel

/-- `f ↦ succ`, `x ↦ 3`, and their call-by-name counterparts. -/
def η₂ : Env I [N ⇒ N, N] :=
  Env.cons (I := I) (A := N ⇒ N) Nat.succ (Env.cons (I := I) (A := N) (3 : Nat) ε)

/-- The call-by-name successor: run the argument computation, return the
successor of its value. -/
def succCbn : Ty.denote I (cbnTy N (N ⇒ N)) :=
  fun (c : (Nat → Nat) → Nat) (k : Nat → Nat) => k (c id + 1)

def η₂' : Env I ([N ⇒ N, N].map (cbnComp N)) :=
  Env.cons (I := I) (A := cbnComp N (N ⇒ N))
    (fun (k : Ty.denote I (cbnTy N (N ⇒ N)) → Nat) => k succCbn)
    (Env.cons (I := I) (A := cbnComp N N) (ret 3) ε)

theorem succCbn_rel : CbnRel N I (N ⇒ N) Nat.succ succCbn := by
  show ∀ (a : Nat) (c : (Nat → Nat) → Nat), (∃ v : Nat, a = v ∧ ∀ k, c k = k v) →
    ∃ w : Nat, a + 1 = w ∧ ∀ k : Nat → Nat, k (c id + 1) = k w
  rintro a c ⟨v, rfl, hc⟩
  exact ⟨a + 1, rfl, fun k => by rw [hc id]; rfl⟩

theorem η₂_rel : CbnEnvRel N η₂ η₂' := by
  intro A x
  cases x with
  | zero => exact ⟨succCbn, succCbn_rel, fun _ => rfl⟩
  | succ x =>
      cases x with
      | zero => exact ⟨(3 : Nat), rfl, fun _ => rfl⟩
      | succ x => exact nomatch x

/-- `f (f x)`. -/
def twice : Tm [N ⇒ N, N] N := .app (.var .zero) (.app (.var .zero) (.var (.succ .zero)))

example : Tm.denote I (cbn N twice) η₂' id = (5 : Nat) := rfl

example : Tm.denote I (cbn N twice) η₂' id = Tm.denote I twice η₂ :=
  cbn_denote_base_id twice η₂_rel

end Cslib.Languages.LambdaCalculus.Stlc.CPS.CbnTests
