/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Control.Monad.Free.Handlers

/-!
# Handler statement tests: collection, exceptions, and state runs

Checks for the free-model handler unit after Plotkin and Pretnar,
"Handlers of Algebraic Effects" (ESOP 2009). The list collector below is
the all-solutions handler of the explicit nondeterminism example
(Section 6.4), read in order over the raw `fail`/`pick` signature. No
equation is claimed for it: the unit imposes neither the Section 6.4
monoid equations nor the semilattice equations of `or : 2`, and list
append is neither commutative nor idempotent, so it is not a model of
the latter.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib

namespace FreeM

universe u v w w' w''

namespace HandlersTests

/-- Ordered, multiplicity-preserving list collector over the raw
nondeterminism signature, following the Section 6.4 all-solutions
handler: values collect to singletons, failure to the empty list, and
choice appends `true` before `false`. Append is neither commutative nor
idempotent, so this is not a model of the semilattice equations of
`or : 2`, and no equation is claimed for it in this unit. -/
def collect {α : Type v} : FreeNondet α → List α :=
  FreeM.foldFreeM (fun a => [a]) fun {ι} op k =>
    match op, k with
    | NondetF.fail, _ => []
    | NondetF.choice, k => k true ++ k false

/-- Collecting a pure return gives the singleton list. -/
theorem collect_pure {α : Type v} (x : α) :
    collect (pure x) = [x] := by
  unfold collect
  rw [FreeM.foldFreeM_pure]

/-- Collecting failure gives the empty list. -/
theorem collect_fail {α : Type v} :
    collect (FreeNondet.fail : FreeNondet α) = ([] : List α) := by
  unfold collect FreeNondet.fail
  rw [FreeM.foldFreeM_lift_bind]

/-- Collecting a choice appends the two collections in order. -/
theorem collect_choice {α : Type v} (x y : FreeNondet α) :
    collect (FreeNondet.choice x y) = collect x ++ collect y := by
  unfold collect FreeNondet.choice
  rw [FreeM.foldFreeM_lift_bind]

/-- Unhandled raises survive the identity-shaped handler. -/
theorem except_unhandled_stays_raised {E : Type u} {α : Type v}
    {δ : Type w'} (e : E) (k : δ → FreeExcept E α) :
    FreeExcept.handle (fun (a : α) => (pure a : FreeExcept E α))
      (fun (e : E) => (FreeExcept.raise e : FreeExcept E α))
      ((FreeExcept.raise e : FreeExcept E δ).bind k) =
      (FreeExcept.raise e : FreeExcept E α) := by
  exact FreeExcept.handle_raise_bind _ _ _ _

/-- Pure values pass through the identity-shaped handler. -/
theorem except_unhandled_pure {E : Type u} {α : Type v} (x : α) :
    FreeExcept.handle (fun (a : α) => (pure a : FreeExcept E α))
      (fun (e : E) => (FreeExcept.raise e : FreeExcept E α))
      (pure x : FreeExcept E α) = (pure x : FreeExcept E α) := by
  exact FreeExcept.handle_pure _ _ _

/-- Setting twice then getting returns the second write. -/
theorem state_put_put_get (s0 : Nat) :
    FreeState.run' ((MonadStateOf.set 1 : FreeState Nat PUnit).bind
      fun _ => (MonadStateOf.set 2 : FreeState Nat PUnit).bind
      fun _ => (MonadStateOf.get : FreeState Nat Nat)) s0 = 2 := by
  have hget : (MonadStateOf.get : FreeState Nat Nat) =
      (MonadState.get : FreeState Nat Nat) := rfl
  rw [hget, FreeM.FreeState.set_def, FreeM.FreeState.set_def,
    FreeM.FreeState.get_def, FreeM.FreeState.run'_bind, FreeM.FreeState.run_set]
  show FreeState.run' ((FreeM.lift (FreeM.StateF.set 2)).bind fun _ =>
      FreeM.lift FreeM.StateF.get) 1 = 2
  rw [FreeM.FreeState.run'_bind, FreeM.FreeState.run_set]
  show FreeState.run' (FreeM.lift FreeM.StateF.get) 2 = 2
  rw [FreeM.FreeState.run'_get]

/-- The get-put law applies under an arbitrary continuation. -/
theorem state_get_set_continuation (s0 : Nat) :
    FreeState.run ((MonadStateOf.get : FreeState Nat Nat).bind fun s =>
      (MonadStateOf.set s : FreeState Nat PUnit).bind fun _ =>
        (MonadStateOf.set 5 : FreeState Nat PUnit)) s0 =
      FreeState.run (MonadStateOf.set 5 : FreeState Nat PUnit) s0 :=
  FreeState.run_get_set _ s0

/-- The put-get law applies under an arbitrary continuation. -/
theorem state_set_get_continuation (s0 : Nat) :
    FreeState.run ((MonadStateOf.set 3 : FreeState Nat PUnit).bind fun _ =>
      (MonadStateOf.get : FreeState Nat Nat).bind fun t =>
        (MonadStateOf.set (t + 1) : FreeState Nat PUnit)) s0 =
      FreeState.run ((MonadStateOf.set 3 : FreeState Nat PUnit).bind fun _ =>
        (MonadStateOf.set (3 + 1) : FreeState Nat PUnit)) s0 :=
  FreeState.run_set_get 3 _ s0

/-- The put-put law applies under an arbitrary continuation. -/
theorem state_set_set_continuation (s0 : Nat) :
    FreeState.run ((MonadStateOf.set 1 : FreeState Nat PUnit).bind fun _ =>
      (MonadStateOf.set 2 : FreeState Nat PUnit).bind fun _ =>
        (MonadStateOf.get : FreeState Nat Nat)) s0 =
      FreeState.run ((MonadStateOf.set 2 : FreeState Nat PUnit).bind fun _ =>
        (MonadStateOf.get : FreeState Nat Nat)) s0 :=
  FreeState.run_set_set 1 2 _ s0

/-- Collecting a nested choice lists every result in order. -/
theorem nondet_collects_all :
    collect (FreeNondet.choice (pure 1 : FreeNondet Nat)
      (FreeNondet.choice (FreeNondet.fail : FreeNondet Nat)
        (pure 2 : FreeNondet Nat))) = [1, 2] := by
  simp only [collect_choice, collect_pure, collect_fail]
  rfl

end HandlersTests

end FreeM

end Cslib

end
