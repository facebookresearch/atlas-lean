/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Control.Monad.Free
public import Cslib.Foundations.Control.Monad.Free.Fold
public import Cslib.Foundations.Control.Monad.Free.Effects

/-!
# Free-model handlers: exceptions, state run laws, explicit nondeterminism

Exception handlers over the free monad after Plotkin and Pretnar,
"Handlers of Algebraic Effects" (ESOP 2009), Section 2: exceptions
are nullary operations with no equations, handled by an arbitrary
return map plus one chosen outcome per exception. Handling here is the
pinned algebra fold, and its uniqueness theorem is reused rather than
reproved. State laws appear only as equalities after running, for an
arbitrary continuation. The nondeterminism signature is the failure
plus binary choice signature of the paper's explicit nondeterminism
example (Section 6.4: `fail : 0`, `pick : 2`), kept as raw syntax:
neither its monoid equations nor the semilattice equations of the
`or : 2` theory (Section 1) are imposed by a quotient.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib

namespace FreeM

universe u v w w' w''

/-- Nullary raise operations: Section 2's `raise_e : 0` for each `e`.

The empty index records that no value is handed to the continuation
after a raise. There are no equations on this signature. -/
inductive ExceptF (E : Type u) : Type u → Type u where
  | raise (e : E) : ExceptF E (PEmpty : Type u)

/-- The free carrier for exceptions: programs that may raise `E`. -/
abbrev FreeExcept (E : Type u) (α : Type v) := FreeM (ExceptF E) α

/-- Raw explicit-nondeterminism signature: failure `fail : 0` and
binary choice `choice` (the paper's `pick : 2`), as in Plotkin and
Pretnar's Section 6.4.

This is syntax only: it is not quotiented by the Section 6.4 monoid equations or
by the semilattice equations of `or : 2`. -/
inductive NondetF : Type → Type where
  | fail : NondetF Empty
  | choice : NondetF Bool

/-- The free carrier for nondeterminism: failure and choice programs over `α`. -/
abbrev FreeNondet (α : Type v) := FreeM NondetF α

namespace FreeExcept

/-- Smart constructor: raise `e`, eliminating the empty continuation
so the computation stands at any result type. -/
def raise {E : Type u} {α : Type v} (e : E) : FreeExcept E α :=
  (FreeM.lift (ExceptF.raise e)).bind fun x => nomatch x

/-- General exception handler as the pinned algebra fold.

The value clause is the arbitrary return map `g`, and each raise of
`e` is sent to the chosen outcome `onRaise e`, ignoring the
continuation. This is an application of the pinned `foldFreeM`
universal property (`foldFreeM_unique`); it proves no new one. -/
def handle {E : Type u} {α : Type v} {β : Type w} (g : α → β)
    (onRaise : E → β) : FreeExcept E α → β :=
  FreeM.foldFreeM g fun {ι} op _ =>
    match op with
    | ExceptF.raise e => onRaise e

/-- The handler sends a pure return to the return map. -/
theorem handle_pure {E : Type u} {α : Type v} {β : Type w} (g : α → β)
    (onRaise : E → β) (x : α) :
    handle g onRaise (pure x) = g x := by
  unfold handle
  rw [FreeM.foldFreeM_pure]

/-- The handler sends a raised exception, bound to any continuation,
to the chosen outcome, discarding the continuation. -/
theorem handle_raise_bind {E : Type u} {α : Type v} {β : Type w}
    {δ : Type w'} (g : α → β) (onRaise : E → β) (e : E)
    (k : δ → FreeExcept E α) :
    handle g onRaise ((raise e : FreeExcept E δ).bind k) =
      onRaise e := by
  unfold raise handle
  rw [FreeM.bind_assoc, FreeM.foldFreeM_lift_bind]

/-- Uniqueness of the exception handler, assembled from the pinned
`foldFreeM_unique` (reuse, not a new universal-property theorem). -/
theorem handle_unique {E : Type u} {α : Type v} {β : Type w} (g : α → β)
    (onRaise : E → β) (h : FreeExcept E α → β)
    (h_pure : ∀ (x : α), h (pure x) = g x)
    (h_raise : ∀ {δ : Type w'} (e : E) (k : δ → FreeExcept E α),
      h ((raise e : FreeExcept E δ).bind k) = onRaise e) :
    h = handle g onRaise := by
  unfold handle
  refine FreeM.foldFreeM_unique _ _ _ ?_ ?_
  · exact h_pure
  · intro ι op k
    cases op with
    | raise e =>
      show h ((FreeM.lift (ExceptF.raise e)).bind k) = onRaise e
      have hr := h_raise (δ := (PEmpty : Type w')) e
        (fun x => (nomatch x : FreeExcept E α))
      have hnode : ((raise e : FreeExcept E (PEmpty : Type w')).bind
          (fun x => (nomatch x : FreeExcept E α))) =
          (FreeM.lift (ExceptF.raise e)).bind k := by
        unfold raise
        rw [FreeM.bind_assoc]
        apply congrArg (FreeM.bind (FreeM.lift (ExceptF.raise e)))
        exact funext fun z => nomatch z
      rw [hnode] at hr
      exact hr

/-- The concrete `Except` runner: return map `Except.ok`, with raised
exceptions becoming `Except.error`. -/
def run {E : Type u} {α : Type v} : FreeExcept E α → Except E α :=
  handle Except.ok Except.error

/-- Running a pure return gives `Except.ok`. -/
theorem run_pure {E : Type u} {α : Type v} (x : α) :
    run (pure x : FreeExcept E α) = (Except.ok x : Except E α) := by
  unfold run
  rw [handle_pure]

/-- Running a raise gives `Except.error`. -/
theorem run_raise {E : Type u} {α : Type v} (e : E) :
    run (raise e : FreeExcept E α) = (Except.error e : Except E α) := by
  unfold run
  have hbind := (FreeM.bind_pure (raise e : FreeExcept E α)).symm
  rw [hbind, handle_raise_bind]

/-- A first error short-circuits the rest of a bind. -/
theorem run_bind_error {E : Type u} {α : Type v} {γ : Type w'}
    (m : FreeExcept E α) (k : α → FreeExcept E γ) (e : E)
    (h : run m = Except.error e) :
    run (m.bind k) = Except.error e := by
  have dist : ∀ (m : FreeExcept E α) (k : α → FreeExcept E γ),
      run (m.bind k) = Except.bind (run m) (fun a => run (k a)) := by
    intro m
    induction m using FreeM.induction with
    | pure a =>
      intro k
      rw [FreeM.pure_bind, run_pure]
      rfl
    | lift_bind op cont ih =>
      intro k
      cases op with
      | raise e' =>
        have hL : run (((FreeM.lift (ExceptF.raise e')).bind cont).bind k) =
            Except.error e' := by
          unfold run handle
          rw [FreeM.bind_assoc, FreeM.foldFreeM_lift_bind]
        have hR : run ((FreeM.lift (ExceptF.raise e')).bind cont) =
            Except.error e' := by
          unfold run handle
          rw [FreeM.foldFreeM_lift_bind]
        rw [hL, hR]
        rfl
  rw [dist, h]
  rfl

end FreeExcept

namespace FreeState

/-- Get-get equation after running: reading twice feeds the same state
twice. A Plotkin-Power state equation stated only for `run`, proved
later from the pinned run lemmas; not an equality of raw syntax. -/
theorem run_get_get {σ : Type u} {α : Type v}
    (k : σ → σ → FreeState σ α) (s0 : σ) :
    run ((MonadStateOf.get : FreeState σ σ).bind fun s1 =>
      (MonadStateOf.get : FreeState σ σ).bind fun s2 => k s1 s2) s0 =
      run ((MonadStateOf.get : FreeState σ σ).bind fun s => k s s) s0 := by
  have hget : (MonadStateOf.get : FreeState σ σ) =
      (MonadState.get : FreeState σ σ) := rfl
  rw [hget, FreeM.FreeState.get_def]
  have hL : run ((FreeM.lift FreeM.StateF.get).bind fun s1 =>
      (FreeM.lift FreeM.StateF.get).bind fun s2 => k s1 s2) s0 =
      run (k s0 s0) s0 := by
    rw [FreeM.FreeState.run_bind, FreeM.FreeState.run_get]
    show run ((FreeM.lift FreeM.StateF.get).bind fun s2 => k s0 s2) s0 =
      run (k s0 s0) s0
    rw [FreeM.FreeState.run_bind, FreeM.FreeState.run_get]
  have hR : run ((FreeM.lift FreeM.StateF.get).bind fun s => k s s) s0 =
      run (k s0 s0) s0 := by
    rw [FreeM.FreeState.run_bind, FreeM.FreeState.run_get]
  rw [hL, hR]

/-- Get-put equation after running, with an arbitrary continuation:
reading the state and writing it back before `k` runs exactly as `k`.
Stated only for `run`, proved from the pinned run lemmas; not an
equality of raw `FreeM` syntax. -/
theorem run_get_set {σ : Type u} {α : Type v} (k : FreeState σ α) (s0 : σ) :
    run ((MonadStateOf.get : FreeState σ σ).bind fun s =>
      (MonadStateOf.set s : FreeState σ PUnit).bind fun _ => k) s0 =
      run k s0 := by
  have hget : (MonadStateOf.get : FreeState σ σ) =
      (MonadState.get : FreeState σ σ) := rfl
  rw [hget, FreeM.FreeState.get_def]
  rw [FreeM.FreeState.run_bind, FreeM.FreeState.run_get]
  change run ((MonadStateOf.set s0 : FreeState σ PUnit).bind fun _ => k) s0 =
    run k s0
  rw [FreeM.FreeState.set_def]
  rw [FreeM.FreeState.run_bind, FreeM.FreeState.run_set]

/-- Return-specialized instance of `run_get_set` (`k := pure PUnit.unit`),
with the final pair computed. -/
theorem run_get_set_pure {σ : Type u} (s0 : σ) :
    run ((MonadStateOf.get : FreeState σ σ).bind fun s =>
      (MonadStateOf.set s : FreeState σ PUnit)) s0 =
      (PUnit.unit, s0) := by
  have hget : (MonadStateOf.get : FreeState σ σ) =
      (MonadState.get : FreeState σ σ) := rfl
  rw [hget, FreeM.FreeState.get_def]
  rw [FreeM.FreeState.run_bind, FreeM.FreeState.run_get]
  change run (MonadStateOf.set s0 : FreeState σ PUnit) s0 = (PUnit.unit, s0)
  rw [FreeM.FreeState.set_def]
  rw [FreeM.FreeState.run_set]

/-- Put-get equation after running, with an arbitrary continuation:
a read right after writing `s` hands `s` to the continuation. Stated
only for `run`, proved from the pinned run lemmas; not an equality of
raw `FreeM` syntax. -/
theorem run_set_get {σ : Type u} {α : Type v} (s : σ)
    (k : σ → FreeState σ α) (s0 : σ) :
    run ((MonadStateOf.set s : FreeState σ PUnit).bind fun _ =>
      (MonadStateOf.get : FreeState σ σ).bind k) s0 =
      run ((MonadStateOf.set s : FreeState σ PUnit).bind fun _ => k s) s0 := by
  have hget : (MonadStateOf.get : FreeState σ σ) =
      (MonadState.get : FreeState σ σ) := rfl
  rw [hget, FreeM.FreeState.set_def, FreeM.FreeState.get_def,
    FreeM.FreeState.run_bind, FreeM.FreeState.run_set]
  change run ((FreeM.lift FreeM.StateF.get).bind k) s =
    run ((FreeM.lift (FreeM.StateF.set s)).bind fun _ => k s) s0
  rw [FreeM.FreeState.run_bind, FreeM.FreeState.run_get,
    FreeM.FreeState.run_bind, FreeM.FreeState.run_set]

/-- Return-specialized instance of `run_set_get` (`k := pure`),
with the final pair computed. -/
theorem run_set_get_pure {σ : Type u} (s s0 : σ) :
    run ((MonadStateOf.set s : FreeState σ PUnit).bind fun _ =>
      (MonadStateOf.get : FreeState σ σ)) s0 = (s, s) := by
  have hget : (MonadStateOf.get : FreeState σ σ) =
      (MonadState.get : FreeState σ σ) := rfl
  rw [hget, FreeM.FreeState.set_def, FreeM.FreeState.get_def,
    FreeM.FreeState.run_bind, FreeM.FreeState.run_set]
  show run (FreeM.lift FreeM.StateF.get) s = (s, s)
  rw [FreeM.FreeState.run_get]

/-- Put-put equation after running, with an arbitrary continuation:
the first of two writes is discarded. Stated only for `run`, proved
from the pinned run lemmas; not an equality of raw `FreeM` syntax. -/
theorem run_set_set {σ : Type u} {α : Type v} (s s' : σ)
    (k : FreeState σ α) (s0 : σ) :
    run ((MonadStateOf.set s : FreeState σ PUnit).bind fun _ =>
      (MonadStateOf.set s' : FreeState σ PUnit).bind fun _ => k) s0 =
      run ((MonadStateOf.set s' : FreeState σ PUnit).bind fun _ => k) s0 := by
  rw [FreeM.FreeState.set_def, FreeM.FreeState.set_def,
    FreeM.FreeState.run_bind, FreeM.FreeState.run_set]
  change run ((FreeM.lift (FreeM.StateF.set s')).bind fun _ => k) s =
    run ((FreeM.lift (FreeM.StateF.set s')).bind fun _ => k) s0
  rw [FreeM.FreeState.run_bind, FreeM.FreeState.run_set,
    FreeM.FreeState.run_bind, FreeM.FreeState.run_set]

/-- Return-specialized instance of `run_set_set` (`k := pure PUnit.unit`),
with the final pair computed. -/
theorem run_set_set_pure {σ : Type u} (s s' s0 : σ) :
    run ((MonadStateOf.set s : FreeState σ PUnit).bind fun _ =>
      (MonadStateOf.set s' : FreeState σ PUnit)) s0 =
      (PUnit.unit, s') := by
  rw [FreeM.FreeState.set_def, FreeM.FreeState.set_def,
    FreeM.FreeState.run_bind, FreeM.FreeState.run_set]

end FreeState

namespace FreeNondet

/-- Smart constructor: failure (Section 6.4's `fail`), eliminating the empty continuation so
the computation stands at any result type. -/
def fail {α : Type v} : FreeNondet α :=
  (FreeM.lift NondetF.fail).bind fun e => nomatch e

/-- Smart constructor: binary choice (Section 6.4's `pick`) of `x` (`true`) or `y` (`false`),
fixing the left-to-right reading order. -/
def choice {α : Type v} (x y : FreeNondet α) : FreeNondet α :=
  (FreeM.lift NondetF.choice).bind fun b =>
    match b with
    | true => x
    | false => y

end FreeNondet

end FreeM

end Cslib

end
