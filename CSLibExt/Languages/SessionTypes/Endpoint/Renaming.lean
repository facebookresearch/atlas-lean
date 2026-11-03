/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.NameTransport

/-!
# Binder-aware rekeying of existing π terms

This is a syntax transformation, not a process semantics. Its canonical
lift/substitution/swap specializations are proved against PiCalculus.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- Extend a name transformation under one existing input/ν binder. -/
def under (f : Name → Name) : Name → Name
  | .const n => liftName 0 (f (.const n))
  | .var 0 => .var 0
  | .var (i + 1) => liftName 0 (f (.var i))

/-- The new binder is fixed and outer names are transformed capture-safely. -/
theorem under_lift_zero (f : Name → Name) (a : Name) :
    under f (liftName 0 a) = liftName 0 (f a) := by
  cases a <;> simp [under, liftName]

/-- Capture-safe name transformation of existing processes. Binder bodies
use `under`; this introduces no new syntax or transition relation. -/
def mapProc (f : Name → Name) : Proc → Proc
  | .nil => .nil
  | .out a b p => .out (f a) (f b) (mapProc f p)
  | .inp a p => .inp (f a) (mapProc (under f) p)
  | .par p q => .par (mapProc f p) (mapProc f q)
  | .nu p => .nu (mapProc (under f) p)
  | .repl p => .repl (mapProc f p)
  | .sum p q => .sum (mapProc f p) (mapProc f q)

/-- Extending a scoped transformation under a binder preserves the
canonical scope relation at the incremented source and target depths. -/
theorem under_scoped {n m : Nat} {f : Name → Name}
    (hf : ∀ a, a.ClosedAt n → (f a).ClosedAt m)
    {a : Name} (ha : a.ClosedAt (n + 1)) :
    (under f a).ClosedAt (m + 1) := by
  cases a with
  | const i => exact (hf (.const i) trivial).lift
  | var i =>
    cases i with
    | zero => exact Nat.zero_lt_succ m
    | succ i =>
      have hi : (Name.var i).ClosedAt n := by
        change i < n
        change i + 1 < n + 1 at ha
        omega
      exact (hf (.var i) hi).lift

/-- Under a binder, canonical lifting increases its cutoff by one. -/
theorem under_liftName (k : Nat) : under (liftName k) = liftName (k + 1) := by
  funext a
  cases a with
  | const => rfl
  | var i =>
    cases i with
    | zero => simp [under, liftName]
    | succ i =>
      simpa [under, liftName] using (liftName_liftName_zero k (.var i)).symm

/-- The generic syntax transformation specializes to the existing π lift. -/
theorem mapProc_liftName (k : Nat) (p : Proc) :
    mapProc (liftName k) p = liftProc k p := by
  induction p generalizing k <;> simp [mapProc, liftProc, under_liftName, *]

/-- Under an existing binder, substitution lifts its replacement and
increments its cutoff, exactly as PiCalculus.substProc does. -/
theorem under_substName (b : Name) (k : Nat) :
    under (substName b k) = substName (liftName 0 b) (k + 1) := by
  funext a
  cases a with
  | const => rfl
  | var j =>
    cases j with
    | zero => simp [under, substName]
    | succ i =>
      by_cases hi : i < k
      · have hi' : i + 1 < k + 1 := by omega
        simp [under, substName, hi, hi', liftName]
      · by_cases he : i = k
        · subst i
          simp [under, substName]
        · have hi' : ¬ i + 1 < k + 1 := by omega
          have hip : 1 ≤ i := by omega
          simp [under, substName, hi, he, hi', liftName,
            Nat.sub_add_cancel hip]

/-- Subject and payload substitution are exactly the canonical π operation,
including through all input and restriction binders. -/
theorem mapProc_substName (b : Name) (k : Nat) (p : Proc) :
    mapProc (substName b k) p = substProc b k p := by
  induction p generalizing b k <;>
    simp [mapProc, substProc, under_substName, *]

/-- Capture-safe syntax transport preserves the canonical process scope. -/
theorem mapProc_closedAt {n m : Nat} {f : Name → Name} {p : Proc}
    (hf : ∀ a, a.ClosedAt n → (f a).ClosedAt m) (hp : p.ClosedAt n) :
    (mapProc f p).ClosedAt m := by
  induction p generalizing n m f with
  | nil => trivial
  | out a b p ih => exact ⟨hf a hp.1, hf b hp.2.1, ih hf hp.2.2⟩
  | inp a p ih => exact ⟨hf a hp.1, ih (fun _ h => under_scoped hf h) hp.2⟩
  | par p q ihp ihq => exact ⟨ihp hf hp.1, ihq hf hp.2⟩
  | nu p ih => exact ih (fun _ h => under_scoped hf h) hp
  | repl p ih => exact ih hf hp
  | sum p q ihp ihq => exact ⟨ihp hf hp.1, ihq hf hp.2⟩

/-- Extending a restriction swap under a binder shifts both swapped indices. -/
theorem under_swapNameAt (k : Nat) : under (swapNameAt k) = swapNameAt (k + 1) := by
  funext a
  cases a with
  | const => rfl
  | var j =>
    cases j with
    | zero => simp [under, swapNameAt]
    | succ i =>
      by_cases h₀ : i = k
      · subst i
        simp [under, swapNameAt, liftName, Nat.add_assoc]
      · by_cases h₁ : i = k + 1
        · subst i
          simp [under, swapNameAt, liftName, Nat.add_assoc]
        · simp [under, swapNameAt, liftName, h₀, h₁]

/-- The generic capture-safe map specializes to the existing π restriction swap. -/
theorem mapProc_swapNameAt (k : Nat) (p : Proc) :
    mapProc (swapNameAt k) p = swapProc k p := by
  induction p generalizing k <;> simp [mapProc, swapProc, under_swapNameAt, *]

end Cslib.SessionTypes.Endpoint
