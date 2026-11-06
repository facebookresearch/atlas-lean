/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.MiniImp.Semantics

@[expose] public section

namespace CSLibExt.Languages.MiniImp

/-- Boolean-expression truth is computably decidable, without classical
choice. -/
instance bevalDecidable (b : BExp) (s : State) : Decidable (beval b s) :=
  match b with
  | .tru => inferInstanceAs (Decidable True)
  | .le a b => inferInstanceAs (Decidable (evalA a s ≤ evalA b s))
  | .and a b => @instDecidableAnd _ _ (bevalDecidable a s) (bevalDecidable b s)
  | .not b => @instDecidableNot _ (bevalDecidable b s)

/-- Fuel bounds recursion depth, not instruction count. `none` means exhausted
fuel or an invalid read. Loop annotations are ghost data and are never
evaluated. -/
def exec : Nat → Stmt → State → Option State
  | 0, _, _ => none
  | fuel + 1, c, s =>
    match c with
    | .skip => some s
    | .assign x e => some (s.update x (evalA e s))
    | .read x xs e =>
        if h : evalA e s < xs.size then
          some (s.update x xs[evalA e s]) else none
    | .seq a b => (exec fuel a s).bind (exec fuel b)
    | .if_ b a c => if beval b s then exec fuel a s else exec fuel c s
    | .while b I c =>
        if beval b s then
          (exec fuel c s).bind (exec fuel (.while b I c)) else some s

/-- Every successful interpreter run is a derivation of the actual MiniImp
semantics. -/
theorem exec_sound {fuel : Nat} {c : Stmt} {s t : State}
    (h : exec fuel c s = some t) : BigStep c s t := by
  induction fuel generalizing c s t with
  | zero => simp [exec] at h
  | succ fuel ih =>
      cases c with
      | skip => cases h; exact .skip
      | assign x e => cases h; exact .assign
      | read x xs e =>
          simp only [exec] at h
          split at h
          next hb => cases h; exact .read hb
          next => contradiction
      | seq a b =>
          simp only [exec, Option.bind_eq_some_iff] at h
          obtain ⟨u, ha, hb⟩ := h
          exact .seq (ih ha) (ih hb)
      | if_ b a c =>
          simp only [exec] at h
          split at h
          next hb => exact .ifTrue hb (ih h)
          next hb => exact .ifFalse hb (ih h)
      | «while» b I c =>
          simp only [exec] at h
          split at h
          next hb =>
            obtain ⟨u, hc, hw⟩ := Option.bind_eq_some_iff.mp h
            exact .whileTrue hb (ih hc) (ih hw)
          next hb => cases h; exact .whileFalse hb

/-- Out-of-bounds reads have no successful semantic derivation. -/
theorem read_no_bigStep {x : String} {xs : Array Nat} {e : AExp} {s t : State}
    (hbad : ¬ evalA e s < xs.size) : ¬ BigStep (.read x xs e) s t := by
  intro h
  cases h with
  | read hb => exact hbad hb

/-- An invalid read fails for every fuel, never supplying a default value. -/
theorem exec_read_invalid (fuel : Nat) {x : String} {xs : Array Nat}
    {e : AExp} {s : State} (hbad : ¬ evalA e s < xs.size) :
    exec fuel (.read x xs e) s = none := by
  cases fuel <;> simp [exec, hbad]

end CSLibExt.Languages.MiniImp
