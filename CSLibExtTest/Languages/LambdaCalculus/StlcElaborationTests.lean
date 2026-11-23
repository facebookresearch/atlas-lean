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

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.ElaborationSubstitution

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.ElaborationTests

open scoped CslibStlc

abbrev Atom := Ty.base (Base := Unit) ()

abbrev rawId : RawTm Unit := .lam Atom (.var 0)
abbrev rawConst : RawTm Unit := .lam Atom (.lam Atom (.var 1))
abbrev rawApply : RawTm Unit :=
  .lam (Atom ⇒ Atom) (.lam Atom (.app (.var 1) (.var 0)))
abbrev rawCompose : RawTm Unit :=
  .lam (Atom ⇒ Atom)
    (.lam (Atom ⇒ Atom)
      (.lam Atom (.app (.var 2) (.app (.var 1) (.var 0)))))

/-- The annotated identity is inferred at the expected type. -/
example : infer [] rawId = some (Atom ⇒ Atom) := by decide

/-- The constant function uses the variable beyond its nearest binder. -/
example : infer [] rawConst = some (Atom ⇒ Atom ⇒ Atom) := by decide

/-- Application elaborates in a context containing both function and argument. -/
example : infer [] rawApply =
    some ((Atom ⇒ Atom) ⇒ Atom ⇒ Atom) := by decide

/-- Composition exercises three binders and two nested applications. -/
example : infer [] rawCompose =
    some ((Atom ⇒ Atom) ⇒ (Atom ⇒ Atom) ⇒ Atom ⇒ Atom) := by
  decide

/-- An unbound de Bruijn index is rejected. -/
example : infer (Base := Unit) [] (.var 0) = none := by decide

/-- Applying an atomic term as a function is rejected. -/
example : infer [Atom] (.app (.var 0) (.var 0)) = none := by decide

/-- Applying a function to an argument of the wrong type is rejected. -/
example : infer [Atom ⇒ Atom] (.app (.var 0) rawId) = none := by decide

/-- Checking agrees with inference on a positive example. -/
example : check [] rawId (Atom ⇒ Atom) = true := by decide

/-- Checking rejects a different requested type. -/
example : check [] rawId Atom = false := by decide

/-- Shifting the free index of a variable changes it by the requested amount. -/
example : (RawTm.var 2 : RawTm Unit).shift 3 = .var 5 := by decide

/-- Shifting respects binders and leaves their bound variable fixed. -/
example : rawId.shift 4 = rawId := by decide

/-- Raw renaming increments a free variable. -/
example : RawTm.rename Nat.succ (.var 2 : RawTm Unit) = .var 3 := by decide

/-- Raw renaming is lifted under binders, preserving index zero. -/
example : RawTm.rename Nat.succ rawId = rawId := by decide

/-- Renaming composition is visible computationally. -/
example :
    RawTm.rename Nat.succ (RawTm.rename Nat.succ (.var 0 : RawTm Unit)) =
      RawTm.rename (Nat.succ ∘ Nat.succ) (.var 0) := by decide

/-- Raw syntax node counts are invariant under renaming. -/
example : (RawTm.rename Nat.succ rawCompose).size = rawCompose.size := by
  simp

/-- The identity term contains only its bound index syntactically. -/
example : RawTm.indices rawId = [0] := by decide

/-- The closedness checker accepts the identity. -/
example : rawId.Closed := by decide

/-- A bare variable is not closed. -/
example : ¬ (RawTm.var 0 : RawTm Unit).Closed := by decide

/-- Simultaneous identity substitution leaves raw syntax unchanged. -/
example : RawTm.substAll RawTm.idSub rawCompose = rawCompose :=
  RawTm.substAll_id rawCompose

/-- A single substitution replaces the nearest variable. -/
example : RawTm.substAll (RawTm.singleSub rawId) (.var 0) = rawId := by rfl

/-- A single substitution decrements older variables. -/
example : RawTm.substAll (RawTm.singleSub rawId) (.var 2) =
    (.var 1 : RawTm Unit) := by rfl

/-- Renaming is the special case of substitution by variables. -/
example : RawTm.rename Nat.succ rawConst =
    RawTm.substAll (fun n => .var (Nat.succ n)) rawConst :=
  RawTm.rename_eq_substAll Nat.succ rawConst

/-- Erasure of intrinsic weakening agrees with raw numerical renaming. -/
example (t : Tm [Atom] Atom) :
    (Tm.weaken (B := Atom) t).erase = RawTm.rename Nat.succ t.erase := by
  simp

/-- Erasure commutes with the identity substitution. -/
example (t : Tm [Atom] Atom) :
    (Tm.subst Sub.id t).erase = RawTm.substAll RawTm.idSub t.erase := by
  exact Tm.erase_subst Sub.id RawTm.idSub subAgrees_id t

/-- Erasure of instantiation is raw simultaneous substitution. -/
example (body : Tm [Atom] Atom) (a : Tm [] Atom) :
    (Tm.instantiate body a).erase =
      RawTm.substAll (RawTm.singleSub a.erase) body.erase := by
  simp

/-- Raw normalization succeeds on a well-typed term. -/
example : (normalizeRaw [] rawId).isSome = true := by decide

/-- Raw normalization rejects ill-typed syntax. -/
example : (normalizeRaw (Base := Unit) [] (.var 0)).isNone = true := by decide

/-- The certified completeness theorem produces an intrinsic witness. -/
example (h : HasType [] rawId (Atom ⇒ Atom)) :
    ∃ t : Tm [] (Atom ⇒ Atom), elaborate [] rawId = some ⟨_, t⟩ :=
  HasType.elaborate_complete h

/-- The certified soundness theorem recovers declarative typing. -/
example {A : Ty Unit} {t : Tm [] A}
    (h : elaborate [] rawId = some ⟨A, t⟩) : HasType [] rawId A :=
  HasType.elaborate_sound h

/-- The returned intrinsic certificate erases to the exact accepted input. -/
example {A : Ty Unit} {t : Tm [] A}
    (h : elaborate [] rawCompose = some ⟨A, t⟩) :
    t.erase = rawCompose :=
  elaborate_faithful h

/-- Inference is deterministic because raw typing is unique. -/
example {raw : RawTm Unit} {A B : Ty Unit}
    (hA : HasType [] raw A) (hB : HasType [] raw B) : A = B :=
  HasType.unique hA hB

/-- Normalization preserves inferred types. -/
example {raw normal : RawTm Unit} {A : Ty Unit}
    (h : normalizeRaw [] raw = some ⟨A, normal⟩) :
    infer [] raw = some A :=
  normalizeRaw_type h

/-- Normalization produces declaratively well-typed syntax. -/
example {raw normal : RawTm Unit} {A : Ty Unit}
    (h : normalizeRaw [] raw = some ⟨A, normal⟩) :
    HasType [] normal A :=
  normalizeRaw_hasType h

/-- Successful raw normalization reaches a fixed point. -/
example {raw normal : RawTm Unit} {A : Ty Unit}
    (h : normalizeRaw [] raw = some ⟨A, normal⟩) :
    normalizeRaw [] normal = some ⟨A, normal⟩ :=
  normalizeRaw_idempotent h

#print axioms Tm.erase_injective
#print axioms HasType.unique
#print axioms HasType.elaborate_complete
#print axioms HasType.elaborate_sound
#print axioms elaborate_faithful
#print axioms normalizeRaw_idempotent
#print axioms Tm.erase_rename
#print axioms Tm.erase_subst
#print axioms Tm.erase_instantiate

end Cslib.Languages.LambdaCalculus.Stlc.ElaborationTests
