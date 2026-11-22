/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Embedding the pure STLC into the calculus with references
-/
module

public import CSLibExt.Languages.LambdaCalculus.References.Typing
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Elaboration

/-!
# Embedding the pure STLC

The pure simply typed lambda calculus of `../DeBruijn/Stlc/` embeds into the
reference-free fragment of this calculus (as a proper sublanguage: it has no
`Unit`). `Term.ofRaw` embeds its extrinsic raw terms (`Stlc.RawTm`, with
binder annotations) and `HasType.ofRaw` carries their typing judgment
(`Stlc.HasType`) over, under every store typing. Composed with the existing
erasure `Stlc.Tm.erase` of intrinsically typed terms, `HasType.ofStlc` embeds
`Stlc.Tm Γ A`.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.References

universe u

variable {Base : Type u}

/-- Simple types as types of the calculus with references. -/
def Ty.ofStlc : Stlc.Ty Base → Ty Base
  | .base b => .base b
  | .arr A B => .arr (ofStlc A) (ofStlc B)

@[simp] theorem Ty.ofStlc_base (b : Base) : Ty.ofStlc (.base b) = .base b := rfl

@[simp] theorem Ty.ofStlc_arr (A B : Stlc.Ty Base) :
    Ty.ofStlc (.arr A B) = .arr (Ty.ofStlc A) (Ty.ofStlc B) := rfl

theorem Ty.ofStlc_injective : Function.Injective (Ty.ofStlc (Base := Base)) := by
  intro A B h
  induction A generalizing B with
  | base b =>
      cases B with
      | base c => cases h; rfl
      | arr => cases h
  | arr A₁ A₂ ih₁ ih₂ =>
      cases B with
      | base => cases h
      | arr B₁ B₂ =>
          simp only [ofStlc_arr, Ty.arr.injEq] at h
          rw [ih₁ h.1, ih₂ h.2]

/-- Embed a raw (extrinsic) STLC term of `../DeBruijn/Stlc/Elaboration.lean`
as a reference-free term. -/
def Term.ofRaw : Stlc.RawTm Base → Term Base
  | .var n => .var n
  | .app f a => .app (ofRaw f) (ofRaw a)
  | .lam A body => .lam (Ty.ofStlc A) (ofRaw body)

theorem Term.ofRaw_injective : Function.Injective (Term.ofRaw (Base := Base)) := by
  intro s t h
  induction s generalizing t with
  | var n => cases t <;> cases h; rfl
  | app f a ihf iha =>
      cases t with
      | app g b =>
          simp only [ofRaw, Term.app.injEq] at h
          rw [ihf h.1, iha h.2]
      | _ => cases h
  | lam A body ih =>
      cases t with
      | lam B body' =>
          simp only [ofRaw, Term.lam.injEq] at h
          rw [Ty.ofStlc_injective h.1, ih h.2]
      | _ => cases h

theorem getElem?_map_ofStlc_toNat {Γ : List (Stlc.Ty Base)} {A : Stlc.Ty Base}
    (x : Stlc.Var Γ A) : (Γ.map Ty.ofStlc)[x.toNat]? = some (Ty.ofStlc A) := by
  induction x with
  | zero => rfl
  | succ x ih => simpa [Stlc.Var.toNat] using ih

/-- A well-typed raw STLC term embeds as a term of the embedded type, under
any store typing. -/
theorem HasType.ofRaw {Γ : List (Stlc.Ty Base)} {raw : Stlc.RawTm Base}
    {A : Stlc.Ty Base} (h : Stlc.HasType Γ raw A) (S : List (Ty Base)) :
    HasType (Γ.map Ty.ofStlc) S (Term.ofRaw raw) (Ty.ofStlc A) := by
  induction h with
  | @var _ _ n x hx =>
      rw [← Stlc.lookupVar_result_toNat hx]
      exact .var (getElem?_map_ofStlc_toNat x)
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ ih => exact .lam ih

/-- An intrinsically typed STLC term, erased and embedded, has the embedded
type under any store typing. -/
theorem HasType.ofStlc {Γ : List (Stlc.Ty Base)} {A : Stlc.Ty Base}
    (t : Stlc.Tm Γ A) (S : List (Ty Base)) :
    HasType (Γ.map Ty.ofStlc) S (Term.ofRaw t.erase) (Ty.ofStlc A) :=
  HasType.ofRaw (Stlc.HasType.erase t) S

end Cslib.Languages.LambdaCalculus.References
