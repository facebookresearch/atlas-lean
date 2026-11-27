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

/-- **Embedding of simple types into the calculus with references.** Fix a type $B$ of base
types. The embedding $\iota$ sends a simple type over $B$ to a type of the calculus with
references over $B$, by recursion: $\iota(b) = b$ for a base type $b \in B$, and
$\iota(A_1 \to A_2) = \iota(A_1) \to \iota(A_2)$. -/
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

/-- **Embedding of raw STLC terms into the calculus with references.** Fix a type $B$ of base
types. The embedding $\iota$ sends a raw (extrinsically typed, binder-annotated) term of the
simply typed lambda calculus over $B$ to a term of the calculus with references over $B$, by
recursion: a de Bruijn variable $n$ goes to the variable $n$, an application $f\,a$ goes to
$\iota(f)\,\iota(a)$, and an abstraction $\lambda{:}A.\,t$ goes to $\lambda{:}\iota(A).\,\iota(t)$,
where $\iota(A)$ is the embedding of the simple type $A$.

The image is reference-free: it contains no unit value, locations, allocations, dereferences or
assignments. -/
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

/-- **Typing is preserved by the embedding of raw STLC terms.** Fix a type $B$ of base types,
and write $\iota$ for the embeddings of simple types and of raw terms of the simply typed
lambda calculus over $B$ into types and terms of the calculus with references over $B$. Let
$\Gamma$ be a context of simple types, $t$ a raw term and $A$ a simple type such that $t$ has
type $A$ in $\Gamma$. Then for every store typing $S$ we have
$\iota(\Gamma) \mid S \vdash \iota(t) : \iota(A)$, where $\iota(\Gamma)$ is the context
obtained by applying $\iota$ to each entry of $\Gamma$. -/
theorem HasType.ofRaw {Γ : List (Stlc.Ty Base)} {raw : Stlc.RawTm Base}
    {A : Stlc.Ty Base} (h : Stlc.HasType Γ raw A) (S : List (Ty Base)) :
    HasType (Γ.map Ty.ofStlc) S (Term.ofRaw raw) (Ty.ofStlc A) := by
  induction h with
  | @var _ _ n x hx =>
      rw [← Stlc.lookupVar_result_toNat hx]
      exact .var (getElem?_map_ofStlc_toNat x)
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ ih => exact .lam ih

/-- **Typing of embedded intrinsically typed STLC terms.** Fix a type $B$ of base types, and
write $\iota$ for the embeddings of simple types and of raw terms of the simply typed lambda
calculus over $B$ into types and terms of the calculus with references over $B$. Let $\Gamma$ be
a context of simple types, $A$ a simple type and $t$ an intrinsically typed term of type $A$ in
$\Gamma$, and let $\mathrm{erase}(t)$ be the raw term obtained from $t$ by erasing its typing
information while keeping binder annotations. Then for every store typing $S$ we have
$\iota(\Gamma) \mid S \vdash \iota(\mathrm{erase}(t)) : \iota(A)$, where $\iota(\Gamma)$ is the
context obtained by applying $\iota$ to each entry of $\Gamma$. -/
theorem HasType.ofStlc {Γ : List (Stlc.Ty Base)} {A : Stlc.Ty Base}
    (t : Stlc.Tm Γ A) (S : List (Ty Base)) :
    HasType (Γ.map Ty.ofStlc) S (Term.ofRaw t.erase) (Ty.ofStlc A) :=
  HasType.ofRaw (Stlc.HasType.erase t) S

end Cslib.Languages.LambdaCalculus.References
