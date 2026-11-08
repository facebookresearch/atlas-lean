/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The simply typed lambda calculus with references: typing
-/
module

public import CSLibExt.Languages.LambdaCalculus.References.Syntax
public import Mathlib.Data.List.Forall2

/-!
# Typing with store typings

`HasType Γ S t T` is the judgment `Γ | Σ ⊢ t : T` of Pierce, *Types and
Programming Languages*, Figure 13-1: `Γ` lists the types of the free de Bruijn
variables (index `0` first) and the store typing `S` lists the types of the
values held at locations `0, 1, …`. (`Σ` is reserved syntax in Lean, so the
store typing is written `S`.)

`StoreTyped Γ S μ` is TAPL's `Γ | Σ ⊢ μ` (Definition 13.5.1): the store `μ`
and the store typing `S` have the same domain, and the value at each location
has the type `S` assigns to it. TAPL's stores bind locations to values by
their grammar; stores here are lists of terms, so `StoreTyped` also requires
each entry to be a value.

The canonical-forms lemmas characterize the values of each type.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.References

universe u

variable {Base : Type u}

/-- The typing judgment `Γ | S ⊢ t : T` (TAPL Figure 13-1). -/
inductive HasType : List (Ty Base) → List (Ty Base) → Term Base → Ty Base → Prop
  | var {Γ S : List (Ty Base)} {x : Nat} {T : Ty Base} (hx : Γ[x]? = some T) :
      HasType Γ S (.var x) T
  | lam {Γ S : List (Ty Base)} {T₁ T₂ : Ty Base} {body : Term Base}
      (hbody : HasType (T₁ :: Γ) S body T₂) :
      HasType Γ S (.lam T₁ body) (.arr T₁ T₂)
  | app {Γ S : List (Ty Base)} {T₁ T₂ : Ty Base} {f a : Term Base}
      (hf : HasType Γ S f (.arr T₁ T₂)) (ha : HasType Γ S a T₁) :
      HasType Γ S (.app f a) T₂
  | unit {Γ S : List (Ty Base)} : HasType Γ S .unit .unit
  | loc {Γ S : List (Ty Base)} {l : Nat} {T : Ty Base} (hl : S[l]? = some T) :
      HasType Γ S (.loc l) (.ref T)
  | ref {Γ S : List (Ty Base)} {t : Term Base} {T : Ty Base}
      (ht : HasType Γ S t T) :
      HasType Γ S (.ref t) (.ref T)
  | deref {Γ S : List (Ty Base)} {t : Term Base} {T : Ty Base}
      (ht : HasType Γ S t (.ref T)) :
      HasType Γ S (.deref t) T
  | assign {Γ S : List (Ty Base)} {t₁ t₂ : Term Base} {T : Ty Base}
      (ht₁ : HasType Γ S t₁ (.ref T)) (ht₂ : HasType Γ S t₂ T) :
      HasType Γ S (.assign t₁ t₂) .unit

/-- A store is well typed, `Γ | S ⊢ μ` (TAPL Definition 13.5.1): it has one
entry per location of `S`, and the entry at each location is a value of the
type `S` assigns to it. -/
def StoreTyped (Γ S : List (Ty Base)) (μ : List (Term Base)) : Prop :=
  List.Forall₂ (fun v T => v.Value ∧ HasType Γ S v T) μ S

namespace StoreTyped

variable {Γ S : List (Ty Base)} {μ : List (Term Base)}

theorem length_eq (h : StoreTyped Γ S μ) : μ.length = S.length :=
  List.Forall₂.length_eq h

/-- Every location the store typing knows holds a value of the right type. -/
theorem exists_of_getElem? {l : Nat} {T : Ty Base} (h : StoreTyped Γ S μ)
    (hl : S[l]? = some T) : ∃ v, μ[l]? = some v ∧ v.Value ∧ HasType Γ S v T := by
  have hlt : l < S.length := (List.getElem?_eq_some_iff.mp hl).1
  have hltμ : l < μ.length := by rw [h.length_eq]; exact hlt
  refine ⟨μ[l], List.getElem?_eq_getElem hltμ, ?_⟩
  have hT : S[l] = T := (List.getElem?_eq_some_iff.mp hl).2
  rw [← hT]
  exact List.forall₂_iff_get.mp h |>.2 l hltμ hlt

end StoreTyped

namespace HasType

variable {Γ S : List (Ty Base)} {v : Term Base}

/-- Canonical forms for function types: a value of type `T₁ → T₂` is an
abstraction with parameter type `T₁`. -/
theorem lam_of_value {T₁ T₂ : Ty Base} (hv : v.Value) (h : HasType Γ S v (.arr T₁ T₂)) :
    ∃ body, v = .lam T₁ body := by
  cases hv with
  | lam T body =>
      cases h
      exact ⟨body, rfl⟩
  | unit => cases h
  | loc l => cases h

/-- Canonical forms for reference types: a value of type `Ref T` is a
location that the store typing assigns type `T`. -/
theorem loc_of_value {T : Ty Base} (hv : v.Value) (h : HasType Γ S v (.ref T)) :
    ∃ l, v = .loc l ∧ S[l]? = some T := by
  cases hv with
  | lam T body => cases h
  | unit => cases h
  | loc l =>
      cases h with
      | loc hl => exact ⟨l, rfl, hl⟩

/-- Canonical forms for `Unit`: the only value of type `Unit` is `unit`. -/
theorem unit_of_value (hv : v.Value) (h : HasType Γ S v .unit) : v = .unit := by
  cases hv with
  | lam T body => cases h
  | unit => rfl
  | loc l => cases h

/-- Base types have no values. -/
theorem not_value_base {b : Base} (hv : v.Value) (h : HasType Γ S v (.base b)) : False := by
  cases hv <;> cases h

end HasType

end Cslib.Languages.LambdaCalculus.References
