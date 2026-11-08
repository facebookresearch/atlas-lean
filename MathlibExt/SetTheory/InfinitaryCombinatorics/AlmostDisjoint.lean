/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Cofinality.Club

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 25, Logic 21, Logic 54

/-!
# Almost disjoint family; Almost disjoint modulo the nonstationary ideal; Almost disjoint family
  of functions

## References

* Jech (for `IsAlmostDisjointFamilyKappa`, `AlmostDisjointModNS`, `IsAlmostDisjointFunFamily`)
-/

open Cardinal Ordinal

namespace MetaMathlibExt

-- Logic 25: Almost disjoint family

/-- A family F ⊆ 𝒫(I) is *κ-almost disjoint* if |A| = κ for every A ∈ F and |A ∩ B| < κ for all
distinct A, B ∈ F.
-/
def IsAlmostDisjointFamilyKappa.{u} {I : Type u} (κ : Cardinal) (F : Set (Set I)) : Prop :=
  (∀ A ∈ F, #A = κ) ∧
  (∀ A ∈ F, ∀ B ∈ F, A ≠ B → #((A ∩ B : Set I)) < κ)

-- Logic 21: Almost disjoint modulo the nonstationary ideal

/-- Functions f, g ∈ ∏_{α<ω₁} A_α are *almost disjoint mod the nonstationary ideal* if the set {  α
< ω₁ : f(α) = g(α)  } on which they agree is nonstationary in ω₁.
-/
def AlmostDisjointModNS.{u} {A : Set.Iio (aleph 1 : Cardinal.{u}).ord → Type u}
    (f g : (α : Set.Iio (aleph 1 : Cardinal.{u}).ord) → A α) : Prop :=
  ¬ IsStationary {α : Set.Iio (aleph 1 : Cardinal.{u}).ord | f α = g α}

-- Logic 54: Almost disjoint family of functions

/-- Let κ be a regular cardinal. A family of functions κ → κ is *almost disjoint* if for all f and g
in the family with f≠ g, |{ α ∣ f(α ) = g(α ) }|<κ..
-/
def IsAlmostDisjointFunFamily.{u} {κ : Cardinal.{u}}
    (F : Set (Set.Iio κ.ord → Set.Iio κ.ord)) : Prop :=
  F.Pairwise fun f g => #{α : Set.Iio κ.ord | f α = g α} < Cardinal.lift.{u+1} κ

end MetaMathlibExt

end
