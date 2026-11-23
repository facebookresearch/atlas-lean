/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.PiZeroMapEndCriterion

/-!
# Tests for the π₀ and automorphism-group criterion

Public-only clients exercise the all-universe criterion, identity maps,
empty and disconnected simplicial sets, and arbitrary hom-sets. No topology,
realization, weak-equivalence, Kan-complex, or model API is imported.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FundamentalGroupoid
namespace PiZeroMapEndCriterionTests

private theorem bijective_mapPiZero_id (X : SSet.{u}) :
    Function.Bijective (SSet.mapπ₀ (𝟙 X)) := by
  have h : SSet.mapπ₀ (𝟙 X) = id := by
    funext q
    exact SSet.mapπ₀_id_apply q
  rw [h]
  exact Function.bijective_id

private theorem bijective_mapEnd_id (X : SSet.{u})
    (x : X _⦋0⦌) : Function.Bijective
      ((SSet.mapFundamentalGroupoid (𝟙 X)).map
        (X := SSet.FundamentalGroupoid.mk x)
        (Y := SSet.FundamentalGroupoid.mk x)) := by
  let _ : (SSet.mapFundamentalGroupoid (𝟙 X)).IsEquivalence :=
    SSet.isEquivalence_mapFundamentalGroupoid (𝟙 X)
  exact Functor.FullyFaithful.map_bijective
    (Functor.FullyFaithful.ofFullyFaithful
      (SSet.mapFundamentalGroupoid (𝟙 X)))
    (SSet.FundamentalGroupoid.mk x)
    (SSet.FundamentalGroupoid.mk x)

private theorem identity_client (X : SSet.{u}) :
    (SSet.mapFundamentalGroupoid (𝟙 X)).IsEquivalence :=
  SSet.isEquivalence_mapFundamentalGroupoid_of_bijective_mapπ₀_mapEnd
    (𝟙 X) (bijective_mapPiZero_id X) (bijective_mapEnd_id X)

section Symbolic

variable {X Y : SSet.{u}} (f : X ⟶ Y)
  (h₀ : Function.Bijective (SSet.mapπ₀ f))
  (h₁ : ∀ x : X _⦋0⦌, Function.Bijective
    ((SSet.mapFundamentalGroupoid f).map
      (X := SSet.FundamentalGroupoid.mk x)
      (Y := SSet.FundamentalGroupoid.mk x)))

example : (SSet.mapFundamentalGroupoid f).IsEquivalence :=
  SSet.isEquivalence_mapFundamentalGroupoid_of_bijective_mapπ₀_mapEnd
    f h₀ h₁

example (a b : SSet.FundamentalGroupoid X) :
    Function.Bijective
      ((SSet.mapFundamentalGroupoid f).map (X := a) (Y := b)) := by
  let _ : (SSet.mapFundamentalGroupoid f).IsEquivalence :=
    SSet.isEquivalence_mapFundamentalGroupoid_of_bijective_mapπ₀_mapEnd
      f h₀ h₁
  exact Functor.FullyFaithful.map_bijective
    (Functor.FullyFaithful.ofFullyFaithful
      (SSet.mapFundamentalGroupoid f)) a b

end Symbolic

section ConcreteUniverses

example {X Y : SSet.{1}} (f : X ⟶ Y)
    (h₀ : Function.Bijective (SSet.mapπ₀ f))
    (h₁ : ∀ x : X _⦋0⦌, Function.Bijective
      ((SSet.mapFundamentalGroupoid f).map
        (X := SSet.FundamentalGroupoid.mk x)
        (Y := SSet.FundamentalGroupoid.mk x))) :
    (SSet.mapFundamentalGroupoid f).IsEquivalence :=
  SSet.isEquivalence_mapFundamentalGroupoid_of_bijective_mapπ₀_mapEnd
    f h₀ h₁

example {X Y : SSet.{0}} (f : X ⟶ Y)
    (h₀ : Function.Bijective (SSet.mapπ₀ f))
    (h₁ : ∀ x : X _⦋0⦌, Function.Bijective
      ((SSet.mapFundamentalGroupoid f).map
        (X := SSet.FundamentalGroupoid.mk x)
        (Y := SSet.FundamentalGroupoid.mk x))) :
    (SSet.mapFundamentalGroupoid f).IsEquivalence :=
  SSet.isEquivalence_mapFundamentalGroupoid_of_bijective_mapπ₀_mapEnd
    f h₀ h₁

end ConcreteUniverses

section IdentityBoundaries

example (X : SSet.{u}) :
    (SSet.mapFundamentalGroupoid (𝟙 X)).IsEquivalence :=
  identity_client X

example :
    (SSet.mapFundamentalGroupoid (𝟙 (⊥_ SSet.{u}))).IsEquivalence :=
  identity_client (⊥_ SSet.{u})

private abbrev twoPointCoproduct : SSet.{u} :=
  (Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u})

example :
    (SSet.mapFundamentalGroupoid (𝟙 twoPointCoproduct.{u})).IsEquivalence :=
  identity_client twoPointCoproduct.{u}

end IdentityBoundaries

#print axioms SSet.isEquivalence_mapFundamentalGroupoid_of_bijective_mapπ₀_mapEnd

end PiZeroMapEndCriterionTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet.FundamentalGroupoid

end
