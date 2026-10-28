/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite actual subgroup images and faithful restrictions from exact cardinality. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationImageSubgroupLowerBound
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The canonical map from an actual subgroup onto its actual homomorphic image is surjective. -/
theorem y322Subgroup_image_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (K : Subgroup G) : Function.Surjective
      (fun x : K => (⟨f x.val, ⟨x.val, x.property, rfl⟩⟩ : K.map f)) := by
  intro y
  obtain ⟨x, hx, he⟩ := y.property
  refine ⟨⟨x, hx⟩, ?_⟩
  exact Subtype.ext he

/-- An actual image of a finite source subgroup is finite. -/
theorem y322FiniteSubgroup_image_finite {G H : Type*} [Group G] [Group H]
    (f : G →* H) (K : Subgroup G) [Finite K] : Finite (K.map f) :=
  Finite.of_surjective _ (y322Subgroup_image_surjective f K)

/-- An actual finite source subgroup bounds the cardinality of its actual homomorphic image. -/
theorem y322FiniteSubgroup_image_card_le {G H : Type*} [Group G] [Group H]
    (f : G →* H) (K : Subgroup G) [Finite K] : Nat.card (K.map f) ≤ Nat.card K :=
  Nat.card_le_card_of_surjective _ (y322Subgroup_image_surjective f K)

/-- Equality of the actual image and finite subgroup orders proves a faithful restriction. -/
theorem y322FiniteSubgroup_image_injective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (K : Subgroup G) [Finite K]
    (hc : Nat.card (K.map f) = Nat.card K) : Function.Injective (f.comp K.subtype) := by
  let := y322FiniteSubgroup_image_finite f K
  let := Fintype.ofFinite K
  let := Fintype.ofFinite (K.map f)
  let g : K → K.map f := fun x => ⟨f x.val, ⟨x.val, x.property, rfl⟩⟩
  have he : Fintype.card K = Fintype.card (K.map f) := by
    simpa only [Nat.card_eq_fintype_card] using hc.symm
  have hi : Function.Injective g :=
    ((Fintype.bijective_iff_surjective_and_card g).mpr
      ⟨y322Subgroup_image_surjective f K, he⟩).1
  intro x y hxy
  apply hi
  exact Subtype.ext hxy

/-- Matching checked source upper and actual image lower bounds prove orders and faithfulness. -/
theorem y322FiniteSubgroup_image_exact_order {G H : Type*} [Group G] [Group H]
    (f : G →* H) (K : Subgroup G) [Finite K] (n : ℕ)
    (lower : n ≤ Nat.card (K.map f)) (upper : Nat.card K ≤ n) :
    Nat.card K = n ∧ Nat.card (K.map f) = n ∧ Function.Injective (f.comp K.subtype) := by
  have hle := y322FiniteSubgroup_image_card_le f K
  have hs : Nat.card K = n := Nat.le_antisymm upper (lower.trans hle)
  have ht : Nat.card (K.map f) = n := Nat.le_antisymm (hle.trans upper) lower
  exact ⟨hs, ht, y322FiniteSubgroup_image_injective f K (ht.trans hs.symm)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
