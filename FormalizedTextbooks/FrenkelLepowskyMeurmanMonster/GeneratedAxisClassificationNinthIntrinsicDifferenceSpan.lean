/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIntrinsicFibers

/-! Repeated differences of an actual marking carrier recover a subspace intrinsically.
The construction is preserved by every genuine linear equivalence preserving that carrier.
The finite Ninth marking enumeration is a separate certificate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Marked points whose translation by the specified difference remains marked. -/
def generatedNinthDifferenceWitnesses (C : Set LeechModTwo) (u : LeechModTwo) :
    Set LeechModTwo := {v | v ∈ C ∧ v + u ∈ C}

/-- The number of directed marked pairs realizing a given difference. -/
def generatedNinthDifferenceMultiplicity (C : Set LeechModTwo) (u : LeechModTwo) : ℕ :=
  Nat.card (generatedNinthDifferenceWitnesses C u)

/-- A genuine linear equivalence bijects the complete difference witnesses. -/
def generatedNinthDifferenceWitnessEquiv
    (f : LeechModTwo ≃ₗ[ZMod 2] LeechModTwo)
    (C : Set LeechModTwo) (u : LeechModTwo) :
    generatedNinthDifferenceWitnesses C u ≃
      generatedNinthDifferenceWitnesses (f '' C) (f u) where
  toFun v := ⟨f v.val, ⟨⟨v.val, v.property.1, rfl⟩,
    ⟨v.val + u, v.property.2, map_add f v.val u⟩⟩⟩
  invFun v := ⟨f.symm v.val, by
    obtain ⟨a, ha, hea⟩ := v.property.1
    obtain ⟨b, hb, heb⟩ := v.property.2
    have hv : f.symm v.val = a := by rw [← hea, f.symm_apply_apply]
    have hu : f.symm v.val + u = b := by
      apply f.injective
      rw [map_add, f.apply_symm_apply]
      exact heb.symm
    exact ⟨hv ▸ ha, hu ▸ hb⟩⟩
  left_inv v := Subtype.ext (f.symm_apply_apply v.val)
  right_inv v := Subtype.ext (f.apply_symm_apply v.val)

/-- Difference multiplicity depends only on the actual carrier and linear structure. -/
theorem generatedNinth_difference_multiplicity_map
    (f : LeechModTwo ≃ₗ[ZMod 2] LeechModTwo)
    (C : Set LeechModTwo) (u : LeechModTwo) :
    generatedNinthDifferenceMultiplicity (f '' C) (f u) =
      generatedNinthDifferenceMultiplicity C u :=
  (Nat.card_congr (generatedNinthDifferenceWitnessEquiv f C u)).symm

/-- Differences with at least a specified number of actual marked witnesses. -/
def generatedNinthRepeatedDifferences (C : Set LeechModTwo) (n : ℕ) : Set LeechModTwo :=
  {u | n ≤ generatedNinthDifferenceMultiplicity C u}

/-- Repeated differences are transported as an entire set. -/
theorem generatedNinth_repeated_differences_map
    (f : LeechModTwo ≃ₗ[ZMod 2] LeechModTwo) (C : Set LeechModTwo) (n : ℕ) :
    f '' generatedNinthRepeatedDifferences C n =
      generatedNinthRepeatedDifferences (f '' C) n := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    change n ≤ generatedNinthDifferenceMultiplicity (f '' C) (f v)
    rw [generatedNinth_difference_multiplicity_map]
    exact hv
  · intro hu
    refine ⟨f.symm u, ?_, f.apply_symm_apply u⟩
    change n ≤ generatedNinthDifferenceMultiplicity C (f.symm u)
    rw [← generatedNinth_difference_multiplicity_map f C (f.symm u), f.apply_symm_apply]
    exact hu

/-- The full linear subspace recovered from repeated actual marking differences. -/
def generatedNinthRepeatedDifferenceSpan (C : Set LeechModTwo) (n : ℕ) :
    Submodule (ZMod 2) LeechModTwo :=
  Submodule.span (ZMod 2) (generatedNinthRepeatedDifferences C n)

/-- The recovered subspace commutes with every genuine linear equivalence. -/
theorem generatedNinth_repeated_difference_span_map
    (f : LeechModTwo ≃ₗ[ZMod 2] LeechModTwo) (C : Set LeechModTwo) (n : ℕ) :
    (generatedNinthRepeatedDifferenceSpan C n).map f.toLinearMap =
      generatedNinthRepeatedDifferenceSpan (f '' C) n := by
  rw [generatedNinthRepeatedDifferenceSpan, Submodule.map_span]
  change Submodule.span (ZMod 2) (f '' generatedNinthRepeatedDifferences C n) = _
  rw [generatedNinth_repeated_differences_map]
  rfl

/-- Preserving an actual marking carrier preserves its recovered full subspace. -/
theorem generatedNinth_repeated_difference_span_preserved
    (f : LeechModTwo ≃ₗ[ZMod 2] LeechModTwo) (C : Set LeechModTwo) (n : ℕ)
    (hC : f '' C = C) :
    (generatedNinthRepeatedDifferenceSpan C n).map f.toLinearMap =
      generatedNinthRepeatedDifferenceSpan C n := by
  rw [generatedNinth_repeated_difference_span_map, hC]

/-- The whole family of affine-fiber spans is intrinsic to the marking carrier. -/
theorem generatedNinth_repeated_difference_fiber_family_preserved
    (f : LeechModTwo ≃ₗ[ZMod 2] LeechModTwo) (C : Set LeechModTwo) (n : ℕ)
    (hC : f '' C = C) :
    (fun W : Submodule (ZMod 2) LeechModTwo => W.map f.toLinearMap) ''
        generatedNinthIntrinsicFiberFamily (generatedNinthRepeatedDifferenceSpan C n) C =
      generatedNinthIntrinsicFiberFamily (generatedNinthRepeatedDifferenceSpan C n) C :=
  generatedNinth_intrinsic_fiber_family_preserved f _ C
    (generatedNinth_repeated_difference_span_preserved f C n hC) hC

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
