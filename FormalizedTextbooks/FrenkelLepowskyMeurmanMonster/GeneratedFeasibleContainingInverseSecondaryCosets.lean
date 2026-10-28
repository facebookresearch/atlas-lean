/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingNewDestinationSeparation

/-! Genuine right transition cosets are the inverse images of the original secondary axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Inverse representatives send actual right cosets to the original group orbit. -/
def generatedFeasibleContainingInverseOrbitMap {Γ X : Type*} [Group Γ] [MulAction Γ X] (x : X)
    (N : Subgroup Γ) (hN : N = MulAction.stabilizer Γ x) :
    Quotient (QuotientGroup.rightRel N) → MulAction.orbit Γ x :=
  Quotient.lift (fun g => ⟨g⁻¹ • x, ⟨g⁻¹, rfl⟩⟩) (by
    intro g h hrel
    apply Subtype.ext
    have hh := QuotientGroup.rightRel_apply.mp hrel
    rw [hN] at hh
    change (h * g⁻¹) • x = x at hh
    rw [mul_smul] at hh
    apply (MulAction.toPerm h).injective
    change h • (g⁻¹ • x) = h • (h⁻¹ • x)
    rw [smul_inv_smul]
    exact hh)

theorem generatedFeasibleContainingInverseOrbitMap_bijective {Γ X : Type*} [Group Γ] [MulAction Γ X]
    (x : X) (N : Subgroup Γ) (hN : N = MulAction.stabilizer Γ x) :
    Function.Bijective (generatedFeasibleContainingInverseOrbitMap x N hN) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h g =>
      induction b using Quotient.inductionOn with
      | h h =>
        intro he
        have hv := congrArg Subtype.val he
        change g⁻¹ • x = h⁻¹ • x at hv
        apply Quotient.sound
        change QuotientGroup.rightRel N g h
        rw [QuotientGroup.rightRel_apply, hN]
        change (h * g⁻¹) • x = x
        rw [mul_smul, hv, smul_inv_smul]
  · rintro ⟨y, ⟨g, hg⟩⟩
    refine ⟨Quotient.mk _ g⁻¹, Subtype.ext ?_⟩
    change (g⁻¹)⁻¹ • x = y
    rw [inv_inv]
    exact hg

/-- The actual right A/N coset is identified with its genuine inverse secondary-axis image. -/
def generatedFeasibleContainingInverseSecondaryCosets :
    generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair ≃
      generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair :=
  Equiv.ofBijective _ (generatedFeasibleContainingInverseOrbitMap_bijective
    (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
    (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)
    (generatedFeasibleSecondaryAxis_stabilizer generatedFeasiblePhysicalRootPair).symm)

/-- Every original coset representative uses the actual inverse of its entire local word. -/
theorem generatedFeasibleContainingInverseSecondaryCosets_apply
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair) :
    (generatedFeasibleContainingInverseSecondaryCosets
      (Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val =
      rhoLocal h.val⁻¹ (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
  rfl

/-- Original signed short labels give their actual secondary-orbit axis. -/
def generatedFeasibleContainingOriginalSecondaryAxis
    (a : generatedFeasibleOrthogonalSignedShortLabels) :
    generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair :=
  ⟨conwayShortAxis a.val.1 a.val.2, by
    rw [generatedFeasibleSecondaryLocalOrbit_eq_physical]
    exact ⟨a, rfl⟩⟩

theorem generatedFeasibleContainingOriginalSecondaryAxis_bijective :
    Function.Bijective generatedFeasibleContainingOriginalSecondaryAxis := by
  constructor
  · intro a b he
    apply Subtype.ext
    exact @generatedAxis_signed_injective a.val b.val (congrArg Subtype.val he)
  · rintro ⟨x, hx⟩
    rw [generatedFeasibleSecondaryLocalOrbit_eq_physical] at hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, Subtype.ext ha⟩

/-- The complete original signed-short catalogue is exactly the actual secondary orbit. -/
def generatedFeasibleContainingOriginalSecondaryAxisEquiv :
    generatedFeasibleOrthogonalSignedShortLabels ≃
      generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair :=
  Equiv.ofBijective _ generatedFeasibleContainingOriginalSecondaryAxis_bijective

/-- Actual right input cosets biject with all original perpendicular signed-short addresses. -/
def generatedFeasibleContainingInverseSecondaryAddresses :
    generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair ≃
      generatedFeasibleOrthogonalSignedShortLabels :=
  generatedFeasibleContainingInverseSecondaryCosets.trans
    generatedFeasibleContainingOriginalSecondaryAxisEquiv.symm

/-- The address records the original entire inverse-word secondary image, including its sign. -/
theorem generatedFeasibleContainingInverseSecondaryAddresses_axis
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair) :
    let a := generatedFeasibleContainingInverseSecondaryAddresses
      (Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)
    conwayShortAxis a.val.1 a.val.2 =
      rhoLocal h.val⁻¹ (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
  have he := generatedFeasibleContainingOriginalSecondaryAxisEquiv.apply_symm_apply
    (generatedFeasibleContainingInverseSecondaryCosets
      (Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h))
  exact congrArg Subtype.val he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
