/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitions

/-! The actual conjugacy-orbit mechanism behind the double-coset reduction of
Höhn--Seysen §3.2. Full Ω conjugates retain the central sign discarded by the
binary quotient. A finite stabilizer-orbit certificate on these elements gives
actual transition coverage without assuming a double-coset decomposition. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual inverse conjugate of source Ω, with its full central phase. -/
noncomputable def generatedAxisGlobalOmegaConjugate (h : H) : H :=
  h⁻¹ * inclQ sourceOmegaQ * h

/-- Equal full Ω conjugates are precisely equal genuine transition cosets. -/
theorem generatedAxisGlobalOmegaConjugate_eq_iff (a b : H) :
    generatedAxisGlobalOmegaConjugate a = generatedAxisGlobalOmegaConjugate b ↔
      QuotientGroup.rightRel localOmegaStabilizer a b := by
  rw [QuotientGroup.rightRel_apply, localOmegaStabilizer,
    Subgroup.mem_centralizer_singleton_iff]
  unfold generatedAxisGlobalOmegaConjugate
  constructor
  · intro he
    calc
      b * a⁻¹ * inclQ sourceOmegaQ =
          b * (a⁻¹ * inclQ sourceOmegaQ * a) * a⁻¹ := by group
      _ = b * (b⁻¹ * inclQ sourceOmegaQ * b) * a⁻¹ := by rw [he]
      _ = inclQ sourceOmegaQ * (b * a⁻¹) := by group
  · intro he
    calc
      a⁻¹ * inclQ sourceOmegaQ * a =
          b⁻¹ * (b * a⁻¹ * inclQ sourceOmegaQ) * a := by group
      _ = b⁻¹ * (inclQ sourceOmegaQ * (b * a⁻¹)) * a := by rw [he]
      _ = b⁻¹ * inclQ sourceOmegaQ * b := by group

/-- The actual Ω conjugacy orbit has one element per actual transition coset. -/
noncomputable def generatedAxisGlobalOmegaOrbitEquiv :
    generatedAxisTransitionCosetSpace ≃ Set.range generatedAxisGlobalOmegaConjugate :=
  Equiv.ofBijective
    (Quotient.lift (fun h : H =>
      (⟨generatedAxisGlobalOmegaConjugate h, h, rfl⟩ :
        Set.range generatedAxisGlobalOmegaConjugate)) (by
      intro a b hab
      apply Subtype.ext
      exact (generatedAxisGlobalOmegaConjugate_eq_iff a b).mpr hab))
    (by
      constructor
      · intro a b hab
        induction a using Quotient.inductionOn with
        | h a =>
          induction b using Quotient.inductionOn with
          | h b =>
            apply Quotient.sound
            exact (generatedAxisGlobalOmegaConjugate_eq_iff a b).mp
              (congrArg Subtype.val hab)
      · rintro ⟨x, h, rfl⟩
        exact ⟨Quotient.mk _ h, rfl⟩)

/-- There are exactly 16,584,750 full Ω conjugates in actual H. -/
theorem generatedAxisGlobalOmegaOrbit_card :
    Nat.card (Set.range generatedAxisGlobalOmegaConjugate) = 16584750 := by
  rw [← Nat.card_congr generatedAxisGlobalOmegaOrbitEquiv]
  exact generatedAxisTransitionCosetSpace_card

/-- Covering full Ω conjugates by the stabilizer's orbits produces the actual
N--C decomposition required by the transition certificate. -/
theorem generatedAxisGlobal_decompose_of_omega_cover {κ : Type*}
    (C : Subgroup H) (r : κ → H)
    (hcover : ∀ h : H, ∃ j c, c ∈ C ∧
      generatedAxisGlobalOmegaConjugate h =
        c⁻¹ * generatedAxisGlobalOmegaConjugate (r j) * c)
    (h : H) :
    ∃ j n c, n ∈ localOmegaStabilizer ∧ c ∈ C ∧ h = n * r j * c := by
  obtain ⟨j, c, hc, he⟩ := hcover h
  have hr : generatedAxisGlobalOmegaConjugate h =
      generatedAxisGlobalOmegaConjugate (r j * c) := by
    rw [he]
    unfold generatedAxisGlobalOmegaConjugate
    group
  have hn : h * (r j * c)⁻¹ ∈ localOmegaStabilizer :=
    QuotientGroup.rightRel_apply.mp
      ((generatedAxisGlobalOmegaConjugate_eq_iff (r j * c) h).mp hr.symm)
  refine ⟨j, h * (r j * c)⁻¹, c, hn, hc, ?_⟩
  group

/-- Full Ω stabilizer-orbit coverage and checked representative transitions
suffice for actual global triality closure. -/
theorem generatedAxisGlobal_triality_of_omega_cover {ι κ : Type*}
    (v : ι → GriessSpace) (C : ι → Subgroup H) (r : ι → κ → H)
    (hfix : ∀ i c, c ∈ C i → rhoLocal c (v i) = v i)
    (hcover : ∀ i h, ∃ j c, c ∈ C i ∧
      generatedAxisGlobalOmegaConjugate h =
        c⁻¹ * generatedAxisGlobalOmegaConjugate (r i j) * c)
    (htransition : ∀ i j,
      sExtra (rhoLocal (r i j) (v i)) ∈ generatedLocalOrbitUnion v) :
    Set.MapsTo sExtra (generatedLocalOrbitUnion v) (generatedLocalOrbitUnion v) := by
  apply generatedLocalOrbitUnion_triality_of_double_cosets v localOmegaStabilizer C r hfix
  · intro n hn
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_conjugate ⟨n, hn⟩
    refine ⟨k.val, ?_⟩
    have he := congrArg Subtype.val hk
    change sExtra * rhoLocal n * sExtra⁻¹ = rhoLocal k.val at he
    calc
      sExtra * rhoLocal n = (sExtra * rhoLocal n * sExtra⁻¹) * sExtra := by group
      _ = rhoLocal k.val * sExtra := by rw [he]
  · intro i h
    exact generatedAxisGlobal_decompose_of_omega_cover (C i) (r i) (hcover i) h
  · exact htransition

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
