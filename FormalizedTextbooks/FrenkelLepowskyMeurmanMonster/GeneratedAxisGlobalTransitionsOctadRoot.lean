/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary

/-! An actual transition at the canonical octad root. A coordinate singleton
outside the octad fixes that signed-short axis and inverts triality, giving an
explicit local transporter for its second triality image. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The canonical octad has an actual physical coordinate outside its eight-point support. -/
theorem generatedAxisGlobal_octad_outside_point_exists : ∃ j : Fin 24, j ∉ golayOctadSupport 0 := by
  by_contra! h
  have he : golayOctadSupport 0 = Finset.univ := by
    ext j
    simp only [Finset.mem_univ, iff_true]
    exact h j
  have hc := golayOctadSupport_card 0
  rw [he] at hc
  norm_num at hc

/-- A genuine physical coordinate outside the canonical octad's eight-point support. -/
noncomputable def generatedAxisGlobalOctadOutsidePoint : Fin 24 :=
  Classical.choose generatedAxisGlobal_octad_outside_point_exists

/-- Actual odd coordinate cocode chosen outside the canonical octad. -/
noncomputable def generatedAxisGlobalOctadReflection : Q :=
  cocodeQ (fun k =>
    (golayGeneratorBit k generatedAxisGlobalOctadOutsidePoint : ZMod 2))

private theorem octadReflectionOdd :
    (golayGeneratorBit 11 generatedAxisGlobalOctadOutsidePoint : ZMod 2) = 1 := by
  exact (by decide +kernel : ∀ j : Fin 24, (golayGeneratorBit 11 j : ZMod 2) = 1) _

private theorem octadReflectionPhase :
    spinDot (fun k =>
      (golayGeneratorBit k generatedAxisGlobalOctadOutsidePoint : ZMod 2))
      (spinTranslation (griessShortQ (Sum.inr (Sum.inl (0, 0))))) = 0 := by
  have hz : golayOctadWord 0 generatedAxisGlobalOctadOutsidePoint = 0 := by
    by_contra hn
    exact (Classical.choose_spec generatedAxisGlobal_octad_outside_point_exists)
      ((golayOctadWord_ne_zero_iff _ _).mp hn)
  rw [griessOctad_translation]
  rw [show griessOctadOmegaCoefficient 0 = 0 by decide +kernel, zero_smul, add_zero]
  change (∑ k, golayLabelCoefficients (golayOctadLabel 0) k *
    (golayGeneratorBit k generatedAxisGlobalOctadOutsidePoint : ZMod 2)) = 0 at hz
  simpa only [spinDot, mul_comm] using hz

/-- The chosen genuine local reflection fixes the canonical signed octad axis. -/
theorem generatedAxisGlobalOctadReflection_fixes :
    rhoLocal (inclQ generatedAxisGlobalOctadReflection)
      (conwayShortAxis (Sum.inr (Sum.inl (0, 0))) 0) =
        conwayShortAxis (Sum.inr (Sum.inl (0, 0))) 0 := by
  have h := generatedAxis_localFiber_image (localFiberIncl generatedAxisGlobalOctadReflection)
    (Sum.inr (Sum.inl (0, 0))) 0
  have hp : griessShortPermutation
      (localFiberIncl generatedAxisGlobalOctadReflection).val.2
        (Sum.inr (Sum.inl (0, 0))) = Sum.inr (Sum.inl (0, 0)) := by
    change griessShortPermutation 1 _ = _
    rw [map_one]
    rfl
  rw [hp] at h
  change rhoLocal (inclQ generatedAxisGlobalOctadReflection) _ = _ at h
  have hc : localShortPhase (localFiberIncl generatedAxisGlobalOctadReflection)
      (Sum.inr (Sum.inl (0, 0))) = 0 := by
    rw [generatedAxisGlobalOctadReflection, cocodeQ_short_phase, octadReflectionPhase]
  simpa only [hc, zero_add] using h

/-- The canonical actual octad-family axis reached from the first local orbit. -/
noncomputable def generatedAxisGlobalOctadRoot : GriessSpace :=
  sExtra (conwayShortAxis (Sum.inr (Sum.inl (0, 0))) 0)

/-- The second triality image of this actual root has an explicit genuine local transporter. -/
theorem generatedAxisGlobalOctadRoot_triality_transport :
    rhoLocal (inclQ generatedAxisGlobalOctadReflection) generatedAxisGlobalOctadRoot =
      sExtra generatedAxisGlobalOctadRoot := by
  let a := rhoLocal (inclQ generatedAxisGlobalOctadReflection)
  have hc : a * sExtra * a⁻¹ = sExtra⁻¹ :=
    cocodeQ_conjugates_sExtra_inverse _ octadReflectionOdd
  have he : a * sExtra = sExtra⁻¹ * a := by
    calc
      a * sExtra = (a * sExtra * a⁻¹) * a := by group
      _ = sExtra⁻¹ * a := by rw [hc]
  have ht := LinearEquiv.congr_fun he
    (conwayShortAxis (Sum.inr (Sum.inl (0, 0))) 0)
  change rhoLocal (inclQ generatedAxisGlobalOctadReflection) generatedAxisGlobalOctadRoot =
    sExtra⁻¹ (rhoLocal (inclQ generatedAxisGlobalOctadReflection)
      (conwayShortAxis (Sum.inr (Sum.inl (0, 0))) 0)) at ht
  rw [generatedAxisGlobalOctadReflection_fixes] at ht
  rw [ht]
  apply sExtra.injective
  change sExtra (sExtra.symm _) = sExtra (sExtra (sExtra _))
  rw [LinearEquiv.apply_symm_apply, sExtra_triple]

/-- The inverse triality image of the actual octad root is an actual first-family axis. -/
theorem generatedAxisGlobalOctadRoot_inverse_triality :
    sExtra⁻¹ generatedAxisGlobalOctadRoot =
      conwayShortAxis (Sum.inr (Sum.inl (0, 0))) 0 :=
  sExtra.symm_apply_apply _

/-- The actual positive triality destination at the octad root returns to its own local class. -/
theorem generatedAxisGlobalOctadRoot_positive_class :
    Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra generatedAxisGlobalOctadRoot) =
      Quotient.mk (MulAction.orbitRel H GriessSpace) generatedAxisGlobalOctadRoot := by
  apply (generatedAxis_local_class_eq_iff _ _).mpr
  refine ⟨(inclQ generatedAxisGlobalOctadReflection)⁻¹, ?_⟩
  rw [← generatedAxisGlobalOctadRoot_triality_transport, rhoLocal.map_inv]
  exact LinearEquiv.symm_apply_apply _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
