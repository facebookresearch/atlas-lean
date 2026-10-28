/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsDefinitions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsQuadratic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCo1GeometryPointSeparation

/-! Intrinsic E8 singular coordinates identify the genuine incident frame classes
in the selected integral section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual binary embedding of the selected eight lattice roots. -/
def generatedAxisE8FrameRootEmbedding : (Fin 8 → ZMod 2) →ₗ[ZMod 2] LeechModTwo :=
  leechHyperbolicCoordinates.symm.toLinearMap.comp generatedFifthFrameBinaryMatrix.mulVecLin

/-- Eight selected root coordinates remain independent in the genuine lattice quotient. -/
theorem generatedAxisE8FrameRootEmbedding_injective :
    Function.Injective generatedAxisE8FrameRootEmbedding := by
  intro a b h
  have hm := congrArg (fun x => generatedFifthFrameLeftInverse *ᵥ
    leechHyperbolicCoordinates x) h
  change generatedFifthFrameLeftInverse *ᵥ
    (leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm
      (generatedFifthFrameBinaryMatrix *ᵥ a))) =
    generatedFifthFrameLeftInverse *ᵥ
    (leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm
      (generatedFifthFrameBinaryMatrix *ᵥ b))) at hm
  simpa only [LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec,
    generatedFifthFrame_left_inverse, Matrix.one_mulVec] using hm

/-- Insertion into the selected octad preserves the actual integer square sum. -/
theorem generatedAxisE8Frame_insert_square (v : Fin 8 → ℤ) :
    leechSquareSum (generatedFifthFrameInsert v) = ∑ i, v i ^ 2 := by
  simp [leechSquareSum, generatedFifthFrameInsert, Fin.sum_univ_succ]

/-- Integer linear combinations reduce to the binary embedding of their actual coefficients. -/
theorem generatedAxisE8FrameRootEmbedding_integer (a : Fin 8 → ℤ) :
    generatedAxisE8FrameRootEmbedding (fun i => (a i : ZMod 2)) =
      leechReduction (∑ j, a j • generatedFifthFrameRoot j) := by
  apply leechHyperbolicCoordinates.injective
  change leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm
    (generatedFifthFrameBinaryMatrix *ᵥ (fun i => (a i : ZMod 2)))) = _
  rw [LinearEquiv.apply_symm_apply, map_sum, map_sum]
  simp only [map_zsmul, generatedFifthFrameRoot_binary]
  change generatedFifthFrameBinaryMatrix *ᵥ (fun i => (a i : ZMod 2)) =
    ∑ j, a j • generatedFifthFrameBinaryMatrix.col j
  ext i
  simp [Matrix.mulVec, dotProduct, zsmul_eq_mul, mul_comm]

/-- A genuine norm-eight frame has unique nonzero singular intrinsic root coordinates. -/
theorem generatedAxisE8Frame_incident_singular (b : LeechModTwo)
    (hb : b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad))) :
    ∃ a : Fin 8 → ZMod 2, a ≠ 0 ∧ generatedAxisE8FrameQuadratic a = 0 ∧
      generatedAxisE8FrameRootEmbedding a = b := by
  obtain ⟨u, hu, hn, hub⟩ := hb
  obtain ⟨a, ha⟩ := generatedFifthFrame_integer_span u hu
  have hphysical : u.val = generatedFifthFrameInsert (generatedOctadIntegerRootMatrix *ᵥ a) := by
    rw [generatedFifthFrame_insert_root_sum, ha]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hnorm : (∑ i, (generatedOctadIntegerRootMatrix *ᵥ a) i ^ 2) = 64 := by
    rw [← generatedAxisE8Frame_insert_square, ← hphysical]
    exact hn
  have he : generatedAxisE8FrameRootEmbedding (fun i => (a i : ZMod 2)) = b := by
    rw [generatedAxisE8FrameRootEmbedding_integer, ← ha, hub]
  refine ⟨fun i => (a i : ZMod 2), ?_,
    generatedAxisE8FrameQuadratic_norm_eight a hnorm, he⟩
  intro hz
  have hb0 : b = 0 := by rw [← he, hz, map_zero]
  exact generatedCo1GeometryPoints_norm_eight_ne_zero u hn (hub.trans hb0)

/-- Every intrinsic nonzero singular coordinate is a genuine incident norm-eight class.
The converse uses the actual 135-class lattice count, not a chosen abstract frame model. -/
theorem generatedAxisE8Frame_singular_incident (a : Fin 8 → ZMod 2)
    (ha : a ≠ 0) (hq : generatedAxisE8FrameQuadratic a = 0) :
    generatedAxisE8FrameRootEmbedding a ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) := by
  classical
  let F := generatedAxisE8FrameClasses
    (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad))
  let Q := {v : Fin 8 → ZMod 2 // v ≠ 0 ∧ generatedAxisE8FrameQuadratic v = 0}
  have hcoords (b : F) := generatedAxisE8Frame_incident_singular b.val b.property
  let f : F → Q := fun b => ⟨(hcoords b).choose,
    (hcoords b).choose_spec.1, (hcoords b).choose_spec.2.1⟩
  have hbind (b : F) : generatedAxisE8FrameRootEmbedding (f b).val = b.val :=
    (hcoords b).choose_spec.2.2
  have hinj : Function.Injective f := by
    intro b c he
    apply Subtype.ext
    rw [← hbind b, ← hbind c, he]
  have hcard : Nat.card F = 135 := by
    have he := generatedAxisE8_image_frameClasses_card generatedFifthFlagOctad 1
    change Nat.card (generatedAxisE8FrameClasses (generatedAxisE8SectionEquiv 1
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)))) = 135 at he
    rwa [generatedAxisE8SectionEquiv_one] at he
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr
      ⟨hinj, hcard.trans generatedAxisE8FrameQuadratic_nonzero_card.symm⟩
  obtain ⟨b, hb⟩ := hbij.2 ⟨a, ha, hq⟩
  have he := hbind b
  rw [hb] at he
  exact he ▸ b.property

/-- Actual selected-section incidence is exactly nonzero singularity in the intrinsic E8 form. -/
theorem generatedAxisE8Frame_incident_iff (a : Fin 8 → ZMod 2) :
    generatedAxisE8FrameRootEmbedding a ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) ↔
    a ≠ 0 ∧ generatedAxisE8FrameQuadratic a = 0 := by
  constructor
  · intro h
    obtain ⟨v, hv, hq, he⟩ := generatedAxisE8Frame_incident_singular _ h
    have ha := generatedAxisE8FrameRootEmbedding_injective he
    exact ha ▸ ⟨hv, hq⟩
  · rintro ⟨ha, hq⟩
    exact generatedAxisE8Frame_singular_incident a ha hq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
