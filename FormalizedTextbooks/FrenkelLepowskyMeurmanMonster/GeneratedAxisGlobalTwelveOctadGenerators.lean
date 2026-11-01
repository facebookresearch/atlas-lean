/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadPermutations
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadMaskAlgebra
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthMaskColumns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadProjectedLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOctadStabilizerProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinary

/-! Sixteen genuine elements of the actual octad-axis stabilizer for the octad binary forest:
the twelve published Golay signs, three Golay-automorphism involutions of the octad-three block,
and the original Xi. Each is a chosen lift fixing the entire actual octad-image axis, and its
binary action is given by exact compact column masks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Sixteen actual spatial generators: twelve signs, three block involutions and Xi. -/
def generatedAxisGlobalTwelveOctadSpatial (k : Fin 16) : leechIsomSubgroup :=
  if h : k.val < 12 then generatedAxisGlobalFifthSpatial ⟨k.val, by omega⟩
  else if h' : k.val < 15 then
    golayPermutationIsometry (generatedAxisGlobalTwelveOctadPermutation ⟨k.val - 12, by omega⟩)
  else generatedAxisGlobalFifthSpatial 18

/-- Their binary column masks in the genuine hyperbolic coordinates. -/
def generatedAxisGlobalTwelveOctadColumns (k : Fin 16) : Fin 24 → ℕ :=
  if h : k.val < 12 then generatedAxisGlobalFifthBinaryColumns ⟨k.val, by omega⟩
  else if h' : k.val < 15 then generatedAxisGlobalTwelveOctadPermColumns ⟨k.val - 12, by omega⟩
  else generatedAxisGlobalFifthBinaryColumns 18

/-- The corresponding direct row lists. -/
def generatedAxisGlobalTwelveOctadRows (k : Fin 16) : List (ℕ × ℕ) :=
  List.ofFn (fun j : Fin 24 => (j.val, generatedAxisGlobalTwelveOctadColumns k j))

/-- Every spatial generator acts on Λ/2Λ by its compact column matrix. -/
theorem generatedAxisGlobalTwelveOctadSpatial_binary (k : Fin 16) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalTwelveOctadSpatial k)) v =
      generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalTwelveOctadColumns k) *ᵥ v := by
  by_cases h : k.val < 12
  · simp only [generatedAxisGlobalTwelveOctadSpatial, generatedAxisGlobalTwelveOctadColumns, h,
      ↓reduceDIte]
    rw [generatedAxisGlobalFifthSpatial_binary, generatedAxisGlobalFifthBinaryColumns_certificate]
  · by_cases h' : k.val < 15
    · simp only [generatedAxisGlobalTwelveOctadSpatial, generatedAxisGlobalTwelveOctadColumns, h,
        h', ↓reduceDIte]
      exact generatedAxisGlobalTwelveOctadPerm_binary _ v
    · simp only [generatedAxisGlobalTwelveOctadSpatial, generatedAxisGlobalTwelveOctadColumns, h,
        h', ↓reduceDIte]
      rw [generatedAxisGlobalFifthSpatial_binary,
        generatedAxisGlobalFifthBinaryColumns_certificate]

/-- Every spatial generator preserves the complete integral octad-three coordinate section. -/
theorem generatedAxisGlobalTwelveOctadSpatial_preserves (k : Fin 16) :
    generatedOctadPreserves (golayOctadWord generatedOctadBasisOctad)
      (generatedAxisGlobalTwelveOctadSpatial k) := by
  by_cases h : k.val < 12
  · simp only [generatedAxisGlobalTwelveOctadSpatial, generatedAxisGlobalFifthSpatial, h,
      ↓reduceDIte]
    exact generatedAxisE8Orthogonal_sign_preserves _
  · by_cases h' : k.val < 15
    · simp only [generatedAxisGlobalTwelveOctadSpatial, h, h', ↓reduceDIte]
      exact generatedAxisGlobalTwelveOctadPermutation_preserves _
    · have h0 : ¬(18 : Fin 19).val < 12 := by decide
      have h1 : ¬(18 : Fin 19).val < 18 := by decide
      simp only [generatedAxisGlobalTwelveOctadSpatial, generatedAxisGlobalFifthSpatial, h, h',
        h0, h1, ↓reduceDIte]
      exact generatedAxisE8Orthogonal_xi_preserves

/-- Each spatial generator has a genuine local lift fixing the entire actual octad axis. -/
theorem generatedAxisGlobalTwelveOctad_lift_exists (k : Fin 16) :
    ∃ f : localFiberSubgroup, f.val.2 = generatedAxisGlobalTwelveOctadSpatial k ∧
      rhoLocal (localFiberIntoH f) (generatedOctadLocalAxis 0 0) = generatedOctadLocalAxis 0 0 :=
  generatedOctad_projected_stabilizer_lift 0 0 _
    (generatedAxisE8_preserving_image _ _ (generatedAxisGlobalTwelveOctadSpatial_preserves k))

/-- The chosen genuine axis-fixing lifts. -/
def generatedAxisGlobalTwelveOctadGeneratorFiber (k : Fin 16) : localFiberSubgroup :=
  Classical.choose (generatedAxisGlobalTwelveOctad_lift_exists k)

/-- The sixteen actual stabilizer generators of the listed Octad representative. -/
def generatedAxisGlobalTwelveOctadGenerator (k : Fin 16) : generatedOctadLocalAxisStabilizer 0 0 :=
  ⟨localFiberIntoH (generatedAxisGlobalTwelveOctadGeneratorFiber k),
    (Classical.choose_spec (generatedAxisGlobalTwelveOctad_lift_exists k)).2⟩

/-- Every generator has exactly the stated spatial Conway projection. -/
theorem generatedAxisGlobalTwelveOctadGenerator_projection (k : Fin 16) :
    projH (generatedAxisGlobalTwelveOctadGenerator k).val =
      QuotientGroup.mk' signsSubgroup (generatedAxisGlobalTwelveOctadSpatial k) := by
  change QuotientGroup.mk' signsSubgroup (generatedAxisGlobalTwelveOctadGeneratorFiber k).val.2 = _
  exact congrArg (QuotientGroup.mk' signsSubgroup)
    (Classical.choose_spec (generatedAxisGlobalTwelveOctad_lift_exists k)).1

/-- The bounded integer mask of a genuine binary Ω-orbit point. -/
def generatedAxisGlobalTwelveOctadMask (x : generatedAxisGlobalBinaryOrbit) : ℕ :=
  ((generatedAxisGlobalMaskFiniteEquiv 24).symm x.val).val

/-- The mask has only the 24 genuine coordinates. -/
theorem generatedAxisGlobalTwelveOctadMask_lt (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalTwelveOctadMask x < 2 ^ 24 :=
  ((generatedAxisGlobalMaskFiniteEquiv 24).symm x.val).isLt

/-- The mask decodes to the actual binary vector. -/
theorem generatedAxisGlobalTwelveOctadMask_decode (x : generatedAxisGlobalBinaryOrbit) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveOctadMask x) = x.val :=
  (generatedAxisGlobalMaskFiniteEquiv 24).apply_symm_apply x.val

/-- Two orbit points with equal masks are equal. -/
theorem generatedAxisGlobalTwelveOctadMask_injective {x y : generatedAxisGlobalBinaryOrbit}
    (h : generatedAxisGlobalTwelveOctadMask x = generatedAxisGlobalTwelveOctadMask y) : x = y := by
  apply Subtype.ext
  rw [← generatedAxisGlobalTwelveOctadMask_decode x, ← generatedAxisGlobalTwelveOctadMask_decode y,
    h]

/-- A point whose actual vector decodes from a bounded mask has exactly that mask. -/
theorem generatedAxisGlobalTwelveOctadMask_of_decode (x : generatedAxisGlobalBinaryOrbit) (b : ℕ)
    (hb : b < 2 ^ 24) (h : x.val = monsterCo1GeometryBinaryMaskDecode (n := 24) b) :
    generatedAxisGlobalTwelveOctadMask x = b := by
  apply generatedAxisGlobalTwelveOctadMask_eq_of_decode (generatedAxisGlobalTwelveOctadMask_lt x) hb
  rw [generatedAxisGlobalTwelveOctadMask_decode, h]

/-- All generator columns stay in the 24 genuine coordinates. -/
theorem generatedAxisGlobalTwelveOctadColumns_lt : ∀ k : Fin 16, ∀ j : Fin 24,
    generatedAxisGlobalTwelveOctadColumns k j < 2 ^ 24 := by
  decide +kernel

/-- Each actual generator acts on masks by its compact row list. -/
theorem generatedAxisGlobalTwelveOctadGenerator_mask (k : Fin 16)
    (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalTwelveOctadMask
        (generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveOctadGenerator k).val x) =
      generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveOctadRows k)
        (generatedAxisGlobalTwelveOctadMask x) := by
  apply generatedAxisGlobalTwelveOctadMask_of_decode
  · exact generatedAxisGlobalTwelveOctadRows_ofFn_lt _
      (generatedAxisGlobalTwelveOctadColumns_lt k) _
  · rw [generatedAxisGlobalTwelveOctadRows, generatedAxisGlobalTwelveOctadRows_ofFn_decode,
      generatedAxisGlobalTwelveOctadMask_decode]
    change co1BinaryAction (projH (generatedAxisGlobalTwelveOctadGenerator k).val) x.val = _
    rw [generatedAxisGlobalTwelveOctadGenerator_projection, generatedAxisGlobalTwelveOctadSpatial_binary]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
