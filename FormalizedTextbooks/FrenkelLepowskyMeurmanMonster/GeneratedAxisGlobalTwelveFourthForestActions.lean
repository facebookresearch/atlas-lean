/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthPermutations
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82Leech
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXiBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSignLifts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinary

/-! Five genuine spatial generators of the actual Fourth flag stabilizer and their actual
binary actions: the four monomial flag words and the normalized flag lift
(source sign y82, flag correction, Xi, source sign y82). Each has an actual local lift
fixing the complete Fourth axis, chosen from the proved projection memberships. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Four monomial flag words, then the normalized flag lift, as actual Leech isometries. -/
def generatedAxisGlobalTwelveFourthSpatial (k : Fin 5) : leechIsomSubgroup :=
  if k.val < 4 then golayPermutationIsometry (generatedAxisGlobalTwelveFourthPermutation k)
  else monsterSourceY82Isometry * generatedFourthFlagCorrectionLeech * co1XiIsometry *
    monsterSourceY82Isometry

/-- Their matrices in the genuine hyperbolic coordinates of the extraspecial quotient. -/
def generatedAxisGlobalTwelveFourthBinaryMatrix (k : Fin 5) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  if k.val < 4 then generatedAxisGlobalTwelveFourthPermutationBinary k
  else monsterSourceY82Binary * generatedAxisGlobalTwelveFourthPermutationBinary 4 *
    (leechHyperbolicInverse * co1XiBasisMatrix.map (Int.castRingHom (ZMod 2)) *
      leechHyperbolicMatrix) * monsterSourceY82Binary

/-- The fifth permutation is the literal flag correction. -/
theorem generatedAxisGlobalTwelveFourthPermutation_four :
    golayPermutationIsometry (generatedAxisGlobalTwelveFourthPermutation 4) =
      generatedFourthFlagCorrectionLeech := rfl

/-- Every matrix is the actual Conway quotient action of its spatial generator. -/
theorem generatedAxisGlobalTwelveFourthSpatial_binary (k : Fin 5) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalTwelveFourthSpatial k)) v =
      generatedAxisGlobalTwelveFourthBinaryMatrix k *ᵥ v := by
  by_cases h : k.val < 4
  · simp only [generatedAxisGlobalTwelveFourthSpatial,
      generatedAxisGlobalTwelveFourthBinaryMatrix, h, ↓reduceIte]
    exact generatedAxisGlobalTwelveFourthPermutation_binary k v
  · simp only [generatedAxisGlobalTwelveFourthSpatial,
      generatedAxisGlobalTwelveFourthBinaryMatrix, h, ↓reduceIte]
    change leechBinaryAction _ v = _
    have hc := generatedAxisGlobalTwelveFourthPermutation_binary 4
    rw [generatedAxisGlobalTwelveFourthPermutation_four] at hc
    change ∀ w, leechBinaryAction generatedFourthFlagCorrectionLeech w = _ at hc
    rw [map_mul, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, monsterSourceY82Isometry_binary, co1Xi_binaryAction, hc,
      monsterSourceY82Isometry_binary, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]

/-- Every spatial generator has an actual local lift fixing the complete Fourth axis. -/
theorem generatedAxisGlobalTwelveFourthSpatial_mem (k : Fin 5) :
    generatedAxisGlobalTwelveFourthSpatial k ∈ generatedFourthPhysicalAxisProjection := by
  by_cases h : k.val < 4
  · have hm := generatedFourth_monomial_physical_projection_mem ⟨k.val, h⟩
    rw [generatedFourth_monomial_spatial] at hm
    simpa only [generatedAxisGlobalTwelveFourthSpatial,
      generatedAxisGlobalTwelveFourthPermutation, h, ↓reduceIte, ↓reduceDIte] using hm
  · simp only [generatedAxisGlobalTwelveFourthSpatial, h, ↓reduceIte]
    exact generatedFourth_monomial_normalized_projection_mem

/-- Each spatial generator has a genuine full-axis-fixing local lift. -/
theorem generatedAxisGlobalTwelveFourth_generator_lift_exists (k : Fin 5) :
    ∃ h : generatedFourthLocalAxisStabilizer,
      projH h.val = QuotientGroup.mk' signsSubgroup (generatedAxisGlobalTwelveFourthSpatial k) := by
  obtain ⟨h, hh, hp⟩ := generatedAxisGlobalTwelveFourthSpatial_mem k
  exact ⟨⟨h, hh⟩, hp⟩

/-- Actual full-axis-fixing lifts of the five spatial generators. -/
def generatedAxisGlobalTwelveFourthGenerator (k : Fin 5) : generatedFourthLocalAxisStabilizer :=
  Classical.choose (generatedAxisGlobalTwelveFourth_generator_lift_exists k)

/-- The chosen lifts have exactly the original spatial projection. -/
theorem generatedAxisGlobalTwelveFourthGenerator_projection (k : Fin 5) :
    projH (generatedAxisGlobalTwelveFourthGenerator k).val =
      QuotientGroup.mk' signsSubgroup (generatedAxisGlobalTwelveFourthSpatial k) :=
  Classical.choose_spec (generatedAxisGlobalTwelveFourth_generator_lift_exists k)

/-- Every chosen generator fixes the complete genuine Fourth axis. -/
theorem generatedAxisGlobalTwelveFourthGenerator_fixed (k : Fin 5) :
    rhoLocal (generatedAxisGlobalTwelveFourthGenerator k).val generatedFourthAxis =
      generatedFourthAxis :=
  (generatedAxisGlobalTwelveFourthGenerator k).property

/-- Every generator acts on the genuine binary Ω orbit by its checked actual matrix. -/
theorem generatedAxisGlobalTwelveFourthGenerator_binary (k : Fin 5)
    (x : generatedAxisGlobalBinaryOrbit) :
    (generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveFourthGenerator k).val x).val =
      generatedAxisGlobalTwelveFourthBinaryMatrix k *ᵥ x.val := by
  change co1BinaryAction (projH (generatedAxisGlobalTwelveFourthGenerator k).val) x.val = _
  rw [generatedAxisGlobalTwelveFourthGenerator_projection,
    generatedAxisGlobalTwelveFourthSpatial_binary]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
