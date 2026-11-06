/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortPhysical

/-! Finite physical and Q formulas bound to the actual pair and fifth-octad catalogues. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Ordered physical pairs and the verified56 actual outgoing octad families. -/
abbrev generatedFifthXiShortCachedLabel :=
  (Fin 2 × {p : Fin 24 × Fin 24 // p.1 < p.2}) ⊕ (Fin 56 × Fin 64)

/-- Bind the finite cache directly to the genuine coordinate catalogue. -/
noncomputable def generatedFifthXiShortCachedEven :
    generatedFifthXiShortCachedLabel → generatedFifthXiEvenShortLabel
  | Sum.inl (s, p) => Sum.inl (s, griessPairIndex p.val.1 p.val.2 (ne_of_lt p.property))
  | Sum.inr (j, e) => Sum.inr (generatedFifthEvenRootOctad j, e)

/-- The actual octad sign mask using the already verified increasing coordinates. -/
def generatedFifthXiShortCachedSignMask (j : Fin 56) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedFifthEvenRootCoordinates j k).val else 0) ||| m) 0

/-- This finite sign mask equals the actual signed-octad mask. -/
theorem generatedFifthXiShortCachedSignMask_actual (j : Fin 56) (e : Fin 64) :
    generatedFifthXiShortCachedSignMask j e =
      griessOctadSignMask (generatedFifthEvenRootOctad j) e := by
  simp only [generatedFifthXiShortCachedSignMask, griessOctadSignMask,
    generatedFifth_even_coordinates_certificate]

/-- Exact finite physical coordinates of a cached genuine short vector. -/
def generatedFifthXiShortCachedIntegral : generatedFifthXiShortCachedLabel → Fin 24 → ℤ
  | Sum.inl (s, p) => fun i => 4 * (if i = p.val.1 then 1 else 0) +
      (if s = 0 then -4 else 4) * (if i = p.val.2 then 1 else 0)
  | Sum.inr (j, e) => fun i =>
      if (golayEncodedMask (generatedFifthEvenRootCode j).val).testBit i.val then
        if (generatedFifthXiShortCachedSignMask j e).testBit i.val then -2 else 2
      else 0

/-- The finite physical coordinates are the actual preferred-short coordinates. -/
theorem generatedFifthXiShortCachedIntegral_actual (r : generatedFifthXiShortCachedLabel) :
    generatedFifthXiShortCachedIntegral r =
      griessShortIntegral (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r)) := by
  rcases r with ⟨s, p⟩ | ⟨j, e⟩
  · simp only [generatedFifthXiShortCachedIntegral, generatedFifthXiShortCachedEven,
      generatedFifthXiEvenShortIndex, griessShortIntegral, griessPairIndex_coordinates,
      p.property, ite_true]
  · simp only [generatedFifthXiShortCachedIntegral, generatedFifthXiShortCachedEven,
      generatedFifthXiEvenShortIndex, griessShortIntegral, generatedFifthEvenRootOctad_label,
      generatedFifthXiShortCachedSignMask_actual]

/-- Actual preferred Q lifts evaluated through the physical-pair and octad-coordinate cache. -/
def generatedFifthXiShortCachedQ : generatedFifthXiShortCachedLabel → Q
  | Sum.inl (s, p) => generatedAxisFourthQFromSpin
      (if s = 0 then 0 else Pi.single 11 1)
      (fun k => (golayGeneratorBit k p.val.1 : ZMod 2) +
        (golayGeneratorBit k p.val.2 : ZMod 2)) 0
  | Sum.inr (j, e) => generatedAxisFourthQFromSpin
      (golayLabelCoefficients (generatedFifthEvenRootCode j) +
        griessOctadOmegaCoefficient e • Pi.single 11 1)
      (sourceWordTheta (generatedFifthEvenRootCode j) +
        golaySyndrome (integerParity (fun i =>
          if (generatedFifthXiShortCachedSignMask j e).testBit i.val then 1 else 0))) 0

/-- The cached preferred Q lift is exactly the actual lift, including its central coefficient. -/
theorem generatedFifthXiShortCachedQ_actual (r : generatedFifthXiShortCachedLabel) :
    generatedFifthXiShortCachedQ r =
      generatedFifthXiEvenShortQ (generatedFifthXiShortCachedEven r) := by
  rcases r with ⟨s, p⟩ | ⟨j, e⟩
  · have hp : (fun k => (golayGeneratorBit k p.val.1 : ZMod 2) +
        (golayGeneratorBit k p.val.2 : ZMod 2)) =
        griessPairSyndrome (griessPairIndex p.val.1 p.val.2 (ne_of_lt p.property)) := by
      ext k
      simp only [griessPairSyndrome, griessPairIndex_coordinates, p.property, ite_true]
    change generatedAxisFourthQFromSpin _ _ _ = generatedAxisFourthQFromSpin _ _ _
    rw [hp]
  · have he : (fun i => if (generatedFifthXiShortCachedSignMask j e).testBit i.val then
        (1 : ℤ) else 0) = griessOctadNegativeInteger (generatedFifthEvenRootOctad j) e := by
      ext i
      simp only [griessOctadNegativeInteger, generatedFifthXiShortCachedSignMask_actual]
    change generatedAxisFourthQFromSpin _ _ _ = generatedAxisFourthQFromSpin _ _ _
    rw [he, generatedFifthEvenRootOctad_label]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
