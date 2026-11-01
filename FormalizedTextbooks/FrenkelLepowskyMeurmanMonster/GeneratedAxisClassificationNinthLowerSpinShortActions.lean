/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinCompactFiberActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortLookup

/-! Complete actual preferred-Q transport uses only the already verified 24 full generator images.
The actual Ninth short coefficient cache binding is an explicit separate prerequisite. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every source Q coordinate image retains the entire genuine Pauli correction. -/
def generatedNinthLowerSpinShortQImages (i : Fin 11) (j : Fin 24) : Q :=
  generatedNinthLowerSpinCorrection i * generatedNinthLowerSpinQImage i j *
    (generatedNinthLowerSpinCorrection i)⁻¹

/-- A full-Q evaluator from 24 genuine source generator images, without expanding a long word. -/
def generatedNinthLowerSpinShortQFast (i : Fin 11) (q : Q) : Q :=
  monsterNortonCoordinateEvaluation (generatedNinthLowerSpinShortQImages i) q

/-- The finite evaluator is the actual compact source conjugation on every Q element. -/
theorem generatedNinth_lower_spin_short_q_fast_actual (i : Fin 11) (q : Q) :
    spinConjugation (generatedNinthLowerSpinCompact i) q =
      generatedNinthLowerSpinShortQFast i q := by
  apply monsterNortonCoordinateEvaluation_eq
  exact generatedNinth_lower_spin_compact_generator i

/-- The compact original mask is the whole actual preferred lift of every dictionary coordinate. -/
theorem generatedNinth_lower_spin_short_q_mask_actual (r : GriessShortIndex) :
    generatedAxisGlobalQMask (generatedAxisGlobalShortMask r) = monsterNortonShortQ r := by
  rw [← generatedAxisGlobalShortMask_Q_actual,
    generatedAxisGlobalShortQFinite_actual, monsterNortonShortQ_eq]

/-- All finite source transport obligations: complete preferred-Q image and signed coefficient. -/
def generatedNinthLowerSpinShortCondition (i : Fin 11) (a : Fin 98280) : Prop :=
  let r := generatedNinthLowerSpinShortIndex a
  generatedNinthLowerSpinShortQFast i
      (generatedAxisGlobalQMask (generatedAxisGlobalShortMask r)) =
    qCentral (generatedNinthLowerSpinShortPhase i r) *
      generatedAxisGlobalQMask
        (generatedAxisGlobalShortMask (generatedNinthLowerSpinShortDestination i r)) ∧
    nortonUIntegerSign (generatedNinthLowerSpinShortPhase i r) *
      generatedNinthLowerSpinShortInputInteger r =
        generatedNinthLowerSpinShortInputInteger (generatedNinthLowerSpinShortDestination i r)

/-- Every complete finite preferred lift certificate is an actual compact source short image. -/
theorem generatedNinth_lower_spin_short_image (i : Fin 11)
    (h : ∀ a, generatedNinthLowerSpinShortCondition i a) (r : GriessShortIndex) :
    spinConjugation (generatedNinthLowerSpinCompactFiber i).val.1 (monsterNortonShortQ r) =
      qCentral (generatedNinthLowerSpinShortPhase i r) *
        monsterNortonShortQ (generatedNinthLowerSpinShortDestination i r) := by
  have hr := h (generatedNinthLowerSpinShortAddress r)
  simp only [generatedNinthLowerSpinShortCondition,
    generatedNinth_lower_spin_short_index_address] at hr
  change spinConjugation (generatedNinthLowerSpinCompact i) (monsterNortonShortQ r) = _
  rw [generatedNinth_lower_spin_short_q_fast_actual,
    ← generatedNinth_lower_spin_short_q_mask_actual r,
    ← generatedNinth_lower_spin_short_q_mask_actual (generatedNinthLowerSpinShortDestination i r)]
  exact hr.1

/-- The whole preferred-Q image fixes its exact genuine spatial short permutation. -/
theorem generatedNinth_lower_spin_short_destination_actual (i : Fin 11)
    (h : ∀ a, generatedNinthLowerSpinShortCondition i a) (r : GriessShortIndex) :
    griessShortPermutation (generatedNinthLowerSpinCompactFiber i).val.2 r =
      generatedNinthLowerSpinShortDestination i r := by
  have hq := generatedNinth_lower_spin_short_image i h r
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq] at hq
  apply griessShortClassEquiv.injective
  apply Subtype.ext
  apply leechHyperbolicCoordinates.injective
  have hb := congrArg (fun q : Q => toAdd q.base) hq
  rw [qCentral_mul_base, griessShortQ_image_base] at hb
  exact hb

/-- Binding every actual short coordinate to the full integer cache yields genuine local
fixation. -/
theorem generatedNinth_lower_spin_short_fix_of_source_cache (i : Fin 11)
    (h : ∀ a, generatedNinthLowerSpinShortCondition i a) (X : GriessShortIndex → ℝ)
    (hinput : ∀ r, 256 * X r = (generatedNinthLowerSpinShortInputInteger r : ℝ)) :
    localShortRepresentation (generatedNinthLowerSpinCompactFiber i) X = X := by
  funext s
  obtain ⟨r, hr⟩ := (griessShortPermutation
    (generatedNinthLowerSpinCompactFiber i).val.2).surjective s
  have hd : generatedNinthLowerSpinShortDestination i r = s :=
    (generatedNinth_lower_spin_short_destination_actual i h r).symm.trans hr
  have ho := monsterNortonShortOperator_of_Q_image
    (generatedNinthLowerSpinCompactFiber i) r (generatedNinthLowerSpinShortDestination i r)
      (generatedNinthLowerSpinShortPhase i r) (generatedNinth_lower_spin_short_image i h r) X
  rw [hd] at ho
  change localShortOperator (generatedNinthLowerSpinCompactFiber i) X s = X s
  rw [ho]
  have hc := (h (generatedNinthLowerSpinShortAddress r))
  simp only [generatedNinthLowerSpinShortCondition,
    generatedNinth_lower_spin_short_index_address] at hc
  have hz := congrArg (fun z : ℤ => (z : ℝ)) hc.2
  simp only [Int.cast_mul, nortonUIntegerSign_real] at hz
  rw [← hinput r, ← hinput (generatedNinthLowerSpinShortDestination i r), hd] at hz
  nlinarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
