/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQDecidable

/-! The exact actual extraspecial correction and preferred-Q images of the zero bridge. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

/-- Decidable equality of genuine Q by both extension coordinates, for finite certificates. -/
local instance generatedFeasibleContainingZeroOutsideAnchorQDecidable : DecidableEq Q :=
  generatedSixthQDecidableEq

/-- The two literal genuine extraspecial corrections, including all code and cocode coordinates. -/
def generatedFeasibleContainingZeroOutsideAnchorCorrection (k : Fin 2) : Q :=
  ⟨ofAdd (Fin.append
    (golayLabelCoefficients (if k = 0 then 0 else 0x7a0))
    (golayLabelCoefficients 0x800)), 1⟩

/-- Each actual source step applies the original Xi spin lift and its exact Q correction. -/
def generatedFeasibleContainingZeroOutsideAnchorStep (k : Fin 2) : localFiberSubgroup :=
  localFiberIncl (generatedFeasibleContainingZeroOutsideAnchorCorrection k) * xiSpinLocalFiber

/-- Entire executable Q images retain the actual central coordinate of Xi and conjugation. -/
def generatedFeasibleContainingZeroOutsideAnchorQImage (k : Fin 2) (q : Q) : Q :=
  generatedFeasibleContainingZeroOutsideAnchorCorrection k *
    xiSpinGImage (xiSpinGammaImage q) *
      (generatedFeasibleContainingZeroOutsideAnchorCorrection k)⁻¹

/-- Bind the executable image to the whole actual fiber-product conjugation. -/
theorem generatedFeasibleContainingZeroOutsideAnchorQImage_actual (k : Fin 2) (q : Q) :
    spinConjugation (generatedFeasibleContainingZeroOutsideAnchorStep k).val.1 q =
      generatedFeasibleContainingZeroOutsideAnchorQImage k q := by
  change spinConjugation
    ((localFiberIncl (generatedFeasibleContainingZeroOutsideAnchorCorrection k)).val.1 *
      xiSpinHolomorph) q = _
  rw [map_mul]
  change spinConjugation (spinHolomorphIncl
    (generatedFeasibleContainingZeroOutsideAnchorCorrection k))
      (spinConjugation xiSpinHolomorph q) = _
  rw [spinConjugation_incl, xiSpinHolomorph_conjugation]
  rfl

/-- The exact preferred phases are read from the two actual unit coefficient signs. -/
def generatedFeasibleContainingZeroOutsideAnchorPhase (k : Fin 2) (n : Fin 120) : ZMod 2 :=
  if generatedFeasibleContainingZeroOutsideAnchorCoefficient (if k = 0 then 0 else 2) n =
    generatedFeasibleContainingZeroOutsideAnchorCoefficient (if k = 0 then 1 else 3) n then 0 else 1

/-- All eight bounded packet addresses cover the full 120 preferred roots. -/
def generatedFeasibleContainingZeroOutsideAnchorPacketIndex (k : Fin 8) (n : Fin 15) : Fin 120 :=
  ⟨15 * k.val + n.val, by omega⟩

/-- Both complete genuine corrected-Xi steps preserve the positive first pair1−2 at the Q level. -/
theorem generatedFeasibleContainingZeroOutsideAnchorFirst_Q : ∀ t : Fin 2,
    generatedFeasibleContainingZeroOutsideAnchorQImage t
      (generatedFeasibleContainingZeroOutsideAnchorQ (Sum.inl (0, 23))) =
        generatedFeasibleContainingZeroOutsideAnchorQ (Sum.inl (0, 23)) := by decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
