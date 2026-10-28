/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source odd cocode reflections in the actual local coordinate group.
The reflection acts by pure Schrödinger modulation, with its short-vector
signs obtained from the genuine Q conjugation action.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddSpinDictionary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairQProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadXYZSpin

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- Actual extraspecial element attached to a cocode syndrome. -/
def cocodeQ (h : Fin 12 → ZMod 2) : Q := ⟨ofAdd (binaryCocodeEmbedding h), 1⟩

@[simp] theorem cocodeQ_translation (h : Fin 12 → ZMod 2) :
    spinTranslation (cocodeQ h) = 0 := by
  funext k
  exact binaryCocodeEmbedding_left h k

@[simp] theorem cocodeQ_modulation (h : Fin 12 → ZMod 2) :
    spinModulation (cocodeQ h) = h := by
  funext k
  exact binaryCocodeEmbedding_right h k

@[simp] theorem cocodeQ_coeff (h : Fin 12 → ZMod 2) : toAdd (cocodeQ h).coeff = 0 := rfl

/-- The actual source cocode reflection fixes translations and multiplies spin coordinates. -/
theorem cocodeQ_spin (h : Fin 12 → ZMod 2) (x : SpinSpace) (t : SpinIndex) :
    spinRepresentation (cocodeQ h) x t = qSign (spinDot h t) * x t := by
  change qSign (spinPhase (cocodeQ h) t) * x (t + spinTranslation (cocodeQ h)) = _
  rw [spinPhase, cocodeQ_coeff, cocodeQ_modulation, cocodeQ_translation]
  simp

/-- The cocycle is the translation-modulation dot product, in its actual argument order. -/
theorem qBeta_spin_coordinates (g k : Q) :
    qBeta (toAdd g.base) (toAdd k.base) =
      spinDot (spinTranslation g) (spinModulation k) := rfl

/-- Symmetry of the binary spin dot product. -/
theorem spinDot_comm (a b : SpinIndex) : spinDot a b = spinDot b a := by
  unfold spinDot
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Pure cocode conjugation gives the genuine short-vector phase. -/
theorem cocodeQ_short_phase (h : Fin 12 → ZMod 2) (r : GriessShortIndex) :
    localShortPhase (localFiberIncl (cocodeQ h)) r =
      spinDot h (spinTranslation (griessShortQ r)) := by
  change toAdd (spinConjugation (spinHolomorphIncl (cocodeQ h)) (griessShortQ r)).coeff = _
  rw [spinConjugation_incl, q_conjugation_central_phase, qCentral_mul_coeff,
    griessShortQ_coeff, add_zero]
  rw [qBeta_spin_coordinates, qBeta_spin_coordinates,
    cocodeQ_translation, cocodeQ_modulation]
  simp only [spinDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The local Q action gives the genuine signs on the physical short block. -/
theorem cocodeQ_short (h : Fin 12 → ZMod 2) (x : GriessShortIndex → ℝ)
    (r : GriessShortIndex) :
    localShortRepresentation (localFiberIncl (cocodeQ h)) x r =
      qSign (spinDot h (spinTranslation (griessShortQ r))) * x r := by
  have hp : griessShortPermutation (localFiberIncl (cocodeQ h)).val.2 r = r := by
    change griessShortPermutation 1 r = r
    rw [map_one]; rfl
  have he := localShortOperator_image (localFiberIncl (cocodeQ h)) x r
  rw [hp, cocodeQ_short_phase] at he
  exact he

/-- The genuine local Q tensor representation acts on each spin column. -/
theorem localTensorRepresentation_q (q : Q) (x : SpinIndex → Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (localFiberIncl q) x t i =
      spinRepresentation q (fun u => x u i) t := by
  obtain ⟨v, rfl⟩ := conwayTensorCoordinates.surjective x
  rw [localTensorRepresentation_coordinates]
  induction v using TensorProduct.inductionOn with
  | tmul a b =>
    change conwayTensorCoordinates (TensorProduct.congr _ _ (a ⊗ₜ[ℝ] b)) t i = _
    rw [TensorProduct.congr_tmul, conwayTensorCoordinates_tmul]
    simp only [conwayTensorCoordinates_tmul]
    change spinRepresentation q a t * b i =
      qSign (spinPhase q t) * (a (t + spinTranslation q) * b i)
    change (qSign (spinPhase q t) * a (t + spinTranslation q)) * b i = _
    ring
  | add a b ha hb =>
    simp only [map_add, Pi.add_apply, ha, hb]
    change _ = qSign (spinPhase q t) * (_ + _)
    rw [mul_add]
    rfl

/-- Pure cocode modulation on the tensor columns of the fixed physical dictionary. -/
theorem cocodeQ_tensor (h : Fin 12 → ZMod 2) (x : SpinIndex → Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (localFiberIncl (cocodeQ h)) x t i =
      qSign (spinDot h t) * x t i := by
  rw [localTensorRepresentation_q, cocodeQ_spin]

/-- The odd source singleton cocode {0}. -/
def singletonCocodeQ : Q := cocodeQ (fun k => (golayGeneratorBit k 0 : ZMod 2))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
