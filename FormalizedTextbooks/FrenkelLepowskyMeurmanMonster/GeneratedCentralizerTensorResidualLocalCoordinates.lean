/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine local Q image in the actual centralizer coordinate dictionaries. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensorResidualShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerLocalLift

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The actual local tensor action agrees with the original fiber tensor representation. -/
theorem generatedLocal_tensor_action (f : localFiberSubgroup) (T : SpinIndex → Fin 24 → ℝ) :
    generatedCentralizerTensorAction (generatedLocalIntoCentralizer (QuotientGroup.mk f)) T =
      localTensorRepresentation f T := by
  change (griessConwayEncode
    (localGriessRepresentation f (griessConwayDecode (0, (0, T))))).2.2 = _
  rw [localGriessRepresentation_encode,
    griessConwayEncode_decode _ (by intro i j; rfl), localConwayRawRepresentation_apply]

/-- Every actual Q image fixes the genuine pure matrix vectors pointwise. -/
theorem generatedLocalQ_matrix_fixed (q : Q) (A : Sym24) :
    (generatedLocalIntoCentralizer (inclQ q)).val.val (generatedCentralPlusEmbed A 0).val =
      (generatedCentralPlusEmbed A 0).val := by
  rw [generatedCentralizerMatrixAction_embed]
  have h := generatedLocal_matrix_action (localFiberIncl q) A
  change (generatedCentralizerMatrixAction (generatedLocalIntoCentralizer (inclQ q)) A).val =
    conwayMatrixAction 1 A.val at h
  rw [map_one] at h
  have he : generatedCentralizerMatrixAction (generatedLocalIntoCentralizer (inclQ q)) A = A :=
    Subtype.ext h
  rw [he]

/-- The actual local Q short action is diagonal with its constructed conjugation phase. -/
theorem generatedLocalQ_short_apply (q : Q) (X : GriessShortIndex → ℝ) (r : GriessShortIndex) :
    generatedCentralizerShortAction (generatedLocalIntoCentralizer (inclQ q)) X r =
      qSign (localShortPhase (localFiberIncl q) r) * X r := by
  have h := localShortOperator_image (localFiberIncl q) X r
  change localShortOperator (localFiberIncl q) X (griessShortPermutation 1 r) = _ at h
  rw [map_one, Equiv.Perm.one_apply] at h
  have hs := generatedLocal_short_action (localFiberIncl q) X
  change generatedCentralizerShortAction (generatedLocalIntoCentralizer (inclQ q)) X =
    localShortRepresentation (localFiberIncl q) X at hs
  rw [hs]
  exact h

/-- Each actual local Q image has the diagonal short signs used by residual recognition. -/
theorem generatedLocalQ_short_unit (q : Q) (r : GriessShortIndex) :
    generatedCentralizerShortAction (generatedLocalIntoCentralizer (inclQ q))
      (shortCoordinateUnit r) =
      qSign (localShortPhase (localFiberIncl q) r) • shortCoordinateUnit r := by
  funext s
  rw [generatedLocalQ_short_apply]
  by_cases h : s = r
  · subst s
    rfl
  · simp [shortCoordinateUnit, h]

/-- The original fiber inclusion applies its actual spin representation in each tensor column. -/
theorem localFiberQ_tensor_columns (q : Q) (T : SpinIndex → Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (localFiberIncl q) T t i =
      spinRepresentation q (fun u => T u i) t := by
  obtain ⟨z, rfl⟩ := conwayTensorCoordinates.surjective T
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [localTensorRepresentation_coordinates]
    change conwayTensorCoordinates ((spinRepresentation q a) ⊗ₜ[ℝ] b) t i = _
    simp only [conwayTensorCoordinates_tmul]
    change spinOperator q a t * b i = spinOperator q (fun u => a u * b i) t
    rw [spinOperator_mul_fun]
    exact mul_comm _ _
  | add a b ha hb =>
    simp only [map_add, Pi.add_apply]
    rw [show (fun u => conwayTensorCoordinates a u i + conwayTensorCoordinates b u i) =
      (fun u => conwayTensorCoordinates a u i) + (fun u => conwayTensorCoordinates b u i) from rfl,
      map_add, Pi.add_apply, ha, hb]

/-- The actual local Q image has its represented spin factor on all tensor columns. -/
theorem generatedLocalQ_tensor_columns (q : Q) (T : SpinIndex → Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    generatedCentralizerTensorAction (generatedLocalIntoCentralizer (inclQ q)) T t i =
      spinRepresentation q (fun u => T u i) t := by
  have h := generatedLocal_tensor_action (localFiberIncl q) T
  change generatedCentralizerTensorAction (generatedLocalIntoCentralizer (inclQ q)) T = _ at h
  rw [h, localFiberQ_tensor_columns]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
