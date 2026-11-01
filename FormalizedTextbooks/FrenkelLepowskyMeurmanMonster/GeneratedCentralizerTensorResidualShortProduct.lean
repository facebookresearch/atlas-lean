/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual tensor residual intertwines each actual short Pauli operator. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensorResidualOrthogonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerJordan
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortCoordinateRecognition

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem weighted_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → SpinIndex → Fin 24 → ℝ) (r : ι) :
    (1 / 8 : ℝ) • ∑ s, (Pi.single r (1 : ℝ) : ι → ℝ) s • P s = (1 / 8 : ℝ) • P r := by
  simp [Pi.single_apply, ite_smul]

private theorem short_single_tensor (r : GriessShortIndex) (T : SpinIndex → Fin 24 → ℝ) :
    conwayShortTensorProduct (shortCoordinateUnit r) T =
      (1 / 8 : ℝ) • conwayTensorShortOperator r T := by
  exact weighted_single (fun s => conwayTensorShortOperator s T) r

private theorem weighted_zero {ι : Type*} [Fintype ι]
    (P : ι → (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ] (SpinIndex → Fin 24 → ℝ)) (Y : ι → ℝ) :
    (1 / 8 : ℝ) • ∑ s, Y s • P s 0 = 0 := by
  simp only [map_zero, smul_zero, Finset.sum_const_zero]

private theorem short_tensor_zero (X : GriessShortIndex → ℝ) :
    conwayShortTensorProduct X 0 = 0 := by
  exact weighted_zero conwayTensorShortOperator X

/-- An actual unit short vector acts on tensors by one eighth of its actual Pauli operator. -/
theorem generatedCentralShort_tensorMul_coordinates (r : GriessShortIndex)
    (x : generatedCentralMinus) :
    generatedCentralMinusTensorEquiv
      (generatedCentralTensorMul (generatedCentralPlusEmbed 0 (shortCoordinateUnit r)) x) =
      (1 / 8 : ℝ) • conwayTensorShortOperator r (generatedCentralMinusTensorEquiv x) := by
  have hx := (mem_generatedCentralMinus_iff_matrix_short_zero x.val).mp x.property
  have hxp : griessConwayEncode x.val =
      (0, (0, generatedCentralMinusTensorEquiv x)) := Prod.ext hx.1 (Prod.ext hx.2 rfl)
  change (griessConwayEncode (griessProd
    (generatedCentralPlusEmbed 0 (shortCoordinateUnit r)).val x.val)).2.2 = _
  rw [griessProd_encode, generatedCentralPlusEmbed_encode, hxp,
    conwayRawProduct_eq_blocks]
  simp only [Submodule.coe_zero, map_zero, LinearMap.zero_apply, add_zero, zero_add,
    short_tensor_zero]
  exact short_single_tensor r _

private theorem tensorMul_smul (c : ℝ) (u : generatedCentralPlus) (x : generatedCentralMinus) :
    generatedCentralTensorMul (c • u) x = c • generatedCentralTensorMul u x := by
  apply Subtype.ext
  exact congrArg (fun f : GriessSpace →ₗ[ℝ] GriessSpace => f x.val)
    (griessProd.map_smul c u.val)

private theorem short_image_plus (g : generatedCentralizer) (r : GriessShortIndex)
    (c : ZMod 2)
    (hc : generatedCentralizerShortAction g (shortCoordinateUnit r) =
      qSign c • shortCoordinateUnit r) :
    generatedCentralizerPlusEquiv g (generatedCentralPlusEmbed 0 (shortCoordinateUnit r)) =
      qSign c • generatedCentralPlusEmbed 0 (shortCoordinateUnit r) := by
  apply Subtype.ext
  rw [show (generatedCentralizerPlusEquiv g
      (generatedCentralPlusEmbed 0 (shortCoordinateUnit r))).val =
    g.val.val (generatedCentralPlusEmbed 0 (shortCoordinateUnit r)).val from rfl,
    generatedCentralizerShortAction_embed, hc]
  have h := generatedCentralPlusCoordinates.symm.map_smul (qSign c)
    ((0, shortCoordinateUnit r) : Sym24 × (GriessShortIndex → ℝ))
  have hv := congrArg (fun x : generatedCentralPlus => x.val) h
  simpa only [Prod.smul_mk, smul_zero, generatedCentralPlusCoordinates_symm_apply] using hv

private theorem short_signed_tensor_commutes (g : generatedCentralizer) (r : GriessShortIndex)
    (c : ZMod 2)
    (hc : generatedCentralizerShortAction g (shortCoordinateUnit r) =
      qSign c • shortCoordinateUnit r) (x : generatedCentralMinus) :
    generatedCentralizerMinusEquiv g
      (generatedCentralTensorMul (generatedCentralPlusEmbed 0 (shortCoordinateUnit r)) x) =
      qSign c • generatedCentralTensorMul (generatedCentralPlusEmbed 0 (shortCoordinateUnit r))
        (generatedCentralizerMinusEquiv g x) := by
  have h := generatedCentralTensorMul_conjugate g
    (generatedCentralPlusEmbed 0 (shortCoordinateUnit r))
  rw [short_image_plus g r c hc] at h
  have he := congrArg (fun f => f (generatedCentralizerMinusEquiv g x)) h
  rw [tensorMul_smul, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply] at he
  exact he.symm

/-- A diagonal actual short sign forces signed commutation on the original tensor operator. -/
theorem generatedCentralizerTensorAction_signed_short (g : generatedCentralizer)
    (r : GriessShortIndex) (c : ZMod 2)
    (hc : generatedCentralizerShortAction g (shortCoordinateUnit r) =
      qSign c • shortCoordinateUnit r) (T : SpinIndex → Fin 24 → ℝ) :
    generatedCentralizerTensorAction g (conwayTensorShortOperator r T) =
      qSign c • conwayTensorShortOperator r (generatedCentralizerTensorAction g T) := by
  obtain ⟨x, rfl⟩ := generatedCentralMinusTensorEquiv.surjective T
  have h := congrArg generatedCentralMinusTensorEquiv (short_signed_tensor_commutes g r c hc x)
  rw [map_smul, generatedCentralShort_tensorMul_coordinates,
    ← generatedCentralizerTensorAction_intertwines,
    generatedCentralShort_tensorMul_coordinates, map_smul,
    ← generatedCentralizerTensorAction_intertwines] at h
  rw [smul_comm (qSign c) (1 / 8 : ℝ)] at h
  exact (smul_right_injective _ (by norm_num : (1 / 8 : ℝ) ≠ 0)) h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
