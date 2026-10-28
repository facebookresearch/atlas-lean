/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Recognition of the actual matrix-fixing, diagonally signed tensor residual. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensorResidualShortProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTraceOperators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinShortNormalizer

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix TensorProduct
set_option backward.isDefEq.respectTransparency false

private theorem short_coefficient_nonzero (r : GriessShortIndex) :
    ∃ i j : Fin 24, conwayTensorCoefficient r i j ≠ 0 := by
  by_contra h
  push Not at h
  have hM : centralizerShortSpatialMatrix r = 0 := by
    ext i j
    exact h i j
  have ht := conwayTensorCoefficient_trace_square r
  rw [hM, zero_mul, Matrix.trace_zero] at ht
  norm_num at ht

private theorem short_operator_insert (r : GriessShortIndex) (j : Fin 24)
    (x : SpinSpace) (t : SpinIndex) (i : Fin 24) :
    conwayTensorShortOperator r (tensorColumnInsert j x) t i =
      spinOperator (griessShortQ r) x t * conwayTensorCoefficient r i j := by
  have hins : tensorColumnInsert j x =
      conwayTensorCoordinates (x ⊗ₜ[ℝ] (Pi.single j (1 : ℝ))) := by
    funext t i
    simp [tensorColumnInsert, conwayTensorCoordinates_tmul, Pi.single_apply, eq_comm]
  rw [hins, conwayTensorShortOperator_tmul, conwayTensorCoordinates_tmul]
  change spinOperator (griessShortQ r) x t *
    (conwayTensorCoefficient r *ᵥ Pi.single j (1 : ℝ)) i = _
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

private theorem spin_column_insert (g : generatedCentralizer)
    (e : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (hcols : ∀ (T : SpinIndex → Fin 24 → ℝ) t i,
      generatedCentralizerTensorAction g T t i = e (fun u => T u i) t)
    (j : Fin 24) (x : SpinSpace) :
    generatedCentralizerTensorAction g (tensorColumnInsert j x) = tensorColumnInsert j (e x) := by
  funext t i
  rw [hcols]
  by_cases hi : i = j
  · subst i
    simp [tensorColumnInsert]
  · simp only [tensorColumnInsert, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_false]
    change e 0 t = 0
    rw [map_zero]
    rfl

/-- Diagonal short-vector signs give signed intertwining of the actual spin operators. -/
theorem generatedCentralizerTensorAction_spin_signed_short (g : generatedCentralizer)
    (e : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (hcols : ∀ (T : SpinIndex → Fin 24 → ℝ) t i,
      generatedCentralizerTensorAction g T t i = e (fun u => T u i) t)
    (r : GriessShortIndex) (c : ZMod 2)
    (hc : generatedCentralizerShortAction g (shortCoordinateUnit r) =
      qSign c • shortCoordinateUnit r) (x : SpinSpace) :
    e (spinOperator (griessShortQ r) x) = qSign c • spinOperator (griessShortQ r) (e x) := by
  obtain ⟨i, j, hij⟩ := short_coefficient_nonzero r
  have h := generatedCentralizerTensorAction_signed_short g r c hc (tensorColumnInsert j x)
  rw [spin_column_insert g e hcols] at h
  funext t
  have ht := congrFun (congrFun h t) i
  rw [hcols, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, short_operator_insert] at ht
  have hcol : (fun u => conwayTensorShortOperator r (tensorColumnInsert j x) u i) =
      conwayTensorCoefficient r i j • spinOperator (griessShortQ r) x := by
    funext u
    rw [short_operator_insert]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  rw [hcol, map_smul, Pi.smul_apply, smul_eq_mul] at ht
  simp only [Pi.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hij
  calc
    conwayTensorCoefficient r i j * e (spinOperator (griessShortQ r) x) t =
        qSign c * (spinOperator (griessShortQ r) (e x) t *
          conwayTensorCoefficient r i j) := ht
    _ = conwayTensorCoefficient r i j *
        (qSign c * spinOperator (griessShortQ r) (e x) t) := by ring

/-- The matrix-fixing centralizer with diagonal short signs has a represented Q spin factor. -/
theorem generatedCentralizerTensorAction_q_columns (g : generatedCentralizer)
    (hfix : ∀ A : Sym24, g.val.val (generatedCentralPlusEmbed A 0).val =
      (generatedCentralPlusEmbed A 0).val)
    (hshort : ∀ r : GriessShortIndex, ∃ c : ZMod 2,
      generatedCentralizerShortAction g (shortCoordinateUnit r) =
        qSign c • shortCoordinateUnit r) :
    ∃ q : Q, ∀ (T : SpinIndex → Fin 24 → ℝ) t i,
      generatedCentralizerTensorAction g T t i = spinRepresentation q (fun u => T u i) t := by
  obtain ⟨e, he, hcols⟩ := generatedCentralizerTensorAction_orthogonal_spin_columns g hfix
  obtain ⟨q, hq⟩ := spinShort_recognize_operator e he (by
    intro r
    obtain ⟨c, hc⟩ := hshort r
    exact ⟨c, generatedCentralizerTensorAction_spin_signed_short g e hcols r c hc⟩)
  exact ⟨q, by simpa only [hq] using hcols⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
