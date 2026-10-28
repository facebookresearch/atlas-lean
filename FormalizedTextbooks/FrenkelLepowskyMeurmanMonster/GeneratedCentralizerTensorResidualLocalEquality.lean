/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The matrix-fixing, diagonally signed residual is an actual local Q element. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensorResidualLocalCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem residual_short_unit_match (g : generatedCentralizer) (q : Q)
    (hcols : ∀ (T : SpinIndex → Fin 24 → ℝ) t i,
      generatedCentralizerTensorAction g T t i = spinRepresentation q (fun u => T u i) t)
    (r : GriessShortIndex) (c : ZMod 2)
    (hc : generatedCentralizerShortAction g (shortCoordinateUnit r) =
      qSign c • shortCoordinateUnit r) :
    generatedCentralizerShortAction g (shortCoordinateUnit r) =
      generatedCentralizerShortAction (generatedLocalIntoCentralizer (inclQ q))
        (shortCoordinateUnit r) := by
  let x : SpinSpace := (spinRepresentation q).symm
    ((spinRepresentation (griessShortQ r)).symm (fun _ => 1))
  have hx : spinOperator (griessShortQ r) (spinRepresentation q x) (0 : SpinIndex) = 1 := by
    change spinRepresentation (griessShortQ r)
      (spinRepresentation q ((spinRepresentation q).symm
        ((spinRepresentation (griessShortQ r)).symm (fun _ => 1)))) (0 : SpinIndex) = 1
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hg := generatedCentralizerTensorAction_spin_signed_short g (spinRepresentation q)
    hcols r c hc x
  have hl := generatedCentralizerTensorAction_spin_signed_short
    (generatedLocalIntoCentralizer (inclQ q)) (spinRepresentation q)
    (generatedLocalQ_tensor_columns q) r (localShortPhase (localFiberIncl q) r)
    (generatedLocalQ_short_unit q r) x
  have hs := congrArg (fun z : SpinSpace => z (0 : SpinIndex)) (hg.symm.trans hl)
  simp only [Pi.smul_apply, smul_eq_mul, hx, mul_one] at hs
  rw [hc, generatedLocalQ_short_unit, hs]

private theorem actual_coordinate_decomposition (x : GriessSpace) :
    x = (generatedCentralPlusEmbed (griessConwaySym24 x) 0).val +
      (generatedCentralPlusEmbed 0 (griessConwayEncode x).2.1).val +
      (generatedCentralMinusTensorEquiv.symm (griessConwayEncode x).2.2).val := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  have ht : griessConwayEncode
      (generatedCentralMinusTensorEquiv.symm (griessConwayEncode x).2.2).val =
      (0, (0, (griessConwayEncode x).2.2)) :=
    griessConwayEncode_decode _ (by intro i j; rfl)
  change griessConwayEncodeLinear x = griessConwayEncodeLinear (_ + _ + _)
  rw [map_add, map_add]
  change griessConwayEncode x =
    griessConwayEncode (generatedCentralPlusEmbed (griessConwaySym24 x) 0).val +
    griessConwayEncode (generatedCentralPlusEmbed 0 (griessConwayEncode x).2.1).val +
    griessConwayEncode
      (generatedCentralMinusTensorEquiv.symm (griessConwayEncode x).2.2).val
  rw [generatedCentralPlusEmbed_encode, generatedCentralPlusEmbed_encode, ht]
  apply Prod.ext
  · simp [griessConwaySym24]
  · apply Prod.ext <;> simp

private theorem realPi_linearMap_ext {ι : Type*} [Finite ι] [DecidableEq ι]
    (F G : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (h : ∀ r : ι, F (Pi.single r (1 : ℝ)) = G (Pi.single r (1 : ℝ))) : F = G := by
  let _ := Fintype.ofFinite ι
  apply (Pi.basisFun ℝ ι).ext
  intro r
  simpa only [Pi.basisFun_apply] using h r

/-- Matching tensor columns and all short signs identifies the whole residual with local Q. -/
theorem generatedCentralizerTensorResidual_eq_localQ (g : generatedCentralizer) (q : Q)
    (hfix : ∀ A : Sym24, g.val.val (generatedCentralPlusEmbed A 0).val =
      (generatedCentralPlusEmbed A 0).val)
    (hshort : ∀ r : GriessShortIndex, ∃ c : ZMod 2,
      generatedCentralizerShortAction g (shortCoordinateUnit r) =
        qSign c • shortCoordinateUnit r)
    (hcols : ∀ (T : SpinIndex → Fin 24 → ℝ) t i,
      generatedCentralizerTensorAction g T t i = spinRepresentation q (fun u => T u i) t) :
    g = generatedLocalIntoCentralizer (inclQ q) := by
  let k := generatedLocalIntoCentralizer (inclQ q)
  have hshortMap : (generatedCentralizerShortAction g).toLinearMap =
      (generatedCentralizerShortAction k).toLinearMap := by
    apply realPi_linearMap_ext
    intro r
    obtain ⟨c, hc⟩ := hshort r
    exact residual_short_unit_match g q hcols r c hc
  have hshortEq (X : GriessShortIndex → ℝ) :
      generatedCentralizerShortAction g X = generatedCentralizerShortAction k X :=
    congrArg (fun f : (GriessShortIndex → ℝ) →ₗ[ℝ] (GriessShortIndex → ℝ) => f X) hshortMap
  have htensor (T : SpinIndex → Fin 24 → ℝ) :
      generatedCentralizerTensorAction g T = generatedCentralizerTensorAction k T := by
    funext t i
    rw [hcols, generatedLocalQ_tensor_columns]
  have hminus (x : generatedCentralMinus) : g.val.val x.val = k.val.val x.val := by
    have he : generatedCentralizerMinusEquiv g x = generatedCentralizerMinusEquiv k x := by
      apply generatedCentralMinusTensorEquiv.injective
      rw [← generatedCentralizerTensorAction_intertwines,
        ← generatedCentralizerTensorAction_intertwines, htensor]
    exact congrArg Subtype.val he
  have hmatrix (A : Sym24) :
      g.val.val (generatedCentralPlusEmbed A 0).val =
        k.val.val (generatedCentralPlusEmbed A 0).val := by
    rw [hfix, generatedLocalQ_matrix_fixed]
  have hshortVector (X : GriessShortIndex → ℝ) :
      g.val.val (generatedCentralPlusEmbed 0 X).val =
        k.val.val (generatedCentralPlusEmbed 0 X).val := by
    rw [generatedCentralizerShortAction_embed, generatedCentralizerShortAction_embed, hshortEq]
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [actual_coordinate_decomposition x, map_add, map_add, map_add, map_add,
    hmatrix, hshortVector, hminus]

/-- The matrix-fixing, diagonally signed centralizer residual is in the actual local Q image. -/
theorem generatedCentralizerTensorResidual_mem_localQ (g : generatedCentralizer)
    (hfix : ∀ A : Sym24, g.val.val (generatedCentralPlusEmbed A 0).val =
      (generatedCentralPlusEmbed A 0).val)
    (hshort : ∀ r : GriessShortIndex, ∃ c : ZMod 2,
      generatedCentralizerShortAction g (shortCoordinateUnit r) =
        qSign c • shortCoordinateUnit r) :
    ∃ q : Q, g = generatedLocalIntoCentralizer (inclQ q) := by
  obtain ⟨q, hq⟩ := generatedCentralizerTensorAction_q_columns g hfix hshort
  exact ⟨q, generatedCentralizerTensorResidual_eq_localQ g q hfix hshort hq⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
