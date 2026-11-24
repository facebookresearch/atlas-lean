/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Topology.Category.TopCat.EndpointFixedCorrection

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace MathlibExtTest.Topology.Category.TopCat.EndpointFixedCorrection

variable {X Y : _root_.TopCat.{u}} {f₀ f₁ : X ⟶ Y}

example (K : _root_.TopCat.Homotopy f₀ f₁) :
    _root_.TopCat.EndpointFixedCorrection K :=
  _root_.TopCat.EndpointFixedCorrection.refl K

example (K : _root_.TopCat.Homotopy f₀ f₁)
    (c : _root_.TopCat.EndpointFixedCorrection K)
    (p : unitInterval × X) :
    c.comparison (0, p) = K p :=
  c.comparison_zero p

example (K : _root_.TopCat.Homotopy f₀ f₁)
    (c : _root_.TopCat.EndpointFixedCorrection K)
    (p : unitInterval × X) :
    c.comparison (1, p) = c.corrected p :=
  c.comparison_one p

example (K : _root_.TopCat.Homotopy f₀ f₁)
    (c : _root_.TopCat.EndpointFixedCorrection K)
    (s : unitInterval) (x : X) :
    c.comparison (s, (0, x)) = K (0, x) :=
  c.comparison_original_zero s x

example (K : _root_.TopCat.Homotopy f₀ f₁)
    (c : _root_.TopCat.EndpointFixedCorrection K)
    (s : unitInterval) (x : X) :
    c.comparison (s, (1, x)) = K (1, x) :=
  c.comparison_original_one s x

example : _root_.TopCat.homotopyReflTransReparam 0 = 0 := by simp

example : _root_.TopCat.homotopyReflTransReparam 1 = 1 := by simp

example (t : unitInterval) :
    _root_.TopCat.homotopyReflTransBlend (0, t) =
      _root_.TopCat.homotopyReflTransReparam t := by simp

example (t : unitInterval) :
    _root_.TopCat.homotopyReflTransBlend (1, t) = t := by simp

example (s : unitInterval) :
    _root_.TopCat.homotopyReflTransBlend (s, 0) = 0 := by simp

example (s : unitInterval) :
    _root_.TopCat.homotopyReflTransBlend (s, 1) = 1 := by simp

example (K : _root_.TopCat.Homotopy f₀ f₁)
    (t : unitInterval) (x : X) :
    ((_root_.TopCat.Homotopy.refl f₀).trans K) (t, x) =
      K (_root_.TopCat.homotopyReflTransReparam t, x) :=
  _root_.TopCat.homotopy_refl_trans_apply K t x

section Behavioral

/-- A nonconstant segment homotopy from the identity to zero. -/
private noncomputable def segK : _root_.TopCat.Homotopy
    (𝟙 (_root_.TopCat.of unitInterval))
    (_root_.TopCat.ofHom (ContinuousMap.const unitInterval 0)) where
  toFun p := Set.Icc.convexComb p.2 0 p.1
  continuous_toFun :=
    Set.Icc.continuous_convexComb_prod.comp
      (continuous_snd.prodMk
        ((continuous_const : Continuous
          fun _ : unitInterval × unitInterval =>
            (0 : unitInterval)).prodMk continuous_fst))
  map_zero_left _ := Set.Icc.convexComb_zero _ _
  map_one_left _ := Set.Icc.convexComb_one _ _

private def segMid : unitInterval := ⟨1 / 2, by norm_num⟩

/-- The reflexive correction computes back to the raw homotopy at a
concrete point. -/
example :
    (_root_.TopCat.EndpointFixedCorrection.refl segK).corrected
      (1, segMid) = 0 :=
  Set.Icc.convexComb_one _ _

/-- The comparison fixes the zero face at a concrete point. -/
example (s : unitInterval) :
    (_root_.TopCat.EndpointFixedCorrection.refl segK).comparison
      (s, (0, segMid)) = segMid := by
  have h := (_root_.TopCat.EndpointFixedCorrection.refl segK).comparison_original_zero
    s segMid
  rw [h]
  exact Set.Icc.convexComb_zero _ _

/-- The comparison fixes the one face at a concrete point. -/
example (s : unitInterval) :
    (_root_.TopCat.EndpointFixedCorrection.refl segK).comparison
      (s, (1, segMid)) = 0 := by
  have h := (_root_.TopCat.EndpointFixedCorrection.refl segK).comparison_original_one
    s segMid
  rw [h]
  exact Set.Icc.convexComb_one _ _

/-- The comparison ends at the corrected homotopy at a concrete point. -/
example :
    (_root_.TopCat.EndpointFixedCorrection.refl segK).comparison
      (1, (1, segMid)) = 0 := by
  have h := (_root_.TopCat.EndpointFixedCorrection.refl segK).comparison_one
    (1, segMid)
  rw [h]
  exact Set.Icc.convexComb_one _ _

end Behavioral

end MathlibExtTest.Topology.Category.TopCat.EndpointFixedCorrection

end
