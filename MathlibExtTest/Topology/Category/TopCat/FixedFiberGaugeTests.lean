/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.FixedFiberGauge
import Mathlib.Topology.Category.TopCat.Monoidal
import Mathlib.Tactic.NormNum

/-! # Nonidentity affine gauges and fixed-fiber coordinate transitions -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace MathlibExtTest.TopCatFixedFiberGauge

private abbrev B : TopCat := TopCat.of ℝ

private def shear : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun x := (x.1, x.2 + x.1)
  invFun x := (x.1, x.2 - x.1)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add continuous_fst)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_fst)

private def a : FixedFiberGauge B B where
  e := TopCat.isoOfHomeo shear
  hom_fst := by apply TopCat.hom_ext; ext x; rfl

private def h₀ : TrivialBundleWithFiber B (CartesianMonoidalCategory.fst B B) where
  r := CartesianMonoidalCategory.snd B B
  isLimit := CartesianMonoidalCategory.tensorProductIsBinaryProduct B B

private def h₁ := h₀.gauge a

example : a.e.hom (2, 3) = (2, 5) := by
  change (2, (3 : ℝ) + 2) = (2, 5)
  norm_num

example : h₁.r (2, 3) = 5 := by
  change (3 : ℝ) + 2 = 5
  norm_num

example : h₁.gauge (TrivialBundleWithFiber.transitionGauge h₀ h₁) = h₀ :=
  TrivialBundleWithFiber.gauge_transition h₀ h₁

example : (a.baseChange (𝟙 B)).e.hom = a.e.hom := by
  apply CartesianMonoidalCategory.hom_ext
  · exact (a.baseChange (𝟙 B)).hom_fst.trans a.hom_fst.symm
  · rw [FixedFiberGauge.baseChange_hom_snd]
    have hid : CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst B B ≫ 𝟙 B)
        (CartesianMonoidalCategory.snd B B) = 𝟙 (B ⊗ B) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hid, Category.id_comp]

example : (a.baseChange (𝟙 B)).e.hom (2, 3) = (2, 5) := by
  change (2, (3 : ℝ) + 2) = (2, 5)
  norm_num

end MathlibExtTest.TopCatFixedFiberGauge
