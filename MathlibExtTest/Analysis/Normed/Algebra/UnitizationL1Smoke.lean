/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.Normed.Algebra.UnitizationL1
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The continuous product equivalence for complex L¹ unitization

The unitization element with scalar coordinate `i` and algebra coordinate
two has L¹ norm three and maps to `(i,i+2)`. The inverse of `(i,2)` has
algebra coordinate `2-i`. Multiplication, both embeddings, and both
continuous directions retain these nonzero complex coordinates.
-/

noncomputable section

namespace MathlibExtTest.UnitizationL1

private abbrev Space := WithLp 1 (Unitization ℂ ℂ)
private abbrev productEquiv := WithLp.unitalUnitizationProdContinuousAlgEquiv ℂ ℂ

private def element : Space :=
  WithLp.toLp 1 (Unitization.inl Complex.I + Unitization.inr (2 : ℂ))

private theorem forward_value : productEquiv element = (Complex.I, Complex.I + 2) := by
  apply Prod.ext <;> simp [element]

example : productEquiv element = (Complex.I, Complex.I + 2) := forward_value

example : ‖element‖ = 3 ∧ element ≠ 0 := by
  have hn : ‖element‖ = 3 := by
    rw [WithLp.unitization_norm_def]
    norm_num [element]
  refine ⟨hn, ?_⟩
  intro h
  rw [h, norm_zero] at hn
  norm_num at hn

example :
    (productEquiv.symm (Complex.I, 2)).ofLp.fst = Complex.I ∧
      (productEquiv.symm (Complex.I, 2)).ofLp.snd = 2 - Complex.I := by
  simp [productEquiv]

example : productEquiv.symm (productEquiv element) = element :=
  productEquiv.symm_apply_apply element

example : productEquiv (element * element) = (-1, 3 + 4 * Complex.I) := by
  rw [map_mul, forward_value]
  ext <;> simp [mul_add, add_mul, Complex.I_mul_I]; ring

example :
    productEquiv (algebraMap ℂ Space Complex.I) = (Complex.I, Complex.I) ∧
      productEquiv (WithLp.toLp 1 (Unitization.inr (2 : ℂ))) = (0, 2) := by
  simp [productEquiv]

example : Continuous (productEquiv : Space → ℂ × ℂ) ∧
    Continuous (productEquiv.symm : ℂ × ℂ → Space) :=
  ⟨productEquiv.continuous, productEquiv.symm.continuous⟩

end MathlibExtTest.UnitizationL1
