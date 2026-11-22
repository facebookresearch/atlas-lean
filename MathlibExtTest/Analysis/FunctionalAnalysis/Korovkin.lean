/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.Korovkin
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.KorovkinTest

open Filter Topology
open scoped unitInterval Topology
open MathlibExt.Analysis.FunctionalAnalysis.Korovkin

noncomputable section

/-- The operators `Lₙ f (x) = (1 - 1/(n+1)) * f x + (1/(n+1)) * f 0`,
which mix `f` with its value at `0`. They are positive, and they converge
to the identity on the Korovkin test functions, so Korovkin's theorem
applies to them. -/
def mixOperator (n : ℕ) : C(I, ℝ) →ₗ[ℝ] C(I, ℝ) where
  toFun f :=
    ⟨fun x => (1 - ((n : ℝ) + 1)⁻¹) * f x + ((n : ℝ) + 1)⁻¹ * f 0,
      by exact (continuous_const.mul f.continuous).add continuous_const⟩
  map_add' f g := by
    ext x
    simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply]
    ring
  map_smul' c f := by
    ext x
    simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem mixOperator_apply (n : ℕ) (f : C(I, ℝ)) (x : I) :
    mixOperator n f x =
      (1 - ((n : ℝ) + 1)⁻¹) * f x + ((n : ℝ) + 1)⁻¹ * f 0 :=
  rfl

/-- The mixing operators are positive. -/
theorem mixOperator_pos (n : ℕ) (f : C(I, ℝ)) (hf : ∀ x, 0 ≤ f x) (x : I) :
    0 ≤ mixOperator n f x := by
  rw [mixOperator_apply]
  have hα1 : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Nat.le_add_left 1 n |>.trans_eq' (by norm_num))
  have hα0 : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := inv_nonneg.mpr (by positivity)
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hα1) (hf x)) (mul_nonneg hα0 (hf 0))

/-- The mixing operators fix the constant function `1`. -/
theorem mixOperator_one (n : ℕ) : mixOperator n (1 : C(I, ℝ)) = 1 := by
  ext x
  rw [mixOperator_apply]
  simp only [ContinuousMap.one_apply]
  ring

/-- On the identity function, the mixing operators are the scalars
`1 - 1/(n+1)`. -/
theorem mixOperator_id (n : ℕ) :
    mixOperator n korovkinId = (1 - ((n : ℝ) + 1)⁻¹) • korovkinId := by
  ext x
  rw [mixOperator_apply]
  simp only [korovkinId_apply, ContinuousMap.smul_apply, smul_eq_mul,
    show ((0 : I) : ℝ) = 0 from rfl]
  ring

/-- On the square function, the mixing operators are the scalars
`1 - 1/(n+1)`. -/
theorem mixOperator_sq (n : ℕ) :
    mixOperator n korovkinIdSq = (1 - ((n : ℝ) + 1)⁻¹) • korovkinIdSq := by
  ext x
  rw [mixOperator_apply]
  simp only [korovkinIdSq_apply, ContinuousMap.smul_apply, smul_eq_mul,
    show ((0 : I) : ℝ) = 0 from rfl]
  ring

/-- Korovkin's theorem applied to the mixing operators: they converge to
the identity on every continuous function. -/
example (f : C(I, ℝ)) :
    Tendsto (fun n => mixOperator n f) atTop (𝓝 f) := by
  have hα : Tendsto (fun n : ℕ => (1 - ((n : ℝ) + 1)⁻¹)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ))).sub h0
    simpa using h
  apply korovkin (L := mixOperator) (f := f)
  · intro n g hg x
    exact mixOperator_pos n g hg x
  · have h : (fun n => mixOperator n (1 : C(I, ℝ))) = fun _ => (1 : C(I, ℝ)) :=
      funext fun n => mixOperator_one n
    rw [h]
    exact tendsto_const_nhds
  · have h : (fun n => mixOperator n korovkinId) =
        fun n : ℕ => (1 - ((n : ℝ) + 1)⁻¹) • korovkinId :=
      funext fun n => mixOperator_id n
    rw [h]
    have hsmul : Tendsto (fun n : ℕ => (1 - ((n : ℝ) + 1)⁻¹) • korovkinId) atTop
        (𝓝 ((1 : ℝ) • korovkinId)) :=
      hα.smul (tendsto_const_nhds : Tendsto (fun _ : ℕ => korovkinId) atTop (𝓝 korovkinId))
    simpa using hsmul
  · have h : (fun n => mixOperator n korovkinIdSq) =
        fun n : ℕ => (1 - ((n : ℝ) + 1)⁻¹) • korovkinIdSq :=
      funext fun n => mixOperator_sq n
    rw [h]
    have hsmul : Tendsto (fun n : ℕ => (1 - ((n : ℝ) + 1)⁻¹) • korovkinIdSq) atTop
        (𝓝 ((1 : ℝ) • korovkinIdSq)) :=
      hα.smul (tendsto_const_nhds : Tendsto (fun _ : ℕ => korovkinIdSq) atTop (𝓝 korovkinIdSq))
    simpa using hsmul

/-- A concrete evaluation: at `n = 3` and `x = 1/2`, the mixing operator
applied to the square function gives `(3/4) * (1/4) = 3/16`. -/
example :
    mixOperator 3 korovkinIdSq ⟨1 / 2, by norm_num⟩ = 3 / 16 := by
  rw [mixOperator_apply]
  simp only [korovkinIdSq_apply, show ((0 : I) : ℝ) = 0 from rfl]
  norm_num

end

end MathlibExt.Analysis.FunctionalAnalysis.KorovkinTest
