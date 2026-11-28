/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shape of Fieller's confidence sets

Completing the square classifies the set when its quadratic coefficient is nonzero.
-/

@[expose] public section

namespace WantedExt.Probability.Statistics.FiellerRatioWanted

/-- **Fieller's confidence set.** The set `{θ | (a - θ b)² ≤ z² (v_aa - 2 θ v_ab + θ² v_bb)}`. -/
def fiellerSet (a b vaa vab vbb z : ℝ) : Set ℝ :=
  {θ | (a - θ * b) ^ 2 ≤ z ^ 2 * (vaa - 2 * θ * vab + θ ^ 2 * vbb)}

private theorem variance_nonneg (vaa vab vbb x : ℝ) (hvaa : 0 ≤ vaa) (hvbb : 0 ≤ vbb)
    (hpsd : vab ^ 2 ≤ vaa * vbb) : 0 ≤ vaa - 2 * x * vab + x ^ 2 * vbb := by
  rcases eq_or_lt_of_le hvbb with hzero | hpos
  · have hvbb0 : vbb = 0 := hzero.symm
    have hvab : vab = 0 := by
      have hsq : vab ^ 2 ≤ 0 := by simpa [hvbb0] using hpsd
      exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg vab))
    simpa [hvbb0, hvab] using hvaa
  · apply nonneg_of_mul_nonneg_left _ hpos
    calc
      0 ≤ (x * vbb - vab) ^ 2 + (vaa * vbb - vab ^ 2) :=
        add_nonneg (sq_nonneg _) (sub_nonneg.mpr hpsd)
      _ = (vaa - 2 * x * vab + x ^ 2 * vbb) * vbb := by ring

/-- **Shape of Fieller's set.** Let `v_aa ≥ 0`, `v_bb ≥ 0` and `v_ab² ≤ v_aa v_bb`
(a positive semidefinite covariance), let `z > 0`, and let `a, b` be real. If `b² > z² v_bb`,
Fieller's set is a bounded closed interval `[l, u]` containing `a / b`. If `b² < z² v_bb`, it is
either the whole real line or the complement of a bounded open interval `(l, u)` with `l < u`.

Sources: E. C. Fieller, "Some problems in interval estimation", J. R. Statist. Soc. B 16 (1954)
175–185. -/
theorem fiellerSet_shape (a b vaa vab vbb z : ℝ) (hvaa : 0 ≤ vaa) (hvbb : 0 ≤ vbb)
    (hpsd : vab ^ 2 ≤ vaa * vbb) (hz : 0 < z) :
    (z ^ 2 * vbb < b ^ 2 →
        ∃ l u : ℝ, l ≤ u ∧ fiellerSet a b vaa vab vbb z = Set.Icc l u ∧ a / b ∈ Set.Icc l u) ∧
      (b ^ 2 < z ^ 2 * vbb →
        fiellerSet a b vaa vab vbb z = Set.univ ∨
          ∃ l u : ℝ, l < u ∧ fiellerSet a b vaa vab vbb z = (Set.Ioo l u)ᶜ) := by
  let A := b ^ 2 - z ^ 2 * vbb
  let c := (a * b - z ^ 2 * vab) / A
  let d := c ^ 2 - (a ^ 2 - z ^ 2 * vaa) / A
  have hmem (hA : A ≠ 0) (θ : ℝ) :
      θ ∈ fiellerSet a b vaa vab vbb z ↔ A * ((θ - c) ^ 2 - d) ≤ 0 := by
    have hc : A * c = a * b - z ^ 2 * vab := by
      dsimp only [c]
      field_simp
    have hd : A * ((a ^ 2 - z ^ 2 * vaa) / A) = a ^ 2 - z ^ 2 * vaa := by
      field_simp
    have hform : (a - θ * b) ^ 2 - z ^ 2 * (vaa - 2 * θ * vab + θ ^ 2 * vbb) =
        A * ((θ - c) ^ 2 - d) := by
      calc
        _ = A * θ ^ 2 - 2 * θ * (a * b - z ^ 2 * vab) + (a ^ 2 - z ^ 2 * vaa) := by
          dsimp only [A]
          ring
        _ = A * (θ - c) ^ 2 - (A * c ^ 2 - (a ^ 2 - z ^ 2 * vaa)) := by
          rw [← hc]
          ring
        _ = A * ((θ - c) ^ 2 - d) := by
          dsimp only [d]
          rw [mul_sub, mul_sub, hd]
    change (a - θ * b) ^ 2 ≤ z ^ 2 * (vaa - 2 * θ * vab + θ ^ 2 * vbb) ↔ _
    rw [← sub_nonpos, hform]
  constructor
  · intro h
    have hA : 0 < A := sub_pos.mpr h
    have hle (θ : ℝ) : θ ∈ fiellerSet a b vaa vab vbb z ↔ (θ - c) ^ 2 ≤ d := by
      simp [hmem hA.ne', mul_nonpos_iff, hA.le, not_le.mpr hA]
    have hb : b ≠ 0 := by
      intro hb
      have hn : 0 ≤ z ^ 2 * vbb := mul_nonneg (sq_nonneg z) hvbb
      simp [hb, not_lt.mpr hn] at h
    have hratio : a / b ∈ fiellerSet a b vaa vab vbb z := by
      change (a - a / b * b) ^ 2 ≤ z ^ 2 * (vaa - 2 * (a / b) * vab + (a / b) ^ 2 * vbb)
      simpa only [div_mul_cancel₀ _ hb, sub_self, zero_pow (by decide : 2 ≠ 0)] using
        mul_nonneg (pow_pos hz 2).le (variance_nonneg vaa vab vbb (a / b) hvaa hvbb hpsd)
    have hd : 0 ≤ d := (sq_nonneg _).trans ((hle _).mp hratio)
    let r := Real.sqrt d
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hrsq : r ^ 2 = d := Real.sq_sqrt hd
    have hset : fiellerSet a b vaa vab vbb z = Set.Icc (c - r) (c + r) := by
      ext θ
      rw [hle θ]
      change (θ - c) ^ 2 ≤ d ↔ c - r ≤ θ ∧ θ ≤ c + r
      rw [← hrsq, sq_le_sq, abs_of_nonneg hr, abs_le]
      constructor <;> intro hθ <;> exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    exact ⟨c - r, c + r, by linarith, hset, hset ▸ hratio⟩
  · intro h
    have hA : A < 0 := sub_neg.mpr h
    have hge (θ : ℝ) : θ ∈ fiellerSet a b vaa vab vbb z ↔ d ≤ (θ - c) ^ 2 := by
      simp [hmem hA.ne, mul_nonpos_iff, hA.le, not_le.mpr hA]
    by_cases hd : 0 < d
    · let r := Real.sqrt d
      have hr : 0 < r := Real.sqrt_pos.2 hd
      have hrsq : r ^ 2 = d := Real.sq_sqrt hd.le
      right
      refine ⟨c - r, c + r, by linarith, ?_⟩
      ext θ
      rw [hge θ]
      change d ≤ (θ - c) ^ 2 ↔ ¬ (c - r < θ ∧ θ < c + r)
      rw [← hrsq, ← not_lt, sq_lt_sq, abs_of_nonneg hr.le, abs_lt]
      refine not_congr ?_
      constructor <;> intro hθ <;> exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    · left
      ext θ
      simp only [hge, Set.mem_univ, iff_true]
      exact (le_of_not_gt hd).trans (sq_nonneg _)

open MeasureTheory ProbabilityTheory in
/-- **Exact coverage of Fieller's set.** Let `μ` be a probability measure and let
`(a, b) : Ω → ℝ × ℝ` have a Gaussian law under `μ`, with `Var a = v_aa`, `Var b = v_bb`,
`Cov(a, b) = v_ab` and means satisfying `E a = θ E b`. Assume
`V(θ) = v_aa - 2 θ v_ab + θ² v_bb > 0` and let `z > 0`. Then the probability that `θ` lies in
Fieller's set computed from `(a, b)` equals the standard Gaussian probability of `[-z, z]`.

Sources: E. C. Fieller, "Some problems in interval estimation", J. R. Statist. Soc. B 16 (1954)
175–185; E. C. Fieller, "The biological standardization of insulin", Suppl. J. R. Statist. Soc. 7
(1940) 1–64. -/
theorem measureReal_mem_fiellerSet {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (a b : Ω → ℝ) (hG : HasGaussianLaw (fun ω => (a ω, b ω)) μ)
    (vaa vab vbb θ z : ℝ) (hvaa : Var[a; μ] = vaa) (hvbb : Var[b; μ] = vbb)
    (hvab : cov[a, b; μ] = vab) (hmean : ∫ ω, a ω ∂μ = θ * ∫ ω, b ω ∂μ)
    (hV : 0 < vaa - 2 * θ * vab + θ ^ 2 * vbb) (hz : 0 < z) :
    μ.real {ω | θ ∈ fiellerSet (a ω) (b ω) vaa vab vbb z} =
      (gaussianReal 0 1).real (Set.Icc (-z) z) := by
  let V := vaa - 2 * θ * vab + θ ^ 2 * vbb
  let D : Ω → ℝ := fun ω ↦ a ω - θ * b ω
  have hD : HasGaussianLaw D μ :=
    hG.map_fun (ContinuousLinearMap.fst ℝ ℝ ℝ - θ • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hDmean : ∫ ω, D ω ∂μ = 0 := by
    dsimp only [D]
    rw [integral_sub hG.fst.integrable (hG.snd.integrable.const_mul θ), integral_const_mul,
      hmean, sub_self]
  have hDvar : Var[D; μ] = V := by
    dsimp only [D, V]
    have hb : MemLp (fun ω ↦ θ * b ω) 2 μ := hG.snd.memLp_two.const_mul θ
    rw [variance_fun_sub hG.fst.memLp_two hb, covariance_const_mul_right,
      variance_const_mul, hvaa, hvbb, hvab]
    ring
  let s := Real.sqrt V
  have hs : 0 < s := Real.sqrt_pos.2 hV
  have hs_sq : s ^ 2 = V := Real.sq_sqrt hV.le
  let X : Ω → ℝ := fun ω ↦ s⁻¹ * D ω
  have hX : HasGaussianLaw X μ := hD.fun_smul s⁻¹
  have hXmean : ∫ ω, X ω ∂μ = 0 := by
    change (∫ ω, s⁻¹ * D ω ∂μ) = 0
    rw [integral_const_mul, hDmean, mul_zero]
  have hXvar : Var[X; μ] = 1 := by
    change Var[fun ω ↦ s⁻¹ * D ω; μ] = 1
    rw [variance_const_mul, hDvar, ← hs_sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hs.ne')]
  have hmap : μ.map X = gaussianReal 0 1 := by
    rw [hX.map_eq_gaussianReal, hXmean, hXvar, Real.toNNReal_one]
  have hevent : {ω | θ ∈ fiellerSet (a ω) (b ω) vaa vab vbb z} = X ⁻¹' Set.Icc (-z) z := by
    ext ω
    change D ω ^ 2 ≤ z ^ 2 * V ↔ X ω ∈ Set.Icc (-z) z
    rw [Set.mem_Icc, ← abs_le]
    calc
      _ ↔ X ω ^ 2 ≤ z ^ 2 := by
        change D ω ^ 2 ≤ z ^ 2 * V ↔ (s⁻¹ * D ω) ^ 2 ≤ z ^ 2
        rw [inv_mul_eq_div, div_pow, div_le_iff₀ (pow_pos hs 2), hs_sq]
      _ ↔ |X ω| ≤ z := by rw [sq_le_sq, abs_of_nonneg hz.le]
  rw [hevent]
  unfold Measure.real
  rw [← Measure.map_apply_of_aemeasurable hX.aemeasurable measurableSet_Icc, hmap]

end WantedExt.Probability.Statistics.FiellerRatioWanted
