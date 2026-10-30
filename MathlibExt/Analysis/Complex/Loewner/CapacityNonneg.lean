/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Complex.Loewner.CapacityProps

/-!
# Nonnegativity of half-plane capacity

If `g` has half-plane capacity `a` and does not increase imaginary parts on the upper half-plane
(`StatMech.SLE.ShrinksIm g`, which holds for the normalized conformal map removing a hull), then
`a ≥ 0`: along `z = iy`, `Re(z (g z - z)) = y (y - Im g(iy)) ≥ 0` tends to `a`. Consequently
half-plane capacity is monotone under composition with such maps.

## Main definitions

* `StatMech.SLE.ShrinksIm`: `Im g(z) ≤ Im z` on the upper half-plane.

## Main results

* `StatMech.SLE.hcap_nonneg_of_shrinksIm`: `ShrinksIm g → hcap g ≥ 0`.
* `StatMech.SLE.le_of_comp_of_shrinksIm`: `hcap g ≤ hcap (h ∘ g)` when `h` shrinks imaginary
  parts.
* `StatMech.SLE.shrinksIm_halfDisk`: the half-disk maps shrink imaginary parts.

## References

* G. F. Lawler, *Conformally Invariant Processes in the Plane*, AMS (2005), Section 3.4.
-/

@[expose] public section

open scoped UpperHalfPlane NNReal
open Filter Topology Complex Bornology

namespace StatMech.SLE

/-- `g` does not increase imaginary parts on the upper half-plane: `Im g(z) ≤ Im z` when
`Im z > 0`. -/
def ShrinksIm (g : ℂ → ℂ) : Prop := ∀ z : ℂ, 0 < z.im → (g z).im ≤ z.im

/-- `i y → ∞` as `y → +∞`. -/
theorem tendsto_imagRay_cocompact :
    Tendsto (fun y : ℝ => Complex.I * (y : ℂ)) atTop (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact (α := ℂ), ← comap_norm_atTop (E := ℂ),
    tendsto_comap_iff]
  have hnorm : (fun y : ℝ => ‖Complex.I * (y : ℂ)‖) = (fun y : ℝ => |y|) := by
    funext y
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  change Tendsto (fun y : ℝ => ‖Complex.I * (y : ℂ)‖) atTop atTop
  rw [hnorm]
  exact tendsto_abs_atTop_atTop

/-- `Re(i y (g(i y) - i y)) = y (y - Im g(i y))`. -/
theorem re_imagRay (g : ℂ → ℂ) (y : ℝ) :
    (Complex.I * (y : ℂ) *
        (g (Complex.I * (y : ℂ)) - Complex.I * (y : ℂ))).re
      = y * (y - (g (Complex.I * (y : ℂ))).im) := by
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- A map that has half-plane capacity `a` and does not increase imaginary parts has `a ≥ 0`. -/
theorem hcap_nonneg_of_shrinksIm {g : ℂ → ℂ} {a : ℝ}
    (hg : HasHalfPlaneCapacity g a) (hshrink : ShrinksIm g) : 0 ≤ a := by
  obtain ⟨_, ha⟩ := hg
  have hcomp :
      Tendsto (fun y : ℝ =>
          Complex.I * (y : ℂ) *
            (g (Complex.I * (y : ℂ)) - Complex.I * (y : ℂ)))
        atTop (𝓝 (a : ℂ)) :=
    ha.comp tendsto_imagRay_cocompact
  have hre :
      Tendsto (fun y : ℝ =>
          (Complex.I * (y : ℂ) *
              (g (Complex.I * (y : ℂ)) - Complex.I * (y : ℂ))).re)
        atTop (𝓝 a) := by
    have h := (Complex.continuous_re.tendsto (a : ℂ)).comp hcomp
    rw [Complex.ofReal_re] at h
    exact h
  have hnn : ∀ᶠ y : ℝ in atTop,
      0 ≤ (Complex.I * (y : ℂ) *
          (g (Complex.I * (y : ℂ)) - Complex.I * (y : ℂ))).re := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [re_imagRay]
    have him : (Complex.I * (y : ℂ)).im = y := by simp
    have hle : (g (Complex.I * (y : ℂ))).im ≤ y := by
      have hsh := hshrink (Complex.I * (y : ℂ)) (by rw [him]; exact hy)
      rwa [him] at hsh
    have hd : 0 ≤ y - (g (Complex.I * (y : ℂ))).im := by linarith
    positivity
  exact ge_of_tendsto hre hnn

/-- `z - z⁻¹` (capacity `-1`) increases imaginary parts, consistently with
`hcap_nonneg_of_shrinksIm`. -/
theorem shrinksIm_neg_example_false : ¬ ShrinksIm (fun z : ℂ => z - z⁻¹) := by
  intro h
  have hi := h Complex.I (by simp)
  simp only [Complex.I_im] at hi
  have hval : (Complex.I - Complex.I⁻¹) = (2 : ℂ) * Complex.I := by
    rw [Complex.inv_I]; ring
  rw [hval] at hi
  simp at hi

/-- For `c ≥ 0`, `z ↦ z + c/z` does not increase imaginary parts on the upper half-plane. -/
theorem shrinksIm_halfDisk {c : ℝ} (hc : 0 ≤ c) :
    ShrinksIm (fun z : ℂ => z + (c : ℂ) / z) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  simp only []
  rw [Complex.add_im, Complex.div_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, zero_sub]
  have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  have hnn : (0 : ℝ) ≤ c * z.im / Complex.normSq z := by positivity
  have hneg : -(c * z.im) / Complex.normSq z ≤ 0 := by rw [neg_div]; linarith
  linarith

/-- Trivial sanity check: the conclusion `0 ≤ c` is the hypothesis; the proof routes it through
`hcap_nonneg_of_shrinksIm`. -/
theorem hcap_halfDisk_nonneg {c : ℝ} (hc : 0 ≤ c) :
    (0 : ℝ) ≤ c :=
  hcap_nonneg_of_shrinksIm (hasHalfPlaneCapacity_halfDisk c) (shrinksIm_halfDisk hc)

/-- Monotonicity: if `g' = h ∘ g` and `h` does not increase imaginary parts, then
`hcap g ≤ hcap g'`. -/
theorem le_of_comp_of_shrinksIm {g h g' : ℂ → ℂ} {a b a' : ℝ}
    (hg : HasHalfPlaneCapacity g a) (hh : HasHalfPlaneCapacity h b)
    (hhull : ShrinksIm h) (hfac : g' = h ∘ g)
    (hg' : HasHalfPlaneCapacity g' a') :
    a ≤ a' :=
  hg.le_of_comp hh (hcap_nonneg_of_shrinksIm hh hhull) hfac hg'

end StatMech.SLE
