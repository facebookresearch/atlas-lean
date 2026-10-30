/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Lp.StrictConvex

@[expose] public section

namespace MathlibExtTest.Analysis.Normed.Lp.StrictConvex

open scoped ENNReal

open MeasureTheory

open MathlibExt.Analysis.Normed.Lp.StrictConvex

instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

instance : Fact (1 < (2 : ℝ≥0∞).toReal) := ⟨by norm_num⟩

noncomputable section

/-- The constant `1` function as an element of `L²` over `Unit`. -/
abbrev F1 : Lp ℝ 2 (Measure.count : MeasureTheory.Measure Unit) :=
  MemLp.toLp (fun _ : Unit => (1 : ℝ)) (memLp_const 1)

/-- The constant `-1` function as an element of `L²` over `Unit`. -/
abbrev Fm1 : Lp ℝ 2 (Measure.count : MeasureTheory.Measure Unit) :=
  MemLp.toLp (fun _ : Unit => (-1 : ℝ)) (memLp_const (-1))

/-- The `L²`-norm of a constant function on the one-point space is the
absolute value of the constant. -/
theorem eLpNorm_unit_const (c : ℝ) (hc : ‖c‖ = 1) :
    eLpNorm (fun _ : Unit => c) 2 (Measure.count : MeasureTheory.Measure Unit) = 1 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) aestronglyMeasurable_const]
  rw [lintegral_count]
  simp [hc, ← ofReal_norm]

theorem norm_F1 : ‖F1‖ = 1 := by
  rw [Lp.norm_toLp, eLpNorm_unit_const 1 (by norm_num)]
  exact ENNReal.toReal_one

theorem norm_Fm1 : ‖Fm1‖ = 1 := by
  rw [Lp.norm_toLp, eLpNorm_unit_const (-1) (by norm_num)]
  exact ENNReal.toReal_one

theorem F1_ne_Fm1 : F1 ≠ Fm1 := by
  intro h
  have h2 : (fun _ : Unit => (1 : ℝ)) =ᵐ[(Measure.count : MeasureTheory.Measure Unit)]
      (fun _ : Unit => (-1 : ℝ)) := (MemLp.toLp_eq_toLp_iff (memLp_const (1:ℝ)) (memLp_const (-1:ℝ))).mp h
  have h3 := (Measure.ae_count_iff.mp h2) ()
  norm_num at h3

end

-- The midpoint of the two concrete unit vectors in `L²(Unit)` has norm `< 1`.
example : ‖(1 / 2 : ℝ) • F1 + (1 / 2 : ℝ) • Fm1‖ < 1 :=
  norm_midpoint_lt_of_norm_eq_one (p := 2) F1_ne_Fm1 norm_F1 norm_Fm1 (by norm_num)

-- The scalar estimate: `‖(1 + I) / 2‖ ^ 2 < 1` in `ℂ`.
example : ‖(1 - (1 / 2 : ℝ)) • (1 : ℂ) + (1 / 2 : ℝ) • Complex.I‖ ^ (2 : ℝ) <
    (1 - (1 / 2 : ℝ)) * ‖(1 : ℂ)‖ ^ (2 : ℝ) +
      (1 / 2 : ℝ) * ‖Complex.I‖ ^ (2 : ℝ) :=
  norm_convex_comb_rpow_lt
    (by intro h; exact one_ne_zero (congrArg Complex.re h))
    (by norm_num) (by norm_num) (by norm_num)

-- Strict convexity of the unit ball of `L^p`, in hypothesis form.
example {μ : Measure ℝ} {f g : Lp ℝ 2 μ} (hfg : f ≠ g)
    (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ‖(1 - t) • f + t • g‖ < 1 :=
  norm_convex_comb_lt_of_norm_le_one (p := 2) hfg hf hg ht0 ht1 (by norm_num)

-- The equality case of Minkowski's inequality, in hypothesis form.
example {μ : Measure ℝ} {f g : Lp ℝ 2 μ} (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (h : ‖f + g‖ = ‖f‖ + ‖g‖) :
    ∃ c : ℝ, 0 ≤ c ∧ g = c • f :=
  exists_nonneg_smul_eq_of_norm_add_eq (p := 2) hf0 hg0 h (by norm_num)

-- Uniqueness of a best approximation, in hypothesis form.
example {μ : Measure ℝ} {K : Set (Lp ℝ 2 μ)}
    (hK : Convex ℝ K) {x p₀ q₀ : Lp ℝ 2 μ}
    (hp₀ : p₀ ∈ K) (hq₀ : q₀ ∈ K)
    (hpmin : ∀ y ∈ K, ‖p₀ - x‖ ≤ ‖y - x‖)
    (hqmin : ∀ y ∈ K, ‖q₀ - x‖ ≤ ‖y - x‖) :
    p₀ = q₀ :=
  eq_of_forall_norm_sub_le_of_convex (p := 2) hK hp₀ hq₀ hpmin hqmin (by norm_num)

-- The `StrictConvexSpace` instance fires for real `L²`.
example (μ : Measure ℝ) : StrictConvexSpace ℝ (Lp ℝ 2 μ) :=
  inferInstance

#print axioms norm_convex_comb_lt_of_norm_le_one
#print axioms exists_nonneg_smul_eq_of_norm_add_eq
#print axioms eq_of_forall_norm_sub_le_of_convex

end MathlibExtTest.Analysis.Normed.Lp.StrictConvex
