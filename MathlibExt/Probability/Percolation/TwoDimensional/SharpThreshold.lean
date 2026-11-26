/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.SharpnessFromInputs
public import MathlibExt.Probability.Percolation.Universality.Defs

/-!
# Subcritical crossing probabilities tend to zero

Bridges between the two encodings of `θ` and `p_c` (`StatMech.Percolation.theta`, `pc` and
`StatMech.Universality.percolationProbability`, `criticalProbability`), and the fact that, below
`p_c`, the one-arm probability `ℙ_p(0 ↔ ∂Λ_n)` tends to `0` and so does the probability of any
event family dominated by a constant times it.

## Main results

* `StatMech.TwoDim.kst_theta_eq_zero_iff`, `StatMech.TwoDim.kst_subcriticalDensities_eq_coe`:
  agreement of the two encodings.
* `StatMech.TwoDim.kst_crossProb_tendsto_zero_of_theta_zero`: `θ(p) = 0` implies
  `ℙ_p(0 ↔ ∂Λ_n) → 0`.
* `StatMech.TwoDim.kst_sharpThreshold_crossingEvent`,
  `StatMech.TwoDim.kst_sharpThreshold_of_dominated`: below `p_c`, one-arm and dominated
  crossing probabilities tend to `0`.

## Implementation notes

The last two results take `hsub : θ(p) = 0` for all `p < p_c` as a hypothesis. It is true (it
follows from monotonicity of `θ` in `p`, by coupling), but monotonicity of `θ` is not yet in the
library. For the left–right crossing of `[0, n]²` an unconditional version, using sharpness
instead, is `StatMech.TwoDim.kcd_horizontal_sharpThreshold`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

/-- `Percolation.theta d p = 0` iff `Universality.percolationProbability d p = 0`. -/
theorem kst_theta_eq_zero_iff (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    Percolation.theta d p hp = 0 ↔ Universality.percolationProbability d p hp = 0 := by
  unfold Percolation.theta Universality.percolationProbability
  rw [Measure.real]
  have he : Universality.percolationEvent d = Percolation.percolationEvent d := rfl
  rw [he]
  constructor
  · intro h
    rw [ENNReal.toReal_eq_zero_iff] at h
    rcases h with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  · intro h; rw [h]; simp

/-- `Universality.subcriticalDensities d` is the image of `Percolation.subcriticalSet d` in `ℝ`. -/
theorem kst_subcriticalDensities_eq_coe (d : ℕ) :
    Universality.subcriticalDensities d
      = NNReal.toReal '' Percolation.subcriticalSet d := by
  ext x
  simp only [Universality.subcriticalDensities, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hx0, hx1, hzero⟩
    refine ⟨⟨x, hx0⟩, ⟨by exact_mod_cast hx1, ?_⟩, rfl⟩
    exact (kst_theta_eq_zero_iff d ⟨x, hx0⟩ _).mpr hzero
  · rintro ⟨p, ⟨hp1, hzero⟩, rfl⟩
    exact ⟨p.coe_nonneg, by exact_mod_cast hp1, (kst_theta_eq_zero_iff d p hp1).mp hzero⟩

/-- If `θ_d(p) = 0`, the one-arm probability `ℙ_p(0 ↔ ∂Λ_n)` tends to `0`. -/
theorem kst_crossProb_tendsto_zero_of_theta_zero (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (h : Percolation.theta d p hp = 0) :
    Tendsto (fun n => Percolation.crossProb d p hp n) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n => Percolation.crossProb d p hp (n + 1)) atTop (𝓝 0) := by
    have := Percolation.tendsto_crossProb_theta (d := d) p hp
    rwa [h] at this
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

/-- Below `p_c`, the one-arm probability tends to `0`, given `hsub` (`θ = 0` below `p_c`; true by
monotonicity of `θ`, which is not yet in the library). -/
theorem kst_sharpThreshold_crossingEvent (d : ℕ)
    (hsub : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < Universality.criticalProbability d →
        Percolation.theta d p hp = 0) :
    ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < Universality.criticalProbability d →
        Tendsto (fun n => (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (Percolation.crossingEvent d n)) atTop (𝓝 0) := by
  intro p hp hlt
  exact kst_crossProb_tendsto_zero_of_theta_zero d p hp (hsub p hp hlt)

/-- Below `p_c`, any event family with `ℙ_p(boxFam n) ≤ C ℙ_p(0 ↔ ∂Λ_n)` has probability tending to
`0`, given `hsub` as in `kst_sharpThreshold_crossingEvent`. -/
theorem kst_sharpThreshold_of_dominated (d : ℕ)
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site d)))} {C : ℝ}
    (hsub : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < Universality.criticalProbability d →
        Percolation.theta d p hp = 0)
    (hdom : ∀ (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ),
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (boxFam n)
          ≤ C * Percolation.crossProb d p hp n) :
    ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < Universality.criticalProbability d →
        Tendsto (fun n => (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (boxFam n)) atTop (𝓝 0) := by
  intro p hp hlt
  have hθ : Percolation.theta d p hp = 0 := hsub p hp hlt
  have hcz : Tendsto (fun n => Percolation.crossProb d p hp n) atTop (𝓝 0) :=
    kst_crossProb_tendsto_zero_of_theta_zero d p hp hθ
  have hub : Tendsto (fun n => C * Percolation.crossProb d p hp n) atTop (𝓝 0) := by
    simpa using hcz.const_mul C
  exact squeeze_zero (fun n => measureReal_nonneg) (fun n => hdom p hp n) hub

end TwoDim

end StatMech
