/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































































import Mathlib
import Code.Universality.Defs
import Code.Percolation.Theta
import Code.Percolation.SubcriticalDecay
import Code.Percolation.Sharpness
import Code.Percolation.PcNontrivial

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation














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






theorem kst_subcriticalDensities_eq_coe (d : ℕ) :
    Universality.subcriticalDensities d
      = NNReal.toReal '' Percolation.subcriticalSet d := by
  ext x
  simp only [Universality.subcriticalDensities, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hx0, hx1, hzero⟩
    refine ⟨⟨x, hx0⟩, ⟨by exact_mod_cast hx1, ?_⟩, rfl⟩
    rw [kst_theta_eq_zero_iff]; exact hzero
  · rintro ⟨p, ⟨hp1, hzero⟩, rfl⟩
    exact ⟨p.coe_nonneg, by exact_mod_cast hp1, (kst_theta_eq_zero_iff d p hp1).mp hzero⟩







theorem kst_criticalProbability_eq_pc (d : ℕ) :
    Universality.criticalProbability d = (Percolation.pc d : ℝ) := by
  unfold Universality.criticalProbability Percolation.pc
  rw [kst_subcriticalDensities_eq_coe, ← NNReal.coe_sSup]













theorem kst_crossProb_tendsto_zero_of_theta_zero (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (h : Percolation.theta d p hp = 0) :
    Tendsto (fun n => Percolation.crossProb d p hp n) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n => Percolation.crossProb d p hp (n + 1)) atTop (𝓝 0) := by
    have := Percolation.tendsto_crossProb_theta (d := d) p hp
    rwa [h] at this
  exact (tendsto_add_atTop_iff_nat 1).mp hshift


















theorem kst_sharpThreshold_crossingEvent (d : ℕ)
    (hsub : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < Universality.criticalProbability d →
        Percolation.theta d p hp = 0) :
    ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < Universality.criticalProbability d →
        Tendsto (fun n => (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (Percolation.crossingEvent d n)) atTop (𝓝 0) := by
  intro p hp hlt
  exact kst_crossProb_tendsto_zero_of_theta_zero d p hp (hsub p hp hlt)




















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
