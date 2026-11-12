/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Theta
public import PhyslibExt.CondensedMatter.IsingModel.InfiniteVolume

/-!
# Spontaneous magnetization and the critical inverse temperature

The magnetization of the plus state of the Ising model on ℤ^d and the critical point `β_c` it
defines.

## i. Overview

The magnetization `m*(β) = ⟨σ_0⟩⁺_β` is the expected origin spin under the plus state `plusState d β
0` at zero field; it lies in `[-1, 1]`. The critical inverse temperature is `β_c(d) = inf {β ≥ 0 |
m*(β) > 0}`.

Note: `plusState d β 0` is a weak subsequential limit of the plus-boundary box measures chosen by
`limitState`, and `sInf ∅ = 0` in `ℝ`, so `betaC d = 0` when no `β` has positive magnetization.

## ii. Key results

- `StatMech.Ising.magnetization` : the spontaneous magnetization `⟨σ_0⟩⁺_β`
- `StatMech.Ising.abs_magnetization_le_one` : `|m*(β)| ≤ 1`
- `StatMech.Ising.betaC` : the critical inverse temperature

## iii. Table of contents

- A. Spin observables
- B. The magnetization
- C. The critical inverse temperature

## iv. References

- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems: A Concrete Mathematical
  Introduction*, Cambridge University Press (2017), Chapter 3
- H. Duminil-Copin, *Lectures on the Ising and Potts models on the hypercubic lattice*, PIMS–CRM
  Summer School in Probability (2017), arXiv:1707.00520
-/

@[expose] public section

open MeasureTheory

namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}

/-! ## A. Spin observables -/

/-- The spin at a site is a measurable function of the configuration. -/
lemma measurable_spin (x : Site d) :
    Measurable (fun ω : ConfigSpace (Site d) => spin ω x) := by
  have hmeas : Measurable (fun ω : ConfigSpace (Site d) => ω x) := measurable_pi_apply x
  simp only [spin]
  exact Measurable.ite (hmeas (measurableSet_singleton true)) measurable_const measurable_const

/-- The spin at a site is integrable for every finite measure. -/
lemma integrable_spin (x : Site d) (μ : Measure (ConfigSpace (Site d)))
    [IsFiniteMeasure μ] :
    Integrable (fun ω : ConfigSpace (Site d) => spin ω x) μ := by
  refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const 1)
    (measurable_spin x).aestronglyMeasurable ?_
  filter_upwards with ω
  simpa using abs_spin_le_one ω x

/-! ## B. The magnetization -/

/-- The spontaneous magnetization `m*(β) = ⟨σ_0⟩⁺_β`: the expected spin at the origin under the
zero-field plus state. -/
noncomputable def magnetization (d : ℕ) (β : ℝ) : ℝ :=
  ∫ ω, spin ω (origin d) ∂(plusState d β 0 : Measure (ConfigSpace (Site d)))

lemma abs_magnetization_le_one (d : ℕ) (β : ℝ) : |magnetization d β| ≤ 1 := by
  rw [magnetization, ← Real.norm_eq_abs]
  have : IsProbabilityMeasure (plusState d β 0 : Measure (ConfigSpace (Site d))) :=
    (plusState d β 0).2
  calc ‖∫ ω, spin ω (origin d) ∂(plusState d β 0 : Measure (ConfigSpace (Site d)))‖
      ≤ 1 * (plusState d β 0 : Measure (ConfigSpace (Site d))).real Set.univ := by
        refine norm_integral_le_of_norm_le_const ?_
        filter_upwards with ω
        simpa using abs_spin_le_one ω (origin d)
    _ = 1 := by simp

lemma magnetization_le_one (d : ℕ) (β : ℝ) : magnetization d β ≤ 1 :=
  (abs_le.mp (abs_magnetization_le_one d β)).2

lemma neg_one_le_magnetization (d : ℕ) (β : ℝ) : -1 ≤ magnetization d β :=
  (abs_le.mp (abs_magnetization_le_one d β)).1

/-! ## C. The critical inverse temperature -/

/-- The set of inverse temperatures `β ≥ 0` at which the spontaneous magnetization is positive. -/
def positiveMagnetizationSet (d : ℕ) : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ 0 < magnetization d β}

@[simp]
lemma mem_positiveMagnetizationSet {d : ℕ} {β : ℝ} :
    β ∈ positiveMagnetizationSet d ↔ 0 ≤ β ∧ 0 < magnetization d β :=
  Iff.rfl

/-- The critical inverse temperature `β_c(d) = inf {β ≥ 0 | m*(β) > 0}` (equal to `0` if the set is
empty, by the convention `sInf ∅ = 0`). -/
noncomputable def betaC (d : ℕ) : ℝ :=
  sInf (positiveMagnetizationSet d)

end Ising

end StatMech
