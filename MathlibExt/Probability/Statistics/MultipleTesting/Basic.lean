/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.HasLaw

/-!
# Multiple testing: p-values, counts below a threshold, false discoveries

Common vocabulary for the multiple-testing procedures in this directory. A family of `m`
hypotheses is tested through p-values `p : Fin m → Ω → ℝ` on a probability space `(Ω, μ)`;
`H0 : Finset (Fin m)` is the (unknown) set of true null hypotheses. A procedure maps the
observed p-values `fun i => p i ω` to a rejection set `R : Finset (Fin m)`.

* `IsValidPValue μ X`: the p-value `X` is *valid* (super-uniform) under `μ`:
  `μ {X ≤ t} ≤ t` for every `t ∈ [0, 1]`. A p-value uniform on `[0, 1]` is valid
  (`isValidPValue_of_hasLaw_uniform`); valid p-values arise from discrete tests.
* `numBelow p t`: the number of p-values that are at most `t`. For the order statistics
  `p₍₁₎ ≤ ⋯ ≤ p₍ₘ₎` and `1 ≤ k ≤ m`, `p₍ₖ₎ ≤ t ↔ k ≤ numBelow p t` (with ties counted with
  multiplicity), which lets step-up and step-down procedures be stated without sorting.
* `falseDiscoveryProportion H0 R = |R ∩ H0| / max |R| 1`.

A rejection set `R` commits a *family-wise error* when `R ∩ H0` is nonempty; the family-wise
error rate (FWER) is the probability of this event.

## Main results

* `isValidPValue_of_hasLaw_uniform`: a p-value with law `Uniform[0, 1]` is valid.
* `falseDiscoveryProportion_nonneg`, `falseDiscoveryProportion_le_one`.

## References

* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  §3.3 (p-values) and §9.1 (multiple testing).
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

/-- A real random variable `X` is a *valid* (super-uniform) p-value under `μ` if
`μ {X ≤ t} ≤ t` for every level `t ∈ [0, 1]`. Uniform p-values are the equality case. -/
def IsValidPValue (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, μ {ω | X ω ≤ t} ≤ ENNReal.ofReal t

/-- A p-value distributed uniformly on `[0, 1]` is valid. -/
theorem isValidPValue_of_hasLaw_uniform {μ : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) : IsValidPValue μ X := by
  intro t ht
  have h : μ {ω | X ω ≤ t} = volume.restrict (Set.Icc (0 : ℝ) 1) (Set.Iic t) := by
    rw [← hX.map_eq, Measure.map_apply_of_aemeasurable hX.aemeasurable measurableSet_Iic]
    rfl
  rw [h, Measure.restrict_apply measurableSet_Iic]
  calc volume (Set.Iic t ∩ Set.Icc 0 1) ≤ volume (Set.Icc 0 t) :=
        measure_mono fun x hx => ⟨hx.2.1, hx.1⟩
    _ = ENNReal.ofReal t := by simp

/-- The number of p-values that are at most `t`. -/
noncomputable def numBelow (p : Fin m → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun i => p i ≤ t).card

/-- At most `m` p-values lie below any threshold. -/
theorem numBelow_le (p : Fin m → ℝ) (t : ℝ) : numBelow p t ≤ m := by
  simpa [numBelow] using Finset.card_filter_le Finset.univ fun i => p i ≤ t

/-- `numBelow p` is monotone in the threshold. -/
theorem numBelow_mono (p : Fin m → ℝ) {s t : ℝ} (hst : s ≤ t) : numBelow p s ≤ numBelow p t :=
  Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans hst

/-- The false discovery proportion of a rejection set `R` when `H0` is the set of true nulls:
`|R ∩ H0| / max |R| 1` (zero when nothing is rejected). -/
noncomputable def falseDiscoveryProportion (H0 R : Finset (Fin m)) : ℝ :=
  ((R ∩ H0).card : ℝ) / max (R.card : ℝ) 1

/-- The false discovery proportion is nonnegative. -/
theorem falseDiscoveryProportion_nonneg (H0 R : Finset (Fin m)) :
    0 ≤ falseDiscoveryProportion H0 R := by
  unfold falseDiscoveryProportion
  positivity

/-- The false discovery proportion is at most one. -/
theorem falseDiscoveryProportion_le_one (H0 R : Finset (Fin m)) :
    falseDiscoveryProportion H0 R ≤ 1 := by
  unfold falseDiscoveryProportion
  rw [div_le_one (by positivity)]
  exact le_max_of_le_left (by exact_mod_cast Finset.card_le_card Finset.inter_subset_left)

end MathlibExt.Probability.Statistics.MultipleTesting
