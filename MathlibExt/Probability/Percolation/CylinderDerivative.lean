/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.CylinderDeriv

/-!
# Russo's formula for the Bernoulli product measure on a finite set

For a finite edge set `E` and an increasing event `A ⊆ {0, 1}^E`, the map
`p ↦ ℙ_p(A)` (probability under the product of Bernoulli(`p`) measures) is differentiable on
`(0, 1)` with derivative `∑_e ℙ_p(e is pivotal for A)`. This file transfers the polynomial form
`StatMech.hasDerivAt_prob_eq_sum_pivotalProb` to the measure `bernoulliProductMeasure`.

## Main definitions

* `StatMech.Percolation.measureProb`: `ℙ_p(A)` as a function of `p ∈ ℝ`, extended outside `[0, 1]`
  by the polynomial `StatMech.prob p A`.

## Main results

* `StatMech.Percolation.russo_derivative`, `StatMech.Percolation.russo_formula`: **Russo's formula**
  `d/dp ℙ_p(A) = ∑_e ℙ_p(e pivotal for A)` for `0 < p < 1`.
* `StatMech.Percolation.russo_derivative_measure`: the same, stated for `p : ℝ≥0` together with the
  identification of `measureProb` with the measure of `A`.

## References

* L. Russo, *On the critical percolation probabilities*, Z. Wahrsch. Verw. Gebiete 56 (1981),
  229–237.
* G. A. Margulis, *Probabilistic characteristics of graphs with large connectivity*, Problemy
  Peredači Informacii 10 (1974), 101–108.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function Filter
open scoped ENNReal NNReal

namespace StatMech

namespace Percolation

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The probability `ℙ_p(A)` of `A` under the Bernoulli(`p`) product measure on `{0, 1}^E` for
`p ∈ [0, 1]`; outside `[0, 1]` it is the polynomial `StatMech.prob p A`, so that the function is
defined on all of `ℝ`. -/
noncomputable def measureProb (A : Set (ConfigSpace E)) (p : ℝ) : ℝ :=
  if h : 0 ≤ p ∧ p ≤ 1 then
    (bernoulliProductMeasure (E := E) ⟨p, h.1⟩ (by exact_mod_cast h.2)).real A
  else prob p A

lemma measureProb_eq_measure_real (A : Set (ConfigSpace E)) (p : ℝ≥0) (hp : p ≤ 1) :
    measureProb A (p : ℝ) = (bernoulliProductMeasure (E := E) p hp).real A := by
  unfold measureProb
  have h0 : (0 : ℝ) ≤ (p : ℝ) := p.2
  have h1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  rw [dite_eq_left ⟨h0, h1⟩]
  congr 1

lemma measureProb_eq_prob (A : Set (ConfigSpace E)) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    measureProb A p = prob p A := by
  unfold measureProb
  rw [dite_eq_left ⟨h0, h1⟩, finiteRealProb_eq_prob (E := E) ⟨p, h0⟩ (by exact_mod_cast h1) A]
  congr 1

lemma measureProb_eventuallyEq_prob (A : Set (ConfigSpace E)) {p : ℝ}
    (h0 : 0 < p) (h1 : p < 1) :
    (fun q => measureProb A q) =ᶠ[nhds p] (fun q => prob q A) := by
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhds p := isOpen_Ioo.mem_nhds ⟨h0, h1⟩
  filter_upwards [hmem] with q hq
  exact measureProb_eq_prob A (le_of_lt hq.1) (le_of_lt hq.2)

/-- **Russo's formula** (Margulis–Russo): for an increasing event `A` on a finite edge set and
`0 < p < 1`, `p ↦ ℙ_p(A)` has derivative `∑_e ℙ_p(e is pivotal for A)` at `p`.
See also `StatMech.hasDerivAt_prob_eq_sum_pivotalProb` (the polynomial form, for all `p`) and
`StatMech.hasDerivAt_realProb_cylinder_pivotal` (cylinder events on an infinite edge set). -/
theorem russo_derivative (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    HasDerivAt (fun p => measureProb A p) (∑ e, pivotalProb p A e) p := by
  rw [(measureProb_eventuallyEq_prob A h0 h1).hasDerivAt_iff]
  exact hasDerivAt_prob_eq_sum_pivotalProb A hA p

/-- **Russo's formula**, `deriv` form: `d/dp ℙ_p(A) = ∑_e ℙ_p(e is pivotal for A)` for an
increasing event `A` and `0 < p < 1`. -/
theorem russo_formula (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    deriv (fun p => measureProb A p) p = ∑ e, pivotalProb p A e :=
  (russo_derivative A hA h0 h1).deriv

/-- Russo's formula for `p : ℝ≥0`, packaged with the identification of `measureProb A p` with
`(bernoulliProductMeasure p hp).real A`. -/
theorem russo_derivative_measure (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (p : ℝ≥0) (hp : p ≤ 1) (h0 : 0 < (p : ℝ)) (h1 : (p : ℝ) < 1) :
    HasDerivAt (fun q => measureProb A q) (∑ e, pivotalProb (p : ℝ) A e) (p : ℝ)
      ∧ measureProb A (p : ℝ) = (bernoulliProductMeasure (E := E) p hp).real A :=
  ⟨russo_derivative A hA h0 h1, measureProb_eq_measure_real A p hp⟩

end Percolation

end StatMech
