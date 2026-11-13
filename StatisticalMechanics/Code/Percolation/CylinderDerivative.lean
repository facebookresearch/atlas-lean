/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































import Code.Foundations.CylinderDeriv

open MeasureTheory ProbabilityTheory Function Filter
open scoped ENNReal NNReal

namespace StatMech

namespace Percolation

variable {E : Type*} [Fintype E] [DecidableEq E]
















noncomputable def measureProb (A : Set (ConfigSpace E)) (p : ℝ) : ℝ :=
  if h : 0 ≤ p ∧ p ≤ 1 then
    (bernoulliProductMeasure (E := E) ⟨p, h.1⟩ (by exact_mod_cast h.2)).real A
  else prob p A






lemma measureProb_eq_measure_real (A : Set (ConfigSpace E)) (p : ℝ≥0) (hp : p ≤ 1) :
    measureProb A (p : ℝ) = (bernoulliProductMeasure (E := E) p hp).real A := by
  unfold measureProb
  have h0 : (0 : ℝ) ≤ (p : ℝ) := p.2
  have h1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  rw [dif_pos ⟨h0, h1⟩]
  congr 1




lemma measureProb_eq_prob (A : Set (ConfigSpace E)) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    measureProb A p = prob p A := by
  unfold measureProb
  rw [dif_pos ⟨h0, h1⟩, finiteRealProb_eq_prob (E := E) ⟨p, h0⟩ (by exact_mod_cast h1) A]
  congr 1





lemma measureProb_eventuallyEq_prob (A : Set (ConfigSpace E)) {p : ℝ}
    (h0 : 0 < p) (h1 : p < 1) :
    (fun q => measureProb A q) =ᶠ[nhds p] (fun q => prob q A) := by
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhds p := isOpen_Ioo.mem_nhds ⟨h0, h1⟩
  filter_upwards [hmem] with q hq
  exact measureProb_eq_prob A (le_of_lt hq.1) (le_of_lt hq.2)

















theorem russo_derivative (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    HasDerivAt (fun p => measureProb A p) (∑ e, pivotalProb p A e) p := by
  rw [(measureProb_eventuallyEq_prob A h0 h1).hasDerivAt_iff]
  exact hasDerivAt_prob_eq_sum_pivotalProb A hA p








theorem russo_formula (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    deriv (fun p => measureProb A p) p = ∑ e, pivotalProb p A e :=
  (russo_derivative A hA h0 h1).deriv















theorem russo_derivative_measure (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (p : ℝ≥0) (hp : p ≤ 1) (h0 : 0 < (p : ℝ)) (h1 : (p : ℝ) < 1) :
    HasDerivAt (fun q => measureProb A q) (∑ e, pivotalProb (p : ℝ) A e) (p : ℝ)
      ∧ measureProb A (p : ℝ) = (bernoulliProductMeasure (E := E) p hp).real A :=
  ⟨russo_derivative A hA h0 h1, measureProb_eq_measure_real A p hp⟩

end Percolation

end StatMech
