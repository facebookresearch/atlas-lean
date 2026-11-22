/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.Russo

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.Russo`

On `ConfigSpace (Fin 2)` with the increasing event `open0 = {ω | ω 0}`:
* `configWeight`, `prob` and `pivotalProb` are computed: `prob p open0 = p`,
  `pivotalProb p open0 0 = 1`, `pivotalProb p open0 1 = 0` (coordinate `0` is always pivotal,
  coordinate `1` never), using `IsPivotal` directly;
* Russo's formula `hasDerivAt_prob_eq_sum_pivotalProb` is applied (with `IsIncreasing open0`
  proved) and, compared with the derivative of `p ↦ p`, yields `∑ e, pivotalProb p open0 e = 1`;
* `deriv_prob_eq_sum_pivotalProb` is evaluated to `deriv (fun p => prob p open0) p = 1`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.Russo

open _root_.StatMech

/-- The event "coordinate `0` is open" on two coordinates. -/
def open0 : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

-- `open0` is increasing.
theorem isIncreasing_open0 : IsIncreasing open0 := by
  intro x y hxy hx
  have h := hxy 0
  simp only [open0, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

/-- A sum over `ConfigSpace (Fin 2)` is a sum over the four configurations. -/
theorem sum_config_fin2 (f : ConfigSpace (Fin 2) → ℝ) :
    ∑ ω, f ω = f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp [finTwoArrowEquiv_symm_apply]
  ring

-- `configWeight` of the all-open configuration is `p^2`.
example (p : ℝ) : configWeight p (fun _ : Fin 2 => true) = p ^ 2 := by
  simp [configWeight, edgeWeight, sq]

-- `prob p open0 = p`.
theorem prob_open0 (p : ℝ) : prob p open0 = p := by
  rw [prob, sum_config_fin2]
  simp [configWeight, edgeWeight, open0, Set.indicator, Fin.prod_univ_two]
  ring

-- Coordinate `0` is pivotal for `open0` at every configuration.
theorem isPivotal_zero (ω : ConfigSpace (Fin 2)) : IsPivotal 0 open0 ω := by
  simp [IsPivotal, setOpen, setClosed, open0]

-- Coordinate `1` is never pivotal for `open0`.
theorem not_isPivotal_one (ω : ConfigSpace (Fin 2)) : ¬ IsPivotal 1 open0 ω := by
  simp [IsPivotal, setOpen, setClosed, open0]

-- `pivotalProb p open0 0 = 1`.
theorem pivotalProb_zero (p : ℝ) : pivotalProb p open0 0 = 1 := by
  have h : {ω | IsPivotal 0 open0 ω} = Set.univ := Set.eq_univ_of_forall isPivotal_zero
  rw [pivotalProb, h, sum_config_fin2]
  simp [configWeight, edgeWeight, Fin.prod_univ_two]
  ring

-- `pivotalProb p open0 1 = 0`.
theorem pivotalProb_one (p : ℝ) : pivotalProb p open0 1 = 0 := by
  have h : {ω | IsPivotal 1 open0 ω} = ∅ := Set.eq_empty_of_forall_notMem not_isPivotal_one
  simp [pivotalProb, h]

-- Russo's formula applied, then compared with `d/dp p = 1`: the pivotal masses sum to `1`.
example (p : ℝ) : ∑ e, pivotalProb p open0 e = 1 := by
  have hR := hasDerivAt_prob_eq_sum_pivotalProb open0 isIncreasing_open0 p
  have hid : HasDerivAt (fun p => prob p open0) 1 p := by
    have h : (fun p => prob p open0) = fun p => p := funext prob_open0
    rw [h]
    exact hasDerivAt_id' p
  exact hR.unique hid

-- The same conclusion from the explicit values of `pivotalProb`.
example (p : ℝ) : ∑ e, pivotalProb p open0 e = 1 := by
  rw [Fin.sum_univ_two, pivotalProb_zero, pivotalProb_one, add_zero]

-- `deriv_prob_eq_sum_pivotalProb` evaluated at `open0`.
example (p : ℝ) : deriv (fun p => prob p open0) p = 1 := by
  rw [deriv_prob_eq_sum_pivotalProb open0 isIncreasing_open0, Fin.sum_univ_two,
    pivotalProb_zero, pivotalProb_one, add_zero]

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.Russo
