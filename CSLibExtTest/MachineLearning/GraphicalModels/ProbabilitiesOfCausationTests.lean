/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.ProbabilitiesOfCausation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for probabilities of causation

The example of Tian and Pearl, Section 5 (Table 2), beyond the computations in the production
module: the rest of the observational law, uniqueness of the monotone law with these data, PN and
PS of the non-monotone law, and non-identification of PNS without monotonicity; the
eight-parameter laws of the constant- and switching-response models; the causal effects of
`orModel`; and controls showing that the hypotheses of `max_le_pns` and `isLeast_pns_expFiber` are
needed and that a wrong value of PNS is rejected.
-/

@[expose] public section

namespace Cslib.MachineLearning.ProbabilitiesOfCausationTests

open Cslib.MachineLearning.GraphicalModels
open Cslib.MachineLearning.GraphicalModels.ProbabilitiesOfCausation
open Cslib.MachineLearning.GraphicalModels.CrossWorld

private theorem poc_aux_or_solve0 (u : Fin 2 → Bool) : orModel.solve u 0 = u 0 := by
  rfl

private theorem poc_aux_or_solve1 (u : Fin 2 → Bool) : orModel.solve u 1 = (u 0 || u 1) := by
  rfl

private theorem poc_aux_or_cf_true (u : Fin 2 → Bool) : orModel.counterfactual 0 true u 1 = true := by
  rfl

private theorem poc_aux_or_cf_false (u : Fin 2 → Bool) : orModel.counterfactual 0 false u 1 = u 1 := by
  rfl

private theorem poc_aux_or_support (k : Fin 2) : (orNoise k).weights.support = Finset.univ := by
  ext b
  cases b <;> simp [orNoise, Finsupp.mem_support_iff, InterveningVsConditioning.coin_true,
    InterveningVsConditioning.coin_false]; norm_num

private theorem poc_aux_or_piFinset :
    Fintype.piFinset (fun j => (orNoise j).weights.support) = Finset.univ := by
  ext u
  simp [Fintype.mem_piFinset, poc_aux_or_support]

private theorem poc_aux_or_weight (u : Fin 2 → Bool) : FiniteSCM.noiseWeight orNoise u = 1 / 4 := by
  simp [FiniteSCM.noiseWeight, orNoise]
  cases h0 : u 0 <;> cases h1 : u 1 <;>
    simp [InterveningVsConditioning.coin_true,
      InterveningVsConditioning.coin_false] <;> norm_num

private theorem poc_aux_or_cfLaw (i j k : Bool) :
    orModel.cfLaw orNoise 0 1 i j k = if i then (1 / 4 : ℝ) else 0 := by
  simp only [FiniteSCM.cfLaw, poc_aux_or_cf_true, poc_aux_or_cf_false, poc_aux_or_solve0,
    poc_aux_or_weight, poc_aux_or_piFinset]
  cases i
  · have hempty : Finset.filter (fun u : Fin 2 → Bool => true = false ∧ u 1 = j ∧ u 0 = k)
        Finset.univ = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro u _
      simp
    rw [hempty, Finset.sum_empty]
    simp
  · simp only [true_and]
    have hset : Finset.filter (fun u : Fin 2 → Bool => u 1 = j ∧ u 0 = k) Finset.univ =
        {fun m => if m = 0 then k else j} := by
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        have h0 : u 0 = (fun m => if m = 0 then k else j) 0 := by simp [h.2]
        have h1 : u 1 = (fun m => if m = 0 then k else j) 1 := by simp [h.1]
        have hall : ∀ m : Fin 2, u m = (fun m => if m = 0 then k else j) m :=
          Fin.forall_fin_two.2 ⟨h0, h1⟩
        exact funext hall
      · intro h
        subst h
        simp [h10]
    rw [hset, Finset.sum_singleton]
    simp

/-- Table 2, nonexperimental data (p. 26): `P(x, y') = 998/2000`, `P(x', y) = 28/2000` and
`P(y) = 30/2000`. -/
example : pxy section5Monotone true false = 998 / 2000 ∧
    pxy section5Monotone false true = 28 / 2000 ∧ py section5Monotone = 30 / 2000 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [pxy, py, section5Monotone] <;> norm_num

/-- `section5Monotone` is the only monotone law with the data of Table 2: its observational law
and the causal effects `P(y_x) = 16/1000` and `P(y_{x'}) = 14/1000`. -/
example (p : CfLaw) (hm : IsMonotone p) (hxy : ∀ x y, pxy p x y = pxy section5Monotone x y)
    (h1 : pyx p = 16 / 1000) (h0 : pyx' p = 14 / 1000) : p = section5Monotone := by
  have m1 : p false true true = 0 := hm true
  have m2 : p false true false = 0 := hm false
  have e1 := hxy true true
  have e2 := hxy true false
  have e3 := hxy false true
  have e4 := hxy false false
  simp [pxy, section5Monotone] at e1 e2 e3 e4
  norm_num at e1 e2 e3 e4
  simp [pyx] at h1
  simp [pyx'] at h0
  funext i j k
  cases i <;> cases j <;> cases k <;> simp [section5Monotone] <;> linarith

/-- The non-monotone law with the data of Table 2: `PN = 1` and `PS = 5/162`, the upper bound of
eq. (60) (printed `0.031`). -/
example : pn section5Upper = 1 ∧ ps section5Upper = 5 / 162 := by
  constructor <;> simp [pn, ps, pxy, section5Upper]; norm_num

/-- `section5Upper` is not monotone: `p₀₁₀ = 14/1000`. -/
example : ¬ IsMonotone section5Upper := by
  intro h
  have h2 := h false
  simp [section5Upper] at h2

/-- Without monotonicity Table 2 does not identify PNS: the two laws share its experimental and
nonexperimental data and have PNS `1/500` and `2/125`. -/
example : pns section5Monotone ≠ pns section5Upper := by
  simp [pns, section5Monotone, section5Upper]
  norm_num

/-- The constant-response model: `P(y_x) = P(y_{x'}) = 1/2` and PNS `0`, the lower bound of
eq. (23) (`probY1Y0_constantResponse`). -/
example : pyx constantResponse.cfLaw = 1 / 2 ∧ pyx' constantResponse.cfLaw = 1 / 2 ∧
    pns constantResponse.cfLaw = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [pyx, pyx', pns, BinarySCM.cfLaw, constantResponse, Fintype.sum_prod_type] <;> norm_num

/-- The switching-response model: `P(y_x) = P(y_{x'}) = 1/2` and PNS `1/2`, the upper bound of
eq. (23) (`probY1Y0_switchingResponse`). -/
example : pyx switchingResponse.cfLaw = 1 / 2 ∧ pyx' switchingResponse.cfLaw = 1 / 2 ∧
    pns switchingResponse.cfLaw = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [pyx, pyx', pns, BinarySCM.cfLaw, switchingResponse, Fintype.sum_prod_type] <;> norm_num

/-- `orModel`: `Y_x = 1` in every unit and `Y_{x'} = U₁`, so `P(y_x) = 1` and
`P(y_{x'}) = 1/2`. -/
example : pyx (orModel.cfLaw orNoise 0 1) = 1 ∧ pyx' (orModel.cfLaw orNoise 0 1) = 1 / 2 := by
  constructor <;> simp [pyx, pyx', poc_aux_or_cfLaw] <;> norm_num

/-- Control: `max_le_pns` needs nonnegative weights. With `p₀₁₀ = -1` and every other weight `0`,
PNS is `0` while `max 0 (P(y_x) - P(y_{x'})) = 1`. -/
example :
    let p : CfLaw := fun i j k => if (i, j, k) = (false, true, false) then -1 else 0
    pns p = 0 ∧ max 0 (pyx p - pyx' p) = 1 := by
  refine ⟨?_, ?_⟩ <;> simp [pns, pyx, pyx']

/-- Control: `isLeast_pns_expFiber` needs `a ≤ 1`; for `a = 2` the fiber is empty. -/
example (b : ℝ) : expFiber 2 b = ∅ := by
  ext p
  simp only [expFiber, IsCfLaw, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
  constructor
  · rintro ⟨⟨h0, h1⟩, hpyx, -⟩
    simp only [pyx] at hpyx
    have hR : 0 ≤ ∑ j, ∑ k, p false j k :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => h0 false j k
    have htot : (∑ i, ∑ j, ∑ k, p i j k) = (∑ j, ∑ k, p true j k) + ∑ j, ∑ k, p false j k := by
      simp
    linarith
  · intro h
    cases h

/-- Control: a wrong value of PNS at Table 2 is rejected. -/
example : pns section5Monotone ≠ 3 / 1000 := by
  simp [pns, section5Monotone]
  norm_num

end Cslib.MachineLearning.ProbabilitiesOfCausationTests
