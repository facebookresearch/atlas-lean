/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CrossWorldCounterfactual
public import CSLibExt.MachineLearning.GraphicalModels.StructuralCausalModels
public import CSLibExt.MachineLearning.GraphicalModels.InterveningVsConditioning
import MathlibExt.Analysis.Convex.StdSimplexWeights
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Probabilities of causation: bounds and identification

For a binary cause `X` and a binary effect `Y` (`x`, `y` stand for `X = true`, `Y = true`, and
`x'`, `y'` for their complements), Tian and Pearl define the probability of necessity
`PN = P(y'_{x'} | x, y)` (Definition 7, p. 9, eq. (10)), the probability of sufficiency
`PS = P(y_x | y', x')` (Definition 8, p. 10, eq. (11)) and the probability of necessity and
sufficiency `PNS = P(y_x, y'_{x'})` (Definition 9, p. 10, eq. (12)). Every causal model induces a
law on `(Y_x, Y_{x'}, X)`, and since `Y = Y_X` (consistency, eq. (4), p. 7, in the binary form
eq. (14), p. 11) the three are functions of its eight parameters
`p i j k = P(Y_x = i, Y_{x'} = j, X = k)` (Section 4.1, pp. 13-14, eqs. (15)-(20)).

The results are stated for such laws (`CfLaw`) and transferred to two model classes: the two-node
`CrossWorld.BinarySCM`, whose cross-world probability `probY1Y0` is PNS, and the finite recursive
`FiniteSCM` with a treatment node `t` and an outcome node `o`, for which this file adds the joint
probability of two intervened worlds at the same noise value
(`FiniteSCM.jointCounterfactualProb`). Every law is induced by a model of each class
(`exists_binarySCM_cfLaw`, `exists_finiteSCM_cfLaw`), so the bounds are sharp for both.

## Main definitions

* `CfLaw`, `IsCfLaw`: the eight parameters and constraint (15).
* `pyx`, `pyx'`, `pnyx'`: the causal effects `P(y_x)`, `P(y_{x'})` (eq. (17)) and `P(y'_{x'})`;
  `pxy`, `py`: the observational probabilities `P(X = x, Y = y)` (eq. (16)) and `P(y)`.
* `pns`, `pn`, `ps`: PNS, PN and PS (eqs. (18)-(20)).
* `IsMonotone`: monotonicity in the form of eq. (38) (p. 18).
* `expFiber a b`: the laws with causal effects `P(y_x) = a` and `P(y_{x'}) = b`.
* `CrossWorld.BinarySCM.cfLaw`, `FiniteSCM.cfLaw`: the law that a model induces;
  `CrossWorld.BinarySCM.IsMonotone`, `FiniteSCM.IsMonotone`: Definition 13 (p. 18, eq. (37)) in
  every unit.
* `FiniteSCM.jointCounterfactualProb`: the two-world joint `P(X_{k ← a} ∈ F, X_{k ← a'} ∈ F')`.

## Main results

* `max_le_pns`, `pns_le_min`: the experimental bounds of Section 4.2.2 (p. 15, eq. (23)),
  `max[0, P(y_x) - P(y_{x'})] ≤ PNS ≤ min[P(y_x), P(y'_{x'})]`; `isLeast_pns_expFiber`,
  `isGreatest_pns_expFiber`: both bounds are attained for all causal effects in `[0, 1]`.
* `pns_eq_of_isMonotone`, `pn_eq_of_isMonotone`, `ps_eq_of_isMonotone`: identification under
  monotonicity (Section 4.4.2, p. 19; Theorem 3, p. 20, eqs. (40)-(42)); `pns_eq_sub_iff`: for
  nonnegative weights the lower bound of eq. (23) is PNS exactly under monotonicity.
* `pns_eq_pxy_mul_pn_add`: Lemma 1 (p. 11, eq. (13)).
* `CrossWorld.BinarySCM.max_le_probY1Y0`, `CrossWorld.BinarySCM.probY1Y0_le_min`,
  `CrossWorld.BinarySCM.probY1Y0_eq_of_isMonotone`, `FiniteSCM.max_le_jointCounterfactualProb`,
  `FiniteSCM.jointCounterfactualProb_le_min`, `FiniteSCM.jointCounterfactualProb_eq_of_isMonotone`:
  eqs. (23) and (40) for the two model classes.
* `section5SCM_tight`: the example of Section 5 (pp. 25-27, Table 2, eqs. (58)-(63)) without
  prevention, a binary SCM whose PNS `1/500` (printed `0.002`, eq. (61)) is the lower bound of
  eq. (23); `orModel_tight`: a Markovian finite SCM attaining the lower bound.

## Implementation notes

* PN and PS are conditional probabilities, meaningful only when `P(x, y) > 0`, resp.
  `P(x', y') > 0`. They are defined with Lean's totalized division (`x / 0 = 0`), as
  `FiniteSCM.counterfactualProb` is, so they are `0` when the conditioning event has probability
  zero; with this convention Lemma 1 and eqs. (41)-(42) need no positivity hypothesis.
* Eq. (23) is stated with `P(y'_{x'})` as printed; on a law it is `1 - P(y_{x'})`.
* Monotonicity is per unit for models (Definition 13) and the weight-zero condition (38) for laws;
  the first implies the second, and identification needs only the second.
* Experimental data give no constraints on PN and PS (p. 15); the bounds from combined
  experimental and nonexperimental data, eqs. (24)-(26), are not stated here.

## References

* J. Tian and J. Pearl, *Probabilities of causation: bounds and identification*, Annals of
  Mathematics and Artificial Intelligence 28 (2000), 287-313. Page and equation numbers refer to
  the UCLA technical report R-271-A (February 2000),
  <https://ftp.cs.ucla.edu/pub/stat_ser/R271-A.pdf>.
-/

@[expose] public section

open Finset Convexity

namespace Cslib.MachineLearning.GraphicalModels.ProbabilitiesOfCausation

/-! ### The eight-parameter law -/

/-- The parameters of Tian and Pearl, Section 4.1 (p. 13): `p i j k = P(Y_x = i, Y_{x'} = j,
X = k)`, with `x = true`, `x' = false` and `1 = true` (the source's `p_{ijk}`). They are raw real
weights; `IsCfLaw p` says that they form a probability law. -/
abbrev CfLaw := Bool → Bool → Bool → ℝ

/-- Constraint (15): the eight parameters are nonnegative and sum to `1`. -/
def IsCfLaw (p : CfLaw) : Prop := (∀ i j k, 0 ≤ p i j k) ∧ ∑ i, ∑ j, ∑ k, p i j k = 1

/-- The causal effect `P(y_x)`, eq. (17): the weight of `Y_x = true`. -/
noncomputable def pyx (p : CfLaw) : ℝ := ∑ j, ∑ k, p true j k

/-- The causal effect `P(y_{x'})`, eq. (17): the weight of `Y_{x'} = true`. -/
noncomputable def pyx' (p : CfLaw) : ℝ := ∑ i, ∑ k, p i true k

/-- `P(y'_{x'})`: the weight of `Y_{x'} = false`, the upper-bound term of eq. (23) as printed (on
a law, `1 - P(y_{x'})`). -/
noncomputable def pnyx' (p : CfLaw) : ℝ := ∑ i, ∑ k, p i false k

/-- `P(X = x, Y = y)`, eq. (16): by consistency `Y = Y_X` (eq. (14)), the factual outcome is `Y_x`
when `X = x` and `Y_{x'}` when `X = x'`. -/
noncomputable def pxy (p : CfLaw) (x y : Bool) : ℝ :=
  if x then ∑ j, p y j true else ∑ i, p i y false

/-- `P(y) = P(x, y) + P(x', y)`. -/
noncomputable def py (p : CfLaw) : ℝ := pxy p true true + pxy p false true

/-- PNS `= P(y_x, y'_{x'})`, Definition 9 (p. 10, eq. (12)): the weight `p₁₀₁ + p₁₀₀` of
eq. (18). -/
noncomputable def pns (p : CfLaw) : ℝ := ∑ k, p true false k

/-- PN `= P(y'_{x'} | x, y)`, Definition 7 (p. 9, eq. (10)), as `p₁₀₁ / P(x, y)` (eq. (19)). It
is a conditional probability only when `P(x, y) > 0`; when `P(x, y) = 0` it is `0` by Lean's
totalized division (`x / 0 = 0`). -/
noncomputable def pn (p : CfLaw) : ℝ := p true false true / pxy p true true

/-- PS `= P(y_x | y', x')`, Definition 8 (p. 10, eq. (11)), as `p₁₀₀ / P(x', y')` (eq. (20)). It
is a conditional probability only when `P(x', y') > 0`; when `P(x', y') = 0` it is `0` by Lean's
totalized division (`x / 0 = 0`). -/
noncomputable def ps (p : CfLaw) : ℝ := p true false false / pxy p false false

/-- Monotonicity in the form of eq. (38) (p. 18): `p₀₁₁ = p₀₁₀ = 0`, no weight on
`Y_x = false ∧ Y_{x'} = true`. -/
def IsMonotone (p : CfLaw) : Prop := ∀ k, p false true k = 0

/-- The feasible set of the linear program of Section 4.2.2 (p. 15): the laws (constraint (15))
with causal effects `P(y_x) = a` and `P(y_{x'}) = b` (constraint (17)). -/
def expFiber (a b : ℝ) : Set CfLaw := {p | IsCfLaw p ∧ pyx p = a ∧ pyx' p = b}

/-- Lemma 1 (p. 11, eq. (13)): `PNS = P(x, y) PN + P(x', y') PS`. For nonnegative weights no
positivity hypothesis is needed: a zero denominator forces its numerator to `0`. -/
theorem pns_eq_pxy_mul_pn_add (p : CfLaw) (hp : ∀ i j k, 0 ≤ p i j k) :
    pns p = pxy p true true * pn p + pxy p false false * ps p := by
  unfold pns pn ps pxy
  simp
  have e1 : (p true true true + p true false true) *
      (p true false true / (p true true true + p true false true)) = p true false true := by
    by_cases h : p true true true + p true false true = 0
    · have h3 : p true false true = 0 := by
        have g1 := hp true true true
        have g3 := hp true false true
        linarith
      simp [h3]
    · rw [← mul_div_assoc, mul_div_cancel_left₀ _ h]
  have e2 : (p true false false + p false false false) *
      (p true false false / (p true false false + p false false false)) = p true false false := by
    by_cases h : p true false false + p false false false = 0
    · have h4 : p true false false = 0 := by
        have g4 := hp true false false
        have g8 := hp false false false
        linarith
      simp [h4]
    · rw [← mul_div_assoc, mul_div_cancel_left₀ _ h]
  rw [e1, e2]

/-- Eq. (23), lower bound (Section 4.2.2, p. 15): `max[0, P(y_x) - P(y_{x'})] ≤ PNS` for
nonnegative weights. -/
theorem max_le_pns (p : CfLaw) (hp : ∀ i j k, 0 ≤ p i j k) :
    max 0 (pyx p - pyx' p) ≤ pns p := by
  apply max_le
  · unfold pns
    simp
    exact add_nonneg (hp _ _ _) (hp _ _ _)
  · unfold pyx pyx' pns
    simp
    have h5 := hp false true true
    have h6 := hp false true false
    linarith

/-- Eq. (23), upper bound: `PNS ≤ min[P(y_x), P(y'_{x'})]` for nonnegative weights, with
`P(y'_{x'})` as printed. -/
theorem pns_le_min (p : CfLaw) (hp : ∀ i j k, 0 ≤ p i j k) :
    pns p ≤ min (pyx p) (pnyx' p) := by
  apply le_min
  · unfold pns pyx
    simp
    have h1 := hp true true true
    have h2 := hp true true false
    linarith
  · unfold pns pnyx'
    simp
    have h7 := hp false false true
    have h8 := hp false false false
    linarith

/-- Section 4.4.2 (p. 19) and Theorem 3, eq. (40) (p. 20): under monotonicity
`PNS = P(y_x) - P(y_{x'})`. -/
theorem pns_eq_of_isMonotone (p : CfLaw) (hm : IsMonotone p) : pns p = pyx p - pyx' p := by
  have h5 := hm true
  have h6 := hm false
  unfold pns pyx pyx'
  simp [h5, h6]

/-- Theorem 3, eq. (41): under monotonicity `PN = [P(y) - P(y_{x'})] / P(x, y)`, both sides with
totalized division. This duplicates, at the level of the law, `SCM.cfProb_necessity`
(`StructuralCausalModel.lean`; Pearl, *Statistics Surveys* 2009, Theorem 3), which proves the
formula for Markovian Boolean `SCM`s with `P(x, y) > 0`. -/
theorem pn_eq_of_isMonotone (p : CfLaw) (hm : IsMonotone p) :
    pn p = (py p - pyx' p) / pxy p true true := by
  have h5 := hm true
  have h6 := hm false
  unfold pn py pxy pyx'
  simp [h5, h6]

/-- Theorem 3, eq. (42): under monotonicity `PS = [P(y_x) - P(y)] / P(x', y')`, both sides with
totalized division. -/
theorem ps_eq_of_isMonotone (p : CfLaw) (hm : IsMonotone p) :
    ps p = (pyx p - py p) / pxy p false false := by
  have h6 := hm false
  unfold ps pyx py pxy
  simp [h6]
  congr 1
  ring

/-- For nonnegative weights the lower bound `P(y_x) - P(y_{x'})` of eq. (23) is PNS exactly when
the law is monotone (eq. (38)). -/
theorem pns_eq_sub_iff (p : CfLaw) (hp : ∀ i j k, 0 ≤ p i j k) :
    pns p = pyx p - pyx' p ↔ IsMonotone p := by
  constructor
  · intro h k
    have h5 := hp false true true
    have h6 := hp false true false
    unfold pns pyx pyx' at h
    simp at h
    cases k <;> linarith
  · intro hm
    exact pns_eq_of_isMonotone p hm

private noncomputable def poc_aux_lo0 (a b : ℝ) : CfLaw
  | true, true, false => a
  | false, true, false => b - a
  | false, false, false => 1 - b
  | _, _, _ => 0

private noncomputable def poc_aux_lo1 (a b : ℝ) : CfLaw
  | true, true, true => b
  | true, false, true => a - b
  | false, false, false => 1 - a
  | _, _, _ => 0

/-- Sharpness of the lower bound of eq. (23): for causal effects `a, b ∈ [0, 1]`, `max 0 (a - b)`
is the least PNS of a law with `P(y_x) = a` and `P(y_{x'}) = b`. -/
theorem isLeast_pns_expFiber {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    IsLeast (pns '' expFiber a b) (max 0 (a - b)) := by
  refine ⟨?_, ?_⟩
  · by_cases h : a ≤ b
    · have hmax : max 0 (a - b) = 0 := max_eq_left (by linarith)
      rw [hmax]
      refine ⟨poc_aux_lo0 a b, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · intro i j k
        cases i <;> cases j <;> cases k <;> simp [poc_aux_lo0] <;> linarith
      · simp [poc_aux_lo0]
      · simp [pyx, poc_aux_lo0]
      · simp [pyx', poc_aux_lo0]
      · simp [pns, poc_aux_lo0]
    · have hmax : max 0 (a - b) = a - b := max_eq_right (by linarith)
      rw [hmax]
      refine ⟨poc_aux_lo1 a b, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · intro i j k
        cases i <;> cases j <;> cases k <;> simp [poc_aux_lo1] <;> linarith
      · simp [poc_aux_lo1]
      · simp [pyx, poc_aux_lo1]
      · simp [pyx', poc_aux_lo1]
      · simp [pns, poc_aux_lo1]
  · intro y hy
    obtain ⟨p, hmem, rfl⟩ := hy
    obtain ⟨hp, hpyx, hpyx'⟩ := hmem
    rw [← hpyx, ← hpyx']
    exact max_le_pns p hp.1

private theorem poc_aux_pnyx'_eq (p : CfLaw) (hp : IsCfLaw p) : pnyx' p = 1 - pyx' p := by
  have htot := hp.2
  unfold pyx' pnyx'
  simp at htot ⊢
  linarith

private noncomputable def poc_aux_hi0 (a b : ℝ) : CfLaw
  | true, false, false => a
  | false, true, true => b
  | false, false, false => 1 - a - b
  | _, _, _ => 0

private noncomputable def poc_aux_hi1 (a b : ℝ) : CfLaw
  | true, true, true => a + b - 1
  | true, false, true => 1 - b
  | false, true, true => 1 - a
  | _, _, _ => 0

/-- Sharpness of the upper bound of eq. (23): on the same fiber `P(y'_{x'}) = 1 - b`, and
`min a (1 - b)` is the greatest PNS. -/
theorem isGreatest_pns_expFiber {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) : IsGreatest (pns '' expFiber a b) (min a (1 - b)) := by
  refine ⟨?_, ?_⟩
  · by_cases h : a + b ≤ 1
    · have hmin : min a (1 - b) = a := min_eq_left (by linarith)
      rw [hmin]
      refine ⟨poc_aux_hi0 a b, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · intro i j k
        cases i <;> cases j <;> cases k <;> simp [poc_aux_hi0] <;> linarith
      · simp [poc_aux_hi0]
      · simp [pyx, poc_aux_hi0]
      · simp [pyx', poc_aux_hi0]
      · simp [pns, poc_aux_hi0]
    · have hmin : min a (1 - b) = 1 - b := min_eq_right (by linarith)
      rw [hmin]
      refine ⟨poc_aux_hi1 a b, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · intro i j k
        cases i <;> cases j <;> cases k <;> simp [poc_aux_hi1] <;> linarith
      · simp [poc_aux_hi1]
      · simp [pyx, poc_aux_hi1]
      · simp [pyx', poc_aux_hi1]
      · simp [pns, poc_aux_hi1]
  · intro y hy
    obtain ⟨p, hmem, rfl⟩ := hy
    obtain ⟨hp, hpyx, hpyx'⟩ := hmem
    have h1 := pns_le_min p hp.1
    rw [hpyx, poc_aux_pnyx'_eq p hp, hpyx'] at h1
    exact h1

end Cslib.MachineLearning.GraphicalModels.ProbabilitiesOfCausation

/-! ### Binary SCMs -/

namespace Cslib.MachineLearning.GraphicalModels.CrossWorld.BinarySCM

open Cslib.MachineLearning.GraphicalModels.ProbabilitiesOfCausation

variable {U : Type*} [Fintype U]

/-- The Tian-Pearl parameters of a binary SCM: the `pU`-weight of `Y_1 = i ∧ Y_0 = j ∧ X = k`,
with the potential outcomes `Y_1 = fY true u` and `Y_0 = fY false u` at the same noise `u` (a
probability law under `IsNoiseLaw`). -/
noncomputable def cfLaw (M : BinarySCM U) : CfLaw := fun i j k =>
  ∑ u, if M.fY true u = i ∧ M.fY false u = j ∧ M.fX u = k then M.pU u else 0

/-- Definition 13 (p. 18, eq. (37)) in every unit: `Y_0(u) = 1 → Y_1(u) = 1`. -/
def IsMonotone (M : BinarySCM U) : Prop := ∀ u, M.fY false u = true → M.fY true u = true

/-- Under `IsNoiseLaw` the parameters of a binary SCM form a law (constraint (15)). -/
theorem isCfLaw_cfLaw (M : BinarySCM U) (hM : M.IsNoiseLaw) : IsCfLaw M.cfLaw := by
  refine ⟨fun i j k => ?_, ?_⟩
  · simp only [cfLaw]
    apply Finset.sum_nonneg
    intro u _
    split
    · exact hM.1 u
    · exact le_rfl
  · simp only [cfLaw]
    simp only [Fintype.sum_bool]
    repeat rw [← Finset.sum_add_distrib]
    rw [← hM.2]
    apply Finset.sum_congr rfl
    intro u _
    cases h1 : M.fY true u <;> cases h2 : M.fY false u <;> cases h3 : M.fX u <;> simp

/-- PNS of a binary SCM is the cross-world probability `probY1Y0` (Definition 9). -/
theorem pns_cfLaw (M : BinarySCM U) : pns M.cfLaw = M.probY1Y0 := by
  simp only [pns, cfLaw, probY1Y0]
  simp only [Fintype.sum_bool]
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  cases h1 : M.fY true u <;> cases h2 : M.fY false u <;> cases h3 : M.fX u <;> simp

/-- `P(y_x)` is the interventional probability of `Y = 1` under `do(X = 1)`. -/
theorem pyx_cfLaw (M : BinarySCM U) : pyx M.cfLaw = M.law (some true, none) true true := by
  simp only [pyx, cfLaw, law]
  simp only [Fintype.sum_bool]
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  have hx : M.solX (some true, none) u = true := rfl
  have hy : M.solY (some true, none) u = M.fY true u := rfl
  rw [hx, hy]
  cases h1 : M.fY true u <;> cases h2 : M.fY false u <;> cases h3 : M.fX u <;> simp

/-- `P(y_{x'})` is the interventional probability of `Y = 1` under `do(X = 0)`. -/
theorem pyx'_cfLaw (M : BinarySCM U) : pyx' M.cfLaw = M.law (some false, none) false true := by
  simp only [pyx', cfLaw, law]
  simp only [Fintype.sum_bool]
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  have hx : M.solX (some false, none) u = false := rfl
  have hy : M.solY (some false, none) u = M.fY false u := rfl
  rw [hx, hy]
  cases h1 : M.fY true u <;> cases h2 : M.fY false u <;> cases h3 : M.fX u <;> simp

/-- `P(y'_{x'})` is the interventional probability of `Y = 0` under `do(X = 0)`. -/
theorem pnyx'_cfLaw (M : BinarySCM U) :
    pnyx' M.cfLaw = M.law (some false, none) false false := by
  simp only [pnyx', cfLaw, law]
  simp only [Fintype.sum_bool]
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  have hx : M.solX (some false, none) u = false := rfl
  have hy : M.solY (some false, none) u = M.fY false u := rfl
  rw [hx, hy]
  cases h1 : M.fY true u <;> cases h2 : M.fY false u <;> cases h3 : M.fX u <;> simp

/-- `P(X = x, Y = y)` is the observational law of the model (consistency). -/
theorem pxy_cfLaw (M : BinarySCM U) (x y : Bool) : pxy M.cfLaw x y = M.law (none, none) x y := by
  cases x
  · show (∑ i, M.cfLaw i y false) = M.law (none, none) false y
    simp only [cfLaw, law]
    simp only [Fintype.sum_bool]
    repeat rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    have hx : M.solX (none, none) u = M.fX u := rfl
    have hy : M.solY (none, none) u = M.fY (M.fX u) u := rfl
    rw [hx, hy]
    cases h3 : M.fX u <;> cases h1 : M.fY true u <;> cases h2 : M.fY false u <;>
      cases y <;> simp
  · show (∑ j, M.cfLaw y j true) = M.law (none, none) true y
    simp only [cfLaw, law]
    simp only [Fintype.sum_bool]
    repeat rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    have hx : M.solX (none, none) u = M.fX u := rfl
    have hy : M.solY (none, none) u = M.fY (M.fX u) u := rfl
    rw [hx, hy]
    cases h3 : M.fX u <;> cases h1 : M.fY true u <;> cases h2 : M.fY false u <;>
      cases y <;> simp

/-- A binary SCM that is monotone in every unit induces a monotone law: eq. (37) implies
eq. (38). -/
theorem isMonotone_cfLaw (M : BinarySCM U) (h : M.IsMonotone) :
    ProbabilitiesOfCausation.IsMonotone M.cfLaw := by
  intro k
  simp only [cfLaw]
  apply Finset.sum_eq_zero
  intro u _
  by_cases hc : (M.fY true u = false ∧ M.fY false u = true ∧ M.fX u = k)
  · obtain ⟨h1, h2, -⟩ := hc
    have ht := h u h2
    rw [h1] at ht
    simp at ht
  · simp [hc]

/-- Eq. (23), lower bound, for binary SCMs. -/
theorem max_le_probY1Y0 (M : BinarySCM U) (hM : M.IsNoiseLaw) :
    max 0 (M.law (some true, none) true true - M.law (some false, none) false true) ≤
      M.probY1Y0 := by
  have h := max_le_pns M.cfLaw (isCfLaw_cfLaw M hM).1
  rw [pyx_cfLaw, pyx'_cfLaw, pns_cfLaw] at h
  exact h

/-- Eq. (23), upper bound, for binary SCMs. -/
theorem probY1Y0_le_min (M : BinarySCM U) (hM : M.IsNoiseLaw) :
    M.probY1Y0 ≤
      min (M.law (some true, none) true true) (M.law (some false, none) false false) := by
  have h := pns_le_min M.cfLaw (isCfLaw_cfLaw M hM).1
  rw [pns_cfLaw, pyx_cfLaw, pnyx'_cfLaw] at h
  exact h

/-- Eq. (40) for binary SCMs: under monotonicity in every unit,
`P(Y_1 = 1, Y_0 = 0) = P(y_x) - P(y_{x'})`. -/
theorem probY1Y0_eq_of_isMonotone (M : BinarySCM U) (h : M.IsMonotone) :
    M.probY1Y0 = M.law (some true, none) true true - M.law (some false, none) false true := by
  have h := pns_eq_of_isMonotone M.cfLaw (isMonotone_cfLaw M h)
  rw [pns_cfLaw, pyx_cfLaw, pyx'_cfLaw] at h
  exact h

end Cslib.MachineLearning.GraphicalModels.CrossWorld.BinarySCM

/-! ### Finite SCMs -/

namespace Cslib.MachineLearning.GraphicalModels.FiniteSCM

open Cslib.MachineLearning.GraphicalModels.ProbabilitiesOfCausation

variable {n : ℕ} {U : Fin n → Type*}

/-- The joint probability of two intervened worlds at the same noise value,
`P(X_{k ← a} ∈ F, X_{k ← a'} ∈ F')`, under independent noises with laws `μ`: the cross-world
joint that `counterfactualProb`, which relates the factual world to one intervened world, does not
cover. As in `evidenceProb`, the sum runs over the product of the supports of the noise laws. -/
noncomputable def jointCounterfactualProb {α : Type*} (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (k : Fin n) (a a' : α)
    (F F' : (Fin n → α) → Prop) [DecidablePred F] [DecidablePred F'] : ℝ :=
  ∑ u ∈ Fintype.piFinset (fun j => (μ j).weights.support) with
    F (M.counterfactual k a u) ∧ F' (M.counterfactual k a' u), noiseWeight μ u

/-- The Tian-Pearl parameters of a Boolean finite SCM with treatment node `t` and outcome node
`o`: the probability of `Y_x = i ∧ Y_{x'} = j ∧ X = k`, where `Y_x = X_{t ← true} o` and
`Y_{x'} = X_{t ← false} o` at the same noise value and `X = X t` is factual. -/
noncomputable def cfLaw (M : FiniteSCM Bool n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (t o : Fin n) : CfLaw := fun i j k =>
  ∑ u ∈ Fintype.piFinset (fun l => (μ l).weights.support) with
    M.counterfactual t true u o = i ∧ M.counterfactual t false u o = j ∧ M.solve u t = k,
    noiseWeight μ u

/-- Definition 13 (p. 18, eq. (37)) in every unit: `X_{t ← false}(u) o = true` implies
`X_{t ← true}(u) o = true` for every noise value `u`. -/
def IsMonotone (M : FiniteSCM Bool n U) (t o : Fin n) : Prop :=
  ∀ u, M.counterfactual t false u o = true → M.counterfactual t true u o = true

variable (M : FiniteSCM Bool n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t o : Fin n)

private theorem poc_aux_sum_bool_triple (w : ℝ) (a b c : Bool) :
    (∑ i, ∑ j, ∑ k, if a = i ∧ b = j ∧ c = k then w else 0) = w := by
  cases a <;> cases b <;> cases c <;> simp

private theorem poc_aux_sum_comm_3 {ι : Type*} (S : Finset ι) (F : Bool → Bool → Bool → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ u ∈ S, F i j k u) = ∑ u ∈ S, ∑ i, ∑ j, ∑ k, F i j k u := by
  calc (∑ i, ∑ j, ∑ k, ∑ u ∈ S, F i j k u)
      = ∑ i, ∑ j, ∑ u ∈ S, ∑ k, F i j k u :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => Finset.sum_comm))
    _ = ∑ i, ∑ u ∈ S, ∑ j, ∑ k, F i j k u :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ u ∈ S, ∑ i, ∑ j, ∑ k, F i j k u := Finset.sum_comm

private theorem poc_aux_cflaw_nonneg {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM Bool n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t o : Fin n) (i j k : Bool) :
    0 ≤ M.cfLaw μ t o i j k := by
  simp only [cfLaw]
  exact Finset.sum_nonneg (fun u _ => noiseWeight_nonneg μ u)

/-- The parameters of a finite SCM form a law (constraint (15)). -/
theorem isCfLaw_cfLaw : IsCfLaw (M.cfLaw μ t o) := by
  refine ⟨fun i j k => poc_aux_cflaw_nonneg M μ t o i j k, ?_⟩
  simp only [cfLaw, Finset.sum_filter]
  rw [poc_aux_sum_comm_3]
  refine (Finset.sum_congr rfl (fun u _ => poc_aux_sum_bool_triple _ _ _ _)).trans
    (sum_noiseWeight_eq_one μ)

private theorem poc_aux_sum_single_k (w : ℝ) (P Q : Prop) [Decidable P] [Decidable Q] (c : Bool) :
    (∑ k, if P ∧ Q ∧ c = k then w else 0) = if P ∧ Q then w else 0 := by
  by_cases hP : P
  · by_cases hQ : Q
    · simp only [hP, hQ, ite_true, true_and]
      cases c <;> simp
    · simp [hP, hQ]
  · by_cases hQ : Q
    · simp [hP, hQ]
    · simp [hP, hQ]

/-- PNS of a finite SCM is the two-world joint `P(Y_x = 1, Y_{x'} = 0)` (Definition 9). -/
theorem pns_cfLaw : pns (M.cfLaw μ t o) =
    M.jointCounterfactualProb μ t true false (fun x => x o = true) (fun x => x o = false) := by
  simp only [pns, cfLaw, jointCounterfactualProb, Finset.sum_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun u _ => poc_aux_sum_single_k _ _ _ _)

private theorem poc_aux_sum_double_jk (w : ℝ) (P : Prop) [Decidable P] (b c : Bool) :
    (∑ j, ∑ k, if P ∧ b = j ∧ c = k then w else 0) = if P then w else 0 := by
  by_cases hP : P
  · simp only [hP, ite_true, true_and]
    cases b <;> cases c <;> simp
  · simp [hP]

private theorem poc_aux_sum_comm_2 {ι : Type*} (S : Finset ι) (F : Bool → Bool → ι → ℝ) :
    (∑ a, ∑ b, ∑ u ∈ S, F a b u) = ∑ u ∈ S, ∑ a, ∑ b, F a b u := by
  calc (∑ a, ∑ b, ∑ u ∈ S, F a b u)
      = ∑ a, ∑ u ∈ S, ∑ b, F a b u :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ u ∈ S, ∑ a, ∑ b, F a b u := Finset.sum_comm

private theorem poc_aux_evidence_true {n : ℕ} {U : Fin n → Type*} (M : FiniteSCM Bool n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) : M.evidenceProb μ (fun _ => True) = 1 := by
  simp only [evidenceProb, Finset.sum_filter, ite_true]
  exact sum_noiseWeight_eq_one μ

/-- `P(y_x)` is the counterfactual probability of `X_{t ← true} o = true` without evidence. -/
theorem pyx_cfLaw :
    pyx (M.cfLaw μ t o) =
      M.counterfactualProb μ (fun _ => True) t true (fun x => x o = true) := by
  simp only [pyx, cfLaw, counterfactualProb, Finset.sum_filter, true_and]
  rw [poc_aux_evidence_true M μ, div_one]
  rw [poc_aux_sum_comm_2]
  exact Finset.sum_congr rfl (fun u _ => poc_aux_sum_double_jk _ _ _ _)

private theorem poc_aux_sum_double_ik (w : ℝ) (a : Bool) (P : Prop) [Decidable P] (c : Bool) :
    (∑ i, ∑ k, if a = i ∧ P ∧ c = k then w else 0) = if P then w else 0 := by
  by_cases hP : P
  · simp only [hP, ite_true, true_and]
    cases a <;> cases c <;> simp
  · simp [hP]

/-- `P(y_{x'})` is the counterfactual probability of `X_{t ← false} o = true` without
evidence. -/
theorem pyx'_cfLaw :
    pyx' (M.cfLaw μ t o) =
      M.counterfactualProb μ (fun _ => True) t false (fun x => x o = true) := by
  simp only [pyx', cfLaw, counterfactualProb, Finset.sum_filter, true_and]
  rw [poc_aux_evidence_true M μ, div_one]
  rw [poc_aux_sum_comm_2]
  exact Finset.sum_congr rfl (fun u _ => poc_aux_sum_double_ik _ _ _ _)

/-- `P(y'_{x'})` is the counterfactual probability of `X_{t ← false} o = false` without
evidence. -/
theorem pnyx'_cfLaw : pnyx' (M.cfLaw μ t o) =
    M.counterfactualProb μ (fun _ => True) t false (fun x => x o = false) := by
  simp only [pnyx', cfLaw, counterfactualProb, Finset.sum_filter, true_and]
  rw [poc_aux_evidence_true M μ, div_one]
  rw [poc_aux_sum_comm_2]
  exact Finset.sum_congr rfl (fun u _ => poc_aux_sum_double_ik _ _ _ _)

private theorem poc_aux_sum_single_j (w : ℝ) (P : Prop) [Decidable P] (b : Bool) (Q : Prop)
    [Decidable Q] :
    (∑ j, if P ∧ b = j ∧ Q then w else 0) = if P ∧ Q then w else 0 := by
  by_cases hP : P
  · by_cases hQ : Q
    · simp only [hP, hQ, ite_true, true_and, and_true]
      cases b <;> simp
    · simp [hP, hQ]
  · by_cases hQ : Q
    · simp [hP, hQ]
    · simp [hP, hQ]

private theorem poc_aux_sum_single_i (w : ℝ) (a : Bool) (P : Prop) [Decidable P] (Q : Prop)
    [Decidable Q] :
    (∑ i, if a = i ∧ P ∧ Q then w else 0) = if P ∧ Q then w else 0 := by
  by_cases hP : P
  · by_cases hQ : Q
    · simp only [hP, hQ, ite_true, and_true]
      cases a <;> simp
    · simp [hP, hQ]
  · by_cases hQ : Q
    · simp [hP, hQ]
    · simp [hP, hQ]

private theorem poc_aux_if_congr (w : ℝ) (A B : Prop) [Decidable A] [Decidable B] (h : A ↔ B) :
    (if A then w else 0) = (if B then w else 0) := by
  by_cases hA : A
  · by_cases hB : B
    · simp only [hA, hB, ite_true]
    · simp only [hA, hB, ite_true, ite_false]
      exact absurd (h.mp hA) hB
  · by_cases hB : B
    · simp only [hA, hB, ite_true, ite_false]
      exact absurd (h.mpr hB) hA
    · simp only [hA, hB, ite_false]

/-- `P(X = x, Y = y)` is the probability of the factual evidence `X t = x ∧ X o = y`. -/
theorem pxy_cfLaw (x y : Bool) :
    pxy (M.cfLaw μ t o) x y = M.evidenceProb μ (fun v => v t = x ∧ v o = y) := by
  cases x
  · show (∑ i, M.cfLaw μ t o i y false) = M.evidenceProb μ (fun v => v t = false ∧ v o = y)
    simp only [cfLaw, evidenceProb, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    have hcollapse : (∑ i, if M.counterfactual t true u o = i ∧
        M.counterfactual t false u o = y ∧ M.solve u t = false then noiseWeight μ u else 0) =
        (if M.counterfactual t false u o = y ∧ M.solve u t = false then noiseWeight μ u
          else 0) :=
      poc_aux_sum_single_i _ _ _ _
    have hcons : M.solve u t = false → M.counterfactual t false u o = M.solve u o := by
      intro h
      rw [M.counterfactual_eq_solve h]
    have hiff : (M.counterfactual t false u o = y ∧ M.solve u t = false) ↔
        (M.solve u t = false ∧ M.solve u o = y) := by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, (hcons h2).symm.trans h1⟩
      · rintro ⟨h2, h3⟩
        exact ⟨(hcons h2).trans h3, h2⟩
    rw [hcollapse]
    exact poc_aux_if_congr _ _ _ hiff
  · show (∑ j, M.cfLaw μ t o y j true) = M.evidenceProb μ (fun v => v t = true ∧ v o = y)
    simp only [cfLaw, evidenceProb, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    have hcollapse : (∑ j, if M.counterfactual t true u o = y ∧
        M.counterfactual t false u o = j ∧ M.solve u t = true then noiseWeight μ u else 0) =
        (if M.counterfactual t true u o = y ∧ M.solve u t = true then noiseWeight μ u
          else 0) :=
      poc_aux_sum_single_j _ _ _ _
    have hcons : M.solve u t = true → M.counterfactual t true u o = M.solve u o := by
      intro h
      rw [M.counterfactual_eq_solve h]
    have hiff : (M.counterfactual t true u o = y ∧ M.solve u t = true) ↔
        (M.solve u t = true ∧ M.solve u o = y) := by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, (hcons h2).symm.trans h1⟩
      · rintro ⟨h2, h3⟩
        exact ⟨(hcons h2).trans h3, h2⟩
    rw [hcollapse]
    exact poc_aux_if_congr _ _ _ hiff

/-- Definition 7 at the `FiniteSCM` level: PN is the conditional counterfactual probability
`P(X_{t ← false} o = false | X t = true, X o = true)`, both sides with totalized division. -/
theorem pn_cfLaw : pn (M.cfLaw μ t o) =
    M.counterfactualProb μ (fun v => v t = true ∧ v o = true) t false (fun v => v o = false) := by
  simp only [pn, counterfactualProb, pxy_cfLaw, cfLaw, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  have hcons : M.solve u t = true → M.counterfactual t true u o = M.solve u o := by
    intro h
    rw [M.counterfactual_eq_solve h]
  have hiff : (M.counterfactual t true u o = true ∧ M.counterfactual t false u o = false ∧
      M.solve u t = true) ↔
      ((M.solve u t = true ∧ M.solve u o = true) ∧ M.counterfactual t false u o = false) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h3, (hcons h3).symm.trans h1⟩, h2⟩
    · rintro ⟨⟨h3, h4⟩, h2⟩
      exact ⟨(hcons h3).trans h4, h2, h3⟩
  exact poc_aux_if_congr _ _ _ hiff

/-- Definition 8 at the `FiniteSCM` level: PS is the conditional counterfactual probability
`P(X_{t ← true} o = true | X t = false, X o = false)`, both sides with totalized division. -/
theorem ps_cfLaw : ps (M.cfLaw μ t o) =
    M.counterfactualProb μ (fun v => v t = false ∧ v o = false) t true (fun v => v o = true) := by
  simp only [ps, counterfactualProb, pxy_cfLaw, cfLaw, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  have hcons : M.solve u t = false → M.counterfactual t false u o = M.solve u o := by
    intro h
    rw [M.counterfactual_eq_solve h]
  have hiff : (M.counterfactual t true u o = true ∧ M.counterfactual t false u o = false ∧
      M.solve u t = false) ↔
      ((M.solve u t = false ∧ M.solve u o = false) ∧ M.counterfactual t true u o = true) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h3, (hcons h3).symm.trans h2⟩, h1⟩
    · rintro ⟨⟨h3, h4⟩, h1⟩
      exact ⟨h1, (hcons h3).trans h4, h3⟩
  exact poc_aux_if_congr _ _ _ hiff

/-- A finite SCM that is monotone in every unit induces a monotone law: eq. (37) implies
eq. (38). -/
theorem isMonotone_cfLaw (h : M.IsMonotone t o) :
    ProbabilitiesOfCausation.IsMonotone (M.cfLaw μ t o) := by
  intro k
  simp only [cfLaw]
  apply Finset.sum_eq_zero
  intro u hu
  simp only [Finset.mem_filter] at hu
  obtain ⟨-, h1, h2, -⟩ := hu
  rw [h u h2] at h1
  exact absurd h1.symm Bool.false_ne_true

/-- Eq. (23), lower bound, for finite SCMs. -/
theorem max_le_jointCounterfactualProb :
    max 0 (M.counterfactualProb μ (fun _ => True) t true (fun x => x o = true) -
        M.counterfactualProb μ (fun _ => True) t false (fun x => x o = true)) ≤
      M.jointCounterfactualProb μ t true false (fun x => x o = true) (fun x => x o = false) := by
  rw [← pns_cfLaw, ← pyx_cfLaw, ← pyx'_cfLaw]
  exact max_le_pns _ (fun i j k => poc_aux_cflaw_nonneg M μ t o i j k)

/-- Eq. (23), upper bound, for finite SCMs. -/
theorem jointCounterfactualProb_le_min :
    M.jointCounterfactualProb μ t true false (fun x => x o = true) (fun x => x o = false) ≤
      min (M.counterfactualProb μ (fun _ => True) t true (fun x => x o = true))
        (M.counterfactualProb μ (fun _ => True) t false (fun x => x o = false)) := by
  rw [← pns_cfLaw, ← pyx_cfLaw, ← pnyx'_cfLaw]
  exact pns_le_min _ (fun i j k => poc_aux_cflaw_nonneg M μ t o i j k)

/-- Eq. (40) for finite SCMs: under monotonicity in every unit, the two-world joint
`P(Y_x = 1, Y_{x'} = 0)` is `P(y_x) - P(y_{x'})`. -/
theorem jointCounterfactualProb_eq_of_isMonotone (h : M.IsMonotone t o) :
    M.jointCounterfactualProb μ t true false (fun x => x o = true) (fun x => x o = false) =
      M.counterfactualProb μ (fun _ => True) t true (fun x => x o = true) -
        M.counterfactualProb μ (fun _ => True) t false (fun x => x o = true) := by
  rw [← pns_cfLaw, ← pyx_cfLaw, ← pyx'_cfLaw]
  exact pns_eq_of_isMonotone _ (isMonotone_cfLaw M μ t o h)

end Cslib.MachineLearning.GraphicalModels.FiniteSCM

namespace Cslib.MachineLearning.GraphicalModels.ProbabilitiesOfCausation

/-! ### Realization -/

/-- Every Tian-Pearl law is the law of a binary SCM. -/
theorem exists_binarySCM_cfLaw (p : CfLaw) (hp : IsCfLaw p) :
    ∃ M : CrossWorld.BinarySCM (Bool × Bool × Bool), M.IsNoiseLaw ∧ M.cfLaw = p := by
  refine ⟨⟨fun u => p u.1 u.2.1 u.2.2, fun u => u.2.2,
    fun x u => if x then u.1 else u.2.1⟩, ⟨?_, ?_⟩, ?_⟩
  · exact fun u => hp.1 u.1 u.2.1 u.2.2
  · simp only [Fintype.sum_prod_type]
    exact hp.2
  · funext i j k
    show (∑ u : Bool × Bool × Bool,
      if u.1 = i ∧ u.2.1 = j ∧ u.2.2 = k then p u.1 u.2.1 u.2.2 else 0) = p i j k
    simp only [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    cases i <;> cases j <;> cases k <;> simp

private noncomputable def poc_aux_margX (p : CfLaw) (b : Bool) : ℝ :=
  ∑ i, ∑ j, p i j b

private theorem poc_aux_margX_nonneg (p : CfLaw) (hp : IsCfLaw p) (b : Bool) :
    0 ≤ poc_aux_margX p b := by
  unfold poc_aux_margX
  apply Fintype.sum_nonneg
  intro i
  apply Fintype.sum_nonneg
  intro j
  exact hp.1 i j b

private theorem poc_aux_margX_sum (p : CfLaw) (hp : IsCfLaw p) :
    ∑ b, poc_aux_margX p b = 1 := by
  unfold poc_aux_margX
  have h := hp.2
  rw [Finset.sum_comm]
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

private noncomputable def poc_aux_cond (p : CfLaw) (b : Bool) (a : Bool × Bool) : ℝ :=
  if poc_aux_margX p b = 0 then (if a = (false, false) then 1 else 0)
  else p a.1 a.2 b / poc_aux_margX p b

private theorem poc_aux_cond_nonneg (p : CfLaw) (hp : IsCfLaw p) (b : Bool) (a : Bool × Bool) :
    0 ≤ poc_aux_cond p b a := by
  unfold poc_aux_cond
  by_cases h : poc_aux_margX p b = 0
  · simp [h]
    by_cases ha : a = (false, false) <;> simp [ha]
  · simp [h]
    apply div_nonneg (hp.1 a.1 a.2 b)
    exact poc_aux_margX_nonneg p hp b

private theorem poc_aux_cond_sum (p : CfLaw) (hp : IsCfLaw p) (b : Bool) :
    ∑ a, poc_aux_cond p b a = 1 := by
  unfold poc_aux_cond
  by_cases h : poc_aux_margX p b = 0
  · simp [h]
  · simp [h]
    rw [← Finset.sum_div]
    have hsum : (∑ a : Bool × Bool, p a.1 a.2 b) = poc_aux_margX p b := by
      unfold poc_aux_margX
      rw [Fintype.sum_prod_type]
    rw [hsum]
    exact div_self h

private def poc_aux_U : Fin 3 → Type
  | ⟨0, _⟩ => Bool
  | ⟨1, _⟩ => Unit
  | ⟨2, _⟩ => (Bool × Bool) × (Bool × Bool)
  | ⟨n + 3, h⟩ => False.elim (by omega)

private instance poc_aux_U_fintype (k : Fin 3) : Fintype (poc_aux_U k) :=
  match k with
  | ⟨0, _⟩ => inferInstanceAs (Fintype Bool)
  | ⟨1, _⟩ => inferInstanceAs (Fintype Unit)
  | ⟨2, _⟩ => inferInstanceAs (Fintype ((Bool × Bool) × (Bool × Bool)))
  | ⟨n + 3, h⟩ => False.elim (by omega)

private def poc_aux_M : FiniteSCM Bool 3 poc_aux_U where
  pa _ := Finset.univ
  f
    | ⟨0, _⟩, _, u => u
    | ⟨1, _⟩, z, _ => z ⟨(0 : Fin 1), Finset.mem_univ _⟩
    | ⟨2, _⟩, z, u =>
      let b0 := z ⟨(0 : Fin 2), Finset.mem_univ _⟩
      let a := z ⟨(1 : Fin 2), Finset.mem_univ _⟩
      let pair := if b0 then u.1 else u.2
      if a then pair.1 else pair.2
    | ⟨n + 3, h⟩, _, _ => False.elim (by omega)

private noncomputable def poc_aux_mu (p : CfLaw) (hp : IsCfLaw p) :
    (k : Fin 3) → StdSimplex ℝ (poc_aux_U k)
  | ⟨0, _⟩ => StdSimplex.ofWeights (poc_aux_margX p)
      (poc_aux_margX_nonneg p hp) (poc_aux_margX_sum p hp)
  | ⟨1, _⟩ => StdSimplex.ofWeights (fun _ : Unit => (1 : ℝ))
      (fun _ => zero_le_one) (by show ∑ _ : Unit, (1 : ℝ) = 1; simp)
  | ⟨2, _⟩ => StdSimplex.ofWeights
      (fun a : (Bool × Bool) × (Bool × Bool) =>
        poc_aux_cond p true a.1 * poc_aux_cond p false a.2)
      (fun a : (Bool × Bool) × (Bool × Bool) => mul_nonneg
        (poc_aux_cond_nonneg p hp true a.1)
        (poc_aux_cond_nonneg p hp false a.2))
      (by
        show ∑ a : (Bool × Bool) × (Bool × Bool),
          poc_aux_cond p true a.1 * poc_aux_cond p false a.2 = 1
        rw [Fintype.sum_prod_type]
        have hF := poc_aux_cond_sum p hp false
        have hT := poc_aux_cond_sum p hp true
        simp only [← Finset.mul_sum, hF, mul_one]
        exact hT)
  | ⟨n + 3, h⟩ => False.elim (by omega)

private theorem poc_aux_solve_t (u : (k : Fin 3) → poc_aux_U k) :
    poc_aux_M.solve u 1 = u 0 := by
  rfl

private def poc_aux_test0 (u : (k : Fin 3) → poc_aux_U k) : Bool :=
  u ⟨0, by decide⟩

private def poc_aux_test2 (u : (k : Fin 3) → poc_aux_U k) : (Bool × Bool) × (Bool × Bool) :=
  u ⟨2, by decide⟩

private theorem poc_aux_cf_true (u : (k : Fin 3) → poc_aux_U k) :
    poc_aux_M.counterfactual 1 true u 2 =
      ((if poc_aux_test0 u then (poc_aux_test2 u).1 else (poc_aux_test2 u).2)).1 := by
  rfl

private theorem poc_aux_cf_false (u : (k : Fin 3) → poc_aux_U k) :
    poc_aux_M.counterfactual 1 false u 2 =
      ((if poc_aux_test0 u then (poc_aux_test2 u).1 else (poc_aux_test2 u).2)).2 := by
  rfl

private theorem poc_aux_w0 (p : CfLaw) (hp : IsCfLaw p) (b : Bool) :
    ((poc_aux_mu p hp) ⟨0, by decide⟩).weights b = poc_aux_margX p b :=
  StdSimplex.ofWeights_weights (poc_aux_margX p)
    (poc_aux_margX_nonneg p hp) (poc_aux_margX_sum p hp) b

private theorem poc_aux_w1 (p : CfLaw) (hp : IsCfLaw p) (x : Unit) :
    ((poc_aux_mu p hp) ⟨1, by decide⟩).weights x = 1 :=
  StdSimplex.ofWeights_weights (fun _ : Unit => (1 : ℝ))
    (fun _ => zero_le_one) (by show ∑ _ : Unit, (1 : ℝ) = 1; simp) x

private theorem poc_aux_w2 (p : CfLaw) (hp : IsCfLaw p)
    (a : (Bool × Bool) × (Bool × Bool)) :
    ((poc_aux_mu p hp) ⟨2, by decide⟩).weights a =
      poc_aux_cond p true a.1 * poc_aux_cond p false a.2 :=
  StdSimplex.ofWeights_weights
    (fun a : (Bool × Bool) × (Bool × Bool) =>
      poc_aux_cond p true a.1 * poc_aux_cond p false a.2)
    (fun a : (Bool × Bool) × (Bool × Bool) => mul_nonneg
      (poc_aux_cond_nonneg p hp true a.1)
      (poc_aux_cond_nonneg p hp false a.2))
    (by
      show ∑ a : (Bool × Bool) × (Bool × Bool),
        poc_aux_cond p true a.1 * poc_aux_cond p false a.2 = 1
      rw [Fintype.sum_prod_type]
      have hF := poc_aux_cond_sum p hp false
      have hT := poc_aux_cond_sum p hp true
      simp only [← Finset.mul_sum, hF, mul_one]
      exact hT) a

private theorem poc_aux_fin0_eq : (0 : Fin 3) = ⟨0, by decide⟩ := by rfl

private theorem poc_aux_fin1_eq : (1 : Fin 3) = ⟨1, by decide⟩ := by rfl

private theorem poc_aux_fin2_eq : (2 : Fin 3) = ⟨2, by decide⟩ := by rfl

private theorem poc_aux_solve_t0 (u : (k : Fin 3) → poc_aux_U k) :
    poc_aux_M.solve u 1 = poc_aux_test0 u := by
  rfl

private theorem poc_aux_w0u (p : CfLaw) (hp : IsCfLaw p)
    (u : (k : Fin 3) → poc_aux_U k) :
    ((poc_aux_mu p hp) ⟨0, by decide⟩).weights (u ⟨0, by decide⟩) =
      poc_aux_margX p (poc_aux_test0 u) :=
  poc_aux_w0 p hp (poc_aux_test0 u)

private theorem poc_aux_w1u (p : CfLaw) (hp : IsCfLaw p)
    (u : (k : Fin 3) → poc_aux_U k) :
    ((poc_aux_mu p hp) ⟨1, by decide⟩).weights (u ⟨1, by decide⟩) = 1 :=
  poc_aux_w1 p hp ()

private theorem poc_aux_w2u (p : CfLaw) (hp : IsCfLaw p)
    (u : (k : Fin 3) → poc_aux_U k) :
    ((poc_aux_mu p hp) ⟨2, by decide⟩).weights (u ⟨2, by decide⟩) =
      poc_aux_cond p true (poc_aux_test2 u).1 *
        poc_aux_cond p false (poc_aux_test2 u).2 :=
  poc_aux_w2 p hp (poc_aux_test2 u)

private theorem poc_aux_noiseWeight (p : CfLaw) (hp : IsCfLaw p)
    (u : (k : Fin 3) → poc_aux_U k) :
    FiniteSCM.noiseWeight (poc_aux_mu p hp) u =
      poc_aux_margX p (poc_aux_test0 u) *
        (poc_aux_cond p true (poc_aux_test2 u).1 *
          poc_aux_cond p false (poc_aux_test2 u).2) := by
  unfold FiniteSCM.noiseWeight
  rw [Fin.prod_univ_three]
  rw [poc_aux_fin0_eq, poc_aux_fin1_eq, poc_aux_fin2_eq]
  rw [poc_aux_w0u, poc_aux_w1u, poc_aux_w2u]
  ring

private def poc_aux_toProd (u : (k : Fin 3) → poc_aux_U k) :
    Bool × ((Bool × Bool) × (Bool × Bool)) :=
  (poc_aux_test0 u, poc_aux_test2 u)

private def poc_aux_ofProd (pa : Bool × ((Bool × Bool) × (Bool × Bool))) :
    (k : Fin 3) → poc_aux_U k
  | ⟨0, _⟩ => pa.1
  | ⟨1, _⟩ => ()
  | ⟨2, _⟩ => pa.2
  | ⟨n + 3, h⟩ => False.elim (by omega)

private theorem poc_aux_left_inv (u : (k : Fin 3) → poc_aux_U k) :
    poc_aux_ofProd (poc_aux_toProd u) = u := by
  funext k
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ =>
    show (() : poc_aux_U ⟨1, by decide⟩) = u ⟨1, by decide⟩
    cases h : u ⟨1, by decide⟩
    rfl
  | ⟨2, _⟩ => rfl
  | ⟨n + 3, h⟩ => exact False.elim (by omega)

private theorem poc_aux_right_inv (pa : Bool × ((Bool × Bool) × (Bool × Bool))) :
    poc_aux_toProd (poc_aux_ofProd pa) = pa := by
  rfl

private def poc_aux_equiv : ((k : Fin 3) → poc_aux_U k) ≃
    (Bool × ((Bool × Bool) × (Bool × Bool))) where
  toFun := poc_aux_toProd
  invFun := poc_aux_ofProd
  left_inv := poc_aux_left_inv
  right_inv := poc_aux_right_inv

private theorem poc_aux_w0U (p : CfLaw) (hp : IsCfLaw p)
    (b : poc_aux_U ⟨0, by decide⟩) :
    ((poc_aux_mu p hp) ⟨0, by decide⟩).weights b = poc_aux_margX p b :=
  poc_aux_w0 p hp b

private theorem poc_aux_w2U (p : CfLaw) (hp : IsCfLaw p)
    (a : poc_aux_U ⟨2, by decide⟩) :
    ((poc_aux_mu p hp) ⟨2, by decide⟩).weights a =
      poc_aux_cond p true a.1 * poc_aux_cond p false a.2 :=
  poc_aux_w2 p hp a

private theorem poc_aux_outside_zero (p : CfLaw) (hp : IsCfLaw p)
    (u : (k : Fin 3) → poc_aux_U k)
    (h : u ∉ Fintype.piFinset
      (fun j => ((poc_aux_mu p hp) j).weights.support)) :
    FiniteSCM.noiseWeight (poc_aux_mu p hp) u = 0 := by
  unfold FiniteSCM.noiseWeight
  rw [Fintype.mem_piFinset] at h
  push Not at h
  obtain ⟨k, hk⟩ := h
  have hw : ((poc_aux_mu p hp) k).weights (u k) = 0 :=
    Finsupp.notMem_support_iff.mp hk
  exact Finset.prod_eq_zero (Finset.mem_univ k) hw

private instance poc_aux_pi_fintype : Fintype ((k : Fin 3) → poc_aux_U k) :=
  inferInstance

private theorem poc_aux_zero_of_marg (p : CfLaw) (hp : IsCfLaw p) (i j k : Bool)
    (h : poc_aux_margX p k = 0) : p i j k = 0 := by
  unfold poc_aux_margX at h
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool] at h
  have h1 := hp.1 true true k
  have h2 := hp.1 true false k
  have h3 := hp.1 false true k
  have h4 := hp.1 false false k
  cases i <;> cases j <;> linarith

private theorem poc_aux_marg_cond (p : CfLaw) (hp : IsCfLaw p) (i j k : Bool) :
    poc_aux_margX p k * poc_aux_cond p k (i, j) = p i j k := by
  unfold poc_aux_cond
  by_cases h : poc_aux_margX p k = 0
  · simp [h, poc_aux_zero_of_marg p hp i j k h]
  · simp only [h, ↓reduceIte]
    field_simp

private theorem poc_aux_prod_eq (a : Bool × Bool) (i j : Bool) :
    (a.1 = i ∧ a.2 = j) ↔ a = (i, j) := by
  cases a <;> simp

private theorem poc_aux_coord (p : CfLaw) (hp : IsCfLaw p) (i j k : Bool) :
    ((poc_aux_M.cfLaw (poc_aux_mu p hp) 1 2) i j k) = p i j k := by
  unfold FiniteSCM.cfLaw
  simp only [poc_aux_cf_true, poc_aux_cf_false, poc_aux_solve_t0,
    poc_aux_noiseWeight]
  rw [Finset.sum_filter]
  have hsub : Fintype.piFinset
      (fun j => ((poc_aux_mu p hp) j).weights.support) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hext : (∑ x ∈ Fintype.piFinset
      (fun j => ((poc_aux_mu p hp) j).weights.support),
      (if (if poc_aux_test0 x = true then (poc_aux_test2 x).1
        else (poc_aux_test2 x).2).1 = i ∧
        (if poc_aux_test0 x = true then (poc_aux_test2 x).1
        else (poc_aux_test2 x).2).2 = j ∧ poc_aux_test0 x = k then
        poc_aux_margX p (poc_aux_test0 x) *
          (poc_aux_cond p true (poc_aux_test2 x).1 *
            poc_aux_cond p false (poc_aux_test2 x).2) else 0)) =
      (∑ x ∈ Finset.univ,
      (if (if poc_aux_test0 x = true then (poc_aux_test2 x).1
        else (poc_aux_test2 x).2).1 = i ∧
        (if poc_aux_test0 x = true then (poc_aux_test2 x).1
        else (poc_aux_test2 x).2).2 = j ∧ poc_aux_test0 x = k then
        poc_aux_margX p (poc_aux_test0 x) *
          (poc_aux_cond p true (poc_aux_test2 x).1 *
            poc_aux_cond p false (poc_aux_test2 x).2) else 0)) := by
    apply Finset.sum_subset hsub
    intro x _ hx
    by_cases hP : (if poc_aux_test0 x = true then (poc_aux_test2 x).1
        else (poc_aux_test2 x).2).1 = i ∧
        (if poc_aux_test0 x = true then (poc_aux_test2 x).1
        else (poc_aux_test2 x).2).2 = j ∧ poc_aux_test0 x = k
    · rw [if_pos hP]
      have hz := poc_aux_outside_zero p hp x hx
      simp only [poc_aux_noiseWeight] at hz
      exact hz
    · simp [hP]
  rw [hext]
  have hreindex : (∑ x ∈ Finset.univ,
      (if (if poc_aux_test0 x = true then (poc_aux_test2 x).1
        else (poc_aux_test2 x).2).1 = i ∧
        (if poc_aux_test0 x = true then (poc_aux_test2 x).1
        else (poc_aux_test2 x).2).2 = j ∧ poc_aux_test0 x = k then
        poc_aux_margX p (poc_aux_test0 x) *
          (poc_aux_cond p true (poc_aux_test2 x).1 *
            poc_aux_cond p false (poc_aux_test2 x).2) else 0)) =
      (∑ pa ∈ (Finset.univ : Finset (Bool × ((Bool × Bool) × (Bool × Bool)))),
      (if (if pa.1 = true then pa.2.1 else pa.2.2).1 = i ∧
        (if pa.1 = true then pa.2.1 else pa.2.2).2 = j ∧ pa.1 = k then
        poc_aux_margX p pa.1 *
          (poc_aux_cond p true pa.2.1 *
            poc_aux_cond p false pa.2.2) else 0)) :=
    Equiv.sum_comp poc_aux_equiv (fun pa : Bool × ((Bool × Bool) × (Bool × Bool)) =>
      (if (if pa.1 = true then pa.2.1 else pa.2.2).1 = i ∧
        (if pa.1 = true then pa.2.1 else pa.2.2).2 = j ∧ pa.1 = k then
        poc_aux_margX p pa.1 *
          (poc_aux_cond p true pa.2.1 *
            poc_aux_cond p false pa.2.2) else 0))
  rw [hreindex, Fintype.sum_prod_type, Fintype.sum_bool]
  cases k
  · simp
    simp only [poc_aux_prod_eq]
    rw [Fintype.sum_prod_type]
    dsimp
    have hinner : ∀ x : Bool × Bool, (∑ y : Bool × Bool,
        (if y = (i, j) then poc_aux_margX p false *
          (poc_aux_cond p true x * poc_aux_cond p false y) else 0)) =
        poc_aux_margX p false *
          (poc_aux_cond p true x * poc_aux_cond p false (i, j)) :=
      fun x => Fintype.sum_ite_eq' _ _
    simp only [hinner]
    have hfac : (∑ x : Bool × Bool, poc_aux_margX p false *
        (poc_aux_cond p true x * poc_aux_cond p false (i, j))) =
        poc_aux_margX p false * poc_aux_cond p false (i, j) *
          (∑ x : Bool × Bool, poc_aux_cond p true x) := by
      simp only [mul_assoc, mul_comm (poc_aux_cond p true _) _,
        ← Finset.mul_sum]
    rw [hfac, poc_aux_cond_sum p hp true, mul_one]
    exact poc_aux_marg_cond p hp i j false
  · simp
    simp only [poc_aux_prod_eq]
    rw [Fintype.sum_prod_type]
    dsimp
    rw [Finset.sum_comm]
    have hinnerT : ∀ y : Bool × Bool, (∑ x : Bool × Bool,
        (if x = (i, j) then poc_aux_margX p true *
          (poc_aux_cond p true x * poc_aux_cond p false y) else 0)) =
        poc_aux_margX p true *
          (poc_aux_cond p true (i, j) * poc_aux_cond p false y) :=
      fun y => Fintype.sum_ite_eq' _ _
    simp only [hinnerT]
    have hfacT : (∑ y : Bool × Bool, poc_aux_margX p true *
        (poc_aux_cond p true (i, j) * poc_aux_cond p false y)) =
        poc_aux_margX p true * poc_aux_cond p true (i, j) *
          (∑ y : Bool × Bool, poc_aux_cond p false y) := by
      simp only [mul_assoc, mul_comm (poc_aux_cond p false _) _,
        ← Finset.mul_sum]
    rw [hfacT, poc_aux_cond_sum p hp false, mul_one]
    exact poc_aux_marg_cond p hp i j true

/-- Every Tian-Pearl law is the law of a Boolean finite SCM on the confounded triangle
`L → X`, `L → Y`, `X → Y` (nodes `0, 1, 2`, `L` latent). -/
theorem exists_finiteSCM_cfLaw (p : CfLaw) (hp : IsCfLaw p) :
    ∃ (U : Fin 3 → Type) (M : FiniteSCM Bool 3 U) (μ : (k : Fin 3) → StdSimplex ℝ (U k)),
      M.pa 1 = Finset.univ ∧ M.pa 2 = Finset.univ ∧ M.cfLaw μ 1 2 = p :=
  ⟨poc_aux_U, poc_aux_M, poc_aux_mu p hp, rfl, rfl,
    funext fun i => funext fun j => funext fun k =>
      poc_aux_coord p hp i j k⟩

/-- Tian and Pearl, Section 5, Table 2, with no prevention: the unique monotone law with these
experimental and nonexperimental data (eqs. (61)-(63)): `p₁₀₁ = p₁₀₀ = 1/1000`,
`p₁₁₀ = 14/1000`, `p₀₀₁ = 499/1000`, `p₀₀₀ = 485/1000`. -/
noncomputable def section5Monotone : CfLaw
  | true, false, true => 1 / 1000
  | true, false, false => 1 / 1000
  | true, true, false => 14 / 1000
  | false, false, true => 499 / 1000
  | false, false, false => 485 / 1000
  | _, _, _ => 0

/-- A non-monotone law with the same Table 2 data, attaining the upper bound of eq. (58). -/
noncomputable def section5Upper : CfLaw
  | true, false, true => 1 / 1000
  | true, false, false => 15 / 1000
  | false, true, false => 14 / 1000
  | false, false, true => 499 / 1000
  | false, false, false => 471 / 1000
  | _, _, _ => 0

/-- `section5Monotone` is a law (constraint (15)). -/
example : IsCfLaw section5Monotone := by
  refine ⟨fun i j k => ?_, ?_⟩
  · cases i <;> cases j <;> cases k <;> norm_num [section5Monotone]
  · simp [section5Monotone]
    norm_num

/-- `section5Monotone` is monotone (eq. (38)). -/
example : IsMonotone section5Monotone := by
  intro k; cases k <;> rfl

/-- Table 2 data: `P(y_x) = 0.016`, `P(y_{x'}) = 0.014`. -/
example : pyx section5Monotone = 16 / 1000 ∧ pyx' section5Monotone = 14 / 1000 := by
  constructor <;> simp [pyx, pyx', section5Monotone]
  norm_num

/-- Both laws have the observational law of Table 2 and the same causal effects. -/
example : (∀ x y, pxy section5Monotone x y = pxy section5Upper x y) ∧
    pyx section5Monotone = pyx section5Upper ∧ pyx' section5Monotone = pyx' section5Upper := by
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · cases x <;> cases y <;> simp [pxy, section5Monotone, section5Upper]
    norm_num
  · simp [pyx, section5Monotone, section5Upper]; norm_num
  · simp [pyx', section5Monotone, section5Upper]

/-- Table 2 data: `P(x, y) = 2/2000` and `P(x', y') = 972/2000`. -/
example :
    pxy section5Monotone true true = 2 / 2000 ∧ pxy section5Monotone false false = 972 / 2000 := by
  constructor <;> simp [pxy, section5Monotone] <;> norm_num

/-- The tightness example: the lower bound of eq. (23) (= eq. (58)) is attained, eq. (61). -/
example : pns section5Monotone = max 0 (pyx section5Monotone - pyx' section5Monotone) ∧
    pns section5Monotone = 2 / 1000 := by
  simp [pns, pyx, pyx', section5Monotone]
  norm_num

/-- Eqs. (62)-(63): `PN = 1`, `PS = 1/486` (printed `0.002`). -/
example : pn section5Monotone = 1 ∧ ps section5Monotone = 1 / 486 := by
  simp [pn, ps, pxy, section5Monotone]
  norm_num

/-- The upper bound of eq. (23) (= eq. (58)) is attained by the non-monotone law. -/
example : pns section5Upper = min (pyx section5Upper) (pnyx' section5Upper) ∧
    pns section5Upper = 16 / 1000 := by
  simp [pns, pyx, pnyx', section5Upper]
  norm_num

/-- Negative control: without monotonicity eq. (40) fails. -/
example : pns section5Upper ≠ pyx section5Upper - pyx' section5Upper := by
  simp [pns, pyx, pyx', section5Upper]
  norm_num

/-- A monotone binary SCM (noisy-OR form `Y = (X ∧ A) ∨ B`) whose law is `section5Monotone`. -/
noncomputable def section5SCM : CrossWorld.BinarySCM (Bool × Bool × Bool) where
  pU u := section5Monotone u.1 u.2.1 u.2.2
  fX u := u.2.2
  fY x u := (x && u.1) || u.2.1

/-- `section5SCM` is monotone in every unit (Definition 13). -/
example : section5SCM.IsMonotone := by
  intro u h
  simp_all [section5SCM]

/-- The law of `section5SCM` is `section5Monotone`. -/
theorem section5SCM_cfLaw : section5SCM.cfLaw = section5Monotone := by
  funext i j k
  cases i <;> cases j <;> cases k <;>
    simp [CrossWorld.BinarySCM.cfLaw, section5SCM, section5Monotone, Fintype.sum_prod_type]

/-- **Tightness example** (Section 5, eq. (61)): `section5SCM` is a probability model whose PNS
`P(Y_1 = 1, Y_0 = 0) = 1/500` (printed `0.002`) is the lower bound of eq. (23). -/
theorem section5SCM_tight : section5SCM.IsNoiseLaw ∧
    section5SCM.probY1Y0 = max 0 (section5SCM.law (some true, none) true true -
      section5SCM.law (some false, none) false true) ∧
    section5SCM.probY1Y0 = 1 / 500 := by
  have hnoise : section5SCM.IsNoiseLaw := by
    refine ⟨fun u => ?_, ?_⟩
    · obtain ⟨a, b, c⟩ := u
      cases a <;> cases b <;> cases c <;> norm_num [section5SCM, section5Monotone]
    · simp [section5SCM, section5Monotone, Fintype.sum_prod_type]
      norm_num
  have hpns : section5SCM.probY1Y0 = 1 / 500 := by
    simp [CrossWorld.BinarySCM.probY1Y0, section5SCM, section5Monotone,
      Fintype.sum_prod_type]
    norm_num
  have hlaw1 : section5SCM.law (some true, none) true true = 16 / 1000 := by
    simp [CrossWorld.BinarySCM.law, CrossWorld.BinarySCM.solX, CrossWorld.BinarySCM.solY,
      section5SCM, section5Monotone, Fintype.sum_prod_type]
    norm_num
  have hlaw2 : section5SCM.law (some false, none) false true = 14 / 1000 := by
    simp [CrossWorld.BinarySCM.law, CrossWorld.BinarySCM.solX, CrossWorld.BinarySCM.solY,
      section5SCM, section5Monotone, Fintype.sum_prod_type]
  refine ⟨hnoise, ?_, hpns⟩
  rw [hpns, hlaw1, hlaw2]
  norm_num

/-- The `CrossWorld` witnesses attain both bounds of eq. (23) at `P(y_x) = P(y_{x'}) = 1/2`:
`constantResponse` the lower bound `0`, `switchingResponse` the upper bound `1/2`. -/
theorem constantResponse_switchingResponse_attain :
    CrossWorld.constantResponse.probY1Y0 =
        max 0 (CrossWorld.constantResponse.law (some true, none) true true -
          CrossWorld.constantResponse.law (some false, none) false true) ∧
      CrossWorld.switchingResponse.probY1Y0 =
        min (CrossWorld.switchingResponse.law (some true, none) true true)
          (CrossWorld.switchingResponse.law (some false, none) false false) := by
  have hc0 : CrossWorld.constantResponse.probY1Y0 = 0 := by
    simp [CrossWorld.BinarySCM.probY1Y0, CrossWorld.constantResponse]
  have hc1 : CrossWorld.constantResponse.law (some true, none) true true = 1 / 2 := by
    simp [CrossWorld.BinarySCM.law, CrossWorld.BinarySCM.solX, CrossWorld.BinarySCM.solY,
      CrossWorld.constantResponse, Fintype.sum_prod_type]
    norm_num
  have hc2 : CrossWorld.constantResponse.law (some false, none) false true = 1 / 2 := by
    simp [CrossWorld.BinarySCM.law, CrossWorld.BinarySCM.solX, CrossWorld.BinarySCM.solY,
      CrossWorld.constantResponse, Fintype.sum_prod_type]
    norm_num
  have hs0 : CrossWorld.switchingResponse.probY1Y0 = 1 / 2 := by
    simp [CrossWorld.BinarySCM.probY1Y0, CrossWorld.switchingResponse,
      Fintype.sum_prod_type]
    norm_num
  have hs1 : CrossWorld.switchingResponse.law (some true, none) true true = 1 / 2 := by
    simp [CrossWorld.BinarySCM.law, CrossWorld.BinarySCM.solX, CrossWorld.BinarySCM.solY,
      CrossWorld.switchingResponse, Fintype.sum_prod_type]
    norm_num
  have hs2 : CrossWorld.switchingResponse.law (some false, none) false false = 1 / 2 := by
    simp [CrossWorld.BinarySCM.law, CrossWorld.BinarySCM.solX, CrossWorld.BinarySCM.solY,
      CrossWorld.switchingResponse, Fintype.sum_prod_type]
    norm_num
  rw [hc0, hc1, hc2, hs0, hs1, hs2]
  norm_num

/-- The or-gate on `X → Y` (node `0` is `X`, node `1` is `Y`): `X = U₀` and `Y = X ∨ U₁`; with the
fair-coin noises `orNoise`, a monotone Markovian finite SCM. -/
noncomputable def orModel : FiniteSCM Bool 2 (fun _ => Bool) where
  pa _ := Finset.univ
  f k z u := if h : (k : ℕ) = 0 then u
    else (z ⟨⟨0, by have := k.isLt; omega⟩, Finset.mem_univ _⟩ || u)

/-- Independent fair-coin noise laws for `orModel`. -/
noncomputable def orNoise : (k : Fin 2) → StdSimplex ℝ ((fun _ => Bool) k) :=
  fun _ => InterveningVsConditioning.coin (1 / 2) (by norm_num) (by norm_num)

/-- A Markovian finite SCM attaining the lower bound of eq. (23): `orModel` with fair-coin noises
is monotone in every unit, and PNS `= 1/2 = max 0 (1 - 1/2)`. -/
theorem orModel_tight : orModel.IsMonotone 0 1 ∧
    pns (orModel.cfLaw orNoise 0 1) =
      max 0 (pyx (orModel.cfLaw orNoise 0 1) - pyx' (orModel.cfLaw orNoise 0 1)) ∧
    pns (orModel.cfLaw orNoise 0 1) = 1 / 2 := by
  have hsolve0 : ∀ u, orModel.solve u 0 = u 0 := fun u => rfl
  have hcf : ∀ (a : Bool) u, orModel.counterfactual 0 a u 1 = (a || u 1) :=
    fun a u => rfl
  have hmono : orModel.IsMonotone 0 1 := by
    intro u _
    simp [hcf]
  have hw : ∀ u, FiniteSCM.noiseWeight orNoise u = 1 / 4 := by
    intro u
    simp only [FiniteSCM.noiseWeight, Fin.prod_univ_two, orNoise]
    cases hu0 : u 0 <;> cases hu1 : u 1 <;>
      simp only [InterveningVsConditioning.coin_true,
        InterveningVsConditioning.coin_false] <;> norm_num
  have hsupp : ∀ k : Fin 2, (orNoise k).weights.support = Finset.univ := by
    intro k
    apply Finset.eq_univ_of_forall
    intro a
    cases a <;>
      simp only [Finsupp.mem_support_iff, orNoise,
        InterveningVsConditioning.coin_true,
        InterveningVsConditioning.coin_false] <;> norm_num
  have hpi : Fintype.piFinset (fun j => (orNoise j).weights.support) = Finset.univ := by
    simp only [hsupp, Fintype.piFinset_univ]
  have hreindex : ∀ F : (Fin 2 → Bool) → ℝ,
      (∑ u, F u) = ∑ a : Bool, ∑ b : Bool, F ![a, b] := by
    intro F
    have h := Equiv.sum_comp (finTwoArrowEquiv Bool)
      (fun p : Bool × Bool => F ((finTwoArrowEquiv Bool).symm p))
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type,
      finTwoArrowEquiv_symm_apply] at h
    exact h
  have htable : orModel.cfLaw orNoise 0 1 = fun i j k => if i then 1 / 4 else 0 := by
    funext i j k
    cases i <;> cases j <;> cases k <;>
      simp only [FiniteSCM.cfLaw, hpi, Finset.sum_filter] <;>
      simp only [hcf, hsolve0, hw, hreindex, Matrix.cons_val_zero,
        Matrix.cons_val_one] <;>
      simp
  have hpns : pns (orModel.cfLaw orNoise 0 1) = 1 / 2 := by
    rw [htable]
    simp [pns]
    norm_num
  have hpyx : pyx (orModel.cfLaw orNoise 0 1) = 1 := by
    rw [htable]
    simp [pyx]
    norm_num
  have hpyx' : pyx' (orModel.cfLaw orNoise 0 1) = 1 / 2 := by
    rw [htable]
    simp [pyx']
    norm_num
  refine ⟨hmono, ?_, hpns⟩
  rw [hpns, hpyx, hpyx']
  norm_num

end Cslib.MachineLearning.GraphicalModels.ProbabilitiesOfCausation
