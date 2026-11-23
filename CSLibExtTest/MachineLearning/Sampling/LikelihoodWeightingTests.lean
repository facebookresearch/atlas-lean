/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.LikelihoodWeighting
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Tests for likelihood weighting

The sprinkler network (Russell and Norvig, *AIMA* 4th ed., §13.4.2) on `Bool`: node `0` Cloudy,
`1` Sprinkler, `2` Rain, `3` WetGrass, with the evidence `Sprinkler = true`, `WetGrass = true`.
Every node may read every earlier node (`pa k = univ`); the tables depend only on the sprinkler
graph's parents.

* No evidence: weight `1`, proposal equal to the joint, evidence probability `1`.
* `P(e) = 2781/10000` and `P(Rain | e) = 33/103`; `E_q[w] = P(e)` instantiated.
* One-sample self-normalized likelihood weighting has expectation `1/2 ≠ 33/103`: the
  finite-sample self-normalized estimator is biased, while the numerator is unbiased.
* Zero-probability evidence (`Sprinkler = false`, `Rain = false`, `WetGrass = true`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.LikelihoodWeightingTests

open Cslib.MachineLearning GraphicalModels Convexity Finset MeasureTheory ProbabilityTheory
  Filter
open scoped Topology

/-- The distribution on `Bool` with `P(true) = p`. -/
noncomputable def coin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : StdSimplex ℝ Bool :=
  StdSimplex.duple (t := 1 - p) true false h0 (by linarith) (by ring)

@[simp]
theorem coin_weights (p : ℝ) (h0 h1) (v : Bool) :
    (coin p h0 h1).weights v = if v then p else 1 - p := by
  cases v <;> simp [coin, StdSimplex.duple]

/-- The sprinkler network. -/
noncomputable def sprinkler : BayesNet Bool 4 where
  pa _ := univ
  cpt k u := if h0 : (k : ℕ) = 0 then coin (1 / 2) (by norm_num) (by norm_num) else
    if h1 : (k : ℕ) = 1 then
      (if u ⟨⟨0, by omega⟩, mem_univ _⟩ then coin (1 / 10) (by norm_num) (by norm_num)
        else coin (1 / 2) (by norm_num) (by norm_num))
    else if h2 : (k : ℕ) = 2 then
      (if u ⟨⟨0, by omega⟩, mem_univ _⟩ then coin (4 / 5) (by norm_num) (by norm_num)
        else coin (1 / 5) (by norm_num) (by norm_num))
    else
      (if u ⟨⟨1, by omega⟩, mem_univ _⟩ then
        (if u ⟨⟨2, by omega⟩, mem_univ _⟩ then coin (99 / 100) (by norm_num) (by norm_num)
          else coin (9 / 10) (by norm_num) (by norm_num))
      else
        (if u ⟨⟨2, by omega⟩, mem_univ _⟩ then coin (9 / 10) (by norm_num) (by norm_num)
          else coin 0 (by norm_num) (by norm_num)))

/-- `P(true) = p` as a real function. -/
def pr (p : ℝ) (v : Bool) : ℝ := if v then p else 1 - p

/-- Sums over `Fin 4 → Bool`. -/
theorem sum_four (g : (Fin 4 → Bool) → ℝ) :
    ∑ x, g x = ∑ a, ∑ b, ∑ c, ∑ d, g ![a, b, c, d] := by
  rw [sum_snoc, sum_snoc, sum_snoc, sum_snoc, Fintype.sum_unique]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun d _ => congrArg g ?_
  funext i
  fin_cases i <;> rfl

theorem sprinkler_joint (a b c d : Bool) :
    sprinkler.joint ![a, b, c, d] = pr (1 / 2) a * pr (if a then 1 / 10 else 1 / 2) b *
      pr (if a then 4 / 5 else 1 / 5) c *
      pr (if b then (if c then 99 / 100 else 9 / 10) else (if c then 9 / 10 else 0)) d := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_four]
  cases a <;> cases b <;> cases c <;> cases d <;> simp [sprinkler, pr]

/-- The evidence `Sprinkler = true`, `WetGrass = true`. -/
def E : Finset (Fin 4) := {1, 3}

/-- Evidence values (`true` on every node; only the values on `E` matter). -/
def e : Fin 4 → Bool := fun _ => true

/-- Rain indicator. -/
noncomputable def rain (x : Fin 4 → Bool) : ℝ := if x 2 then 1 else 0

/-! ### No evidence -/

/-- **Positive check**: without evidence the likelihood weight is `1`. -/
example (x : Fin 4 → Bool) : sprinkler.lwWeight ∅ x = 1 := by simp

/-- Without evidence the clamped proposal is the joint, and the evidence has probability `1`. -/
example : (sprinkler.mutilateSet ∅ e).joint = sprinkler.joint ∧ sprinkler.evidenceProb ∅ e = 1 :=
  ⟨sprinkler.joint_mutilateSet_empty e, sprinkler.evidenceProb_empty e⟩

/-! ### Evidence `Sprinkler = true`, `WetGrass = true` -/

/-- **Non-vacuity**: the evidence has positive probability `P(e) = 0.2781`. -/
theorem evidenceProb_sprinkler : sprinkler.evidenceProb E e = 2781 / 10000 := by
  rw [BayesNet.evidenceProb, sum_filter, sum_four]
  simp [E, e, sprinkler_joint, pr]
  norm_num

/-- `E_q[w] = P(e)` on the sprinkler network. -/
example : ∑ x, (sprinkler.mutilateSet E e).joint x * sprinkler.lwWeight E x = 2781 / 10000 := by
  rw [sprinkler.sum_proposal_mul_lwWeight, evidenceProb_sprinkler]

/-- The posterior `P(Rain = true | Sprinkler = true, WetGrass = true) = 33/103`. -/
theorem posteriorMean_rain : sprinkler.posteriorMean E e rain = 33 / 103 := by
  rw [BayesNet.posteriorMean, evidenceProb_sprinkler, sum_filter, sum_four]
  simp [E, e, sprinkler_joint, pr, rain]
  norm_num

/-- The proposal mean of the rain indicator over positive weights is `1/2`. -/
theorem proposal_rain_mean :
    ∑ x, (sprinkler.mutilateSet E e).joint x *
      (if sprinkler.lwWeight E x = 0 then 0 else rain x) = 1 / 2 := by
  rw [sum_four]
  simp [BayesNet.joint_mutilateSet, BayesNet.lwWeight, E, e, Fin.prod_univ_four, rain,
    sprinkler, BayesNet.paVal]
  norm_num

/-- **Negative check**: one-sample self-normalized likelihood weighting is biased. For any samples
with the proposal law, its expectation is `1/2`, while the posterior is `33/103`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → Fin 4 → Bool}
    (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = (sprinkler.mutilateSet E e).jointMeasure) :
    ∫ ω, sprinkler.lwSelfNormalized E rain X 1 ω ∂μ ≠ sprinkler.posteriorMean E e rain := by
  rw [sprinkler.integral_lwSelfNormalized_one E e rain hX hlaw, proposal_rain_mean,
    posteriorMean_rain]
  norm_num

/-- The likelihood-weighting numerator is unbiased for `P(Rain = true, e) = 891/10000`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → Fin 4 → Bool}
    (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = (sprinkler.mutilateSet E e).jointMeasure) {m : ℕ} (hm : m ≠ 0) :
    ∫ ω, sprinkler.lwEstimate E rain X m ω ∂μ = 891 / 10000 := by
  rw [sprinkler.integral_lwEstimate E e rain hX hlaw hm, sum_filter, sum_four]
  simp [E, e, sprinkler_joint, pr, rain]
  norm_num

/-- Self-normalized likelihood weighting converges almost surely to `33/103`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → Fin 4 → Bool}
    (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = (sprinkler.mutilateSet E e).jointMeasure)
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun m ↦ sprinkler.lwSelfNormalized E rain X m ω) atTop
      (𝓝 (33 / 103)) := by
  rw [← posteriorMean_rain]
  exact sprinkler.tendsto_lwSelfNormalized E e rain hX hlaw hindep
    (by rw [evidenceProb_sprinkler]; norm_num)

/-! ### Zero-probability evidence -/

/-- **Boundary**: `Sprinkler = false`, `Rain = false`, `WetGrass = true` has probability `0`, so
the positivity hypothesis of `tendsto_lwSelfNormalized` fails. -/
example : sprinkler.evidenceProb {1, 2, 3} ![true, false, false, true] = 0 := by
  rw [BayesNet.evidenceProb, sum_filter, sum_four]
  simp [sprinkler_joint, pr]

/-- Support coverage on the sprinkler network: the evidence-consistent all-`true` assignment has
nonzero proposal probability and weight. -/
example : (sprinkler.mutilateSet E e).joint ![true, true, true, true] ≠ 0 ∧
    sprinkler.lwWeight E ![true, true, true, true] ≠ 0 :=
  sprinkler.proposal_ne_zero_of_joint_ne_zero (by decide)
    (by rw [sprinkler_joint]; norm_num [pr])

end Cslib.MachineLearning.LikelihoodWeightingTests

#print axioms Cslib.MachineLearning.GraphicalModels.BayesNet.proposal_mul_lwWeight
#print axioms Cslib.MachineLearning.GraphicalModels.BayesNet.sum_proposal_mul_lwWeight
#print axioms Cslib.MachineLearning.GraphicalModels.BayesNet.integral_lwEstimate
#print axioms Cslib.MachineLearning.GraphicalModels.BayesNet.tendsto_lwSelfNormalized
#print axioms Cslib.MachineLearning.GraphicalModels.BayesNet.integral_lwSelfNormalized_one
#print axioms Cslib.MachineLearning.GraphicalModels.BayesNet.proposal_ne_zero_of_joint_ne_zero
#print axioms Cslib.MachineLearning.LikelihoodWeightingTests.posteriorMean_rain
#print axioms Cslib.MachineLearning.LikelihoodWeightingTests.proposal_rain_mean
