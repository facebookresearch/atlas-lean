/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Identifiability
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Deterministic

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics

namespace MathlibExtTest.Probability.Statistics.Identifiability

/-- Duplicate parameter labels with equal estimand values are allowed: a constant estimand is
identified by any family, including one that is not injective. -/
example : IsIdentifiedBy (fun _ : Bool => Measure.dirac (0 : ℝ)) (fun _ => (1 : ℝ)) := by
  exact fun _ _ _ => rfl

/-- Two indistinguishable laws with different latent means are not identified. -/
example : ¬ IsIdentifiedBy (fun _ : Bool => Measure.dirac (0 : ℝ))
    (fun b => if b then (1 : ℝ) else 0) := by
  exact not_isIdentifiedBy_of_eq_of_ne (θ := true) (θ' := false) rfl (by norm_num)

/-- Strict separation matters: at the boundary `2ε = |τ θ - τ θ'|` (`τ θ = 0`, `τ θ' = 2`,
`ε = 1`) the constant estimator `δ ≡ 1` succeeds at both parameters, so the success
probabilities sum to `2`. -/
example : (Measure.dirac (0 : ℝ)).real {x : ℝ | |(fun _ : ℝ => (1 : ℝ)) x - 0| ≤ 1} +
    (Measure.dirac (0 : ℝ)).real {x : ℝ | |(fun _ : ℝ => (1 : ℝ)) x - 2| ≤ 1} = 2 := by
  rw [Measure.dirac_real_apply_of_mem (by norm_num),
    Measure.dirac_real_apply_of_mem (by norm_num)]
  norm_num

/-- `ε = 0` is admitted: exact recovery fails with probability at least `1/2` at one of two
indistinguishable parameters with distinct estimand values. -/
example {δ : ℝ → ℝ} (hδ : Measurable δ) :
    1 / 2 ≤ (Measure.dirac (0 : ℝ)).real {x | 0 < |δ x - 0|} ∨
      1 / 2 ≤ (Measure.dirac (0 : ℝ)).real {x | 0 < |δ x - 1|} := by
  exact exists_measureReal_failure_ge_half (fun _ : Bool => Measure.dirac (0 : ℝ))
    (fun b => if b then (1 : ℝ) else 0) (θ := false) (θ' := true) rfl hδ le_rfl (by norm_num)

/-- A fair coin on `Bool`. -/
noncomputable def fairCoin : Measure Bool :=
  (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure fairCoin := by
  constructor
  simp [fairCoin, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The sign `±1` of a coin toss. -/
noncomputable def coinSign (b : Bool) : ℝ := if b then 1 else -1

/-- Positive: two equal fair-coin laws with latent estimands `0` and `1` fire the bound at
`ε = 1 / 4`. -/
example :
    let P : Bool → Measure Bool := fun _ => fairCoin
    let τ : Bool → ℝ := fun b => if b then 0 else 1
    1 / 2 ≤ (P true).real {x | (1 / 4 : ℝ) < |coinSign x - τ true|} ∨
      1 / 2 ≤ (P false).real {x | (1 / 4 : ℝ) < |coinSign x - τ false|} := by
  intro P τ
  have hP : P true = P false := rfl
  have hδ : Measurable coinSign := Measurable.of_discrete
  have hε : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hsep : 2 * (1 / 4 : ℝ) < |τ true - τ false| := by
    show 2 * (1 / 4 : ℝ) < |(0 : ℝ) - 1|
    norm_num
  haveI hI : IsProbabilityMeasure (P true) := by
    show IsProbabilityMeasure fairCoin
    infer_instance
  exact MathlibExt.Probability.Statistics.exists_measureReal_failure_ge_half
    (δ := coinSign) (ε := 1 / 4) P τ hP hδ hε hsep

/-- Boundary: at `2ε = |Δτ|` the success sets overlap (`1 / 2` lies in both). -/
example : ¬ Disjoint ({x : ℝ | |x - (0 : ℝ)| ≤ 1 / 2} : Set ℝ)
    ({x : ℝ | |x - (1 : ℝ)| ≤ 1 / 2} : Set ℝ) := by
  have h1 : |(1 / 2 : ℝ) - 0| ≤ 1 / 2 := by norm_num
  have h2 : |(1 / 2 : ℝ) - 1| ≤ 1 / 2 := by norm_num
  intro h
  exact (Set.disjoint_left.mp h h1) h2

/-- Boundary: at `ε = 0` the success sets need not be disjoint. With equal estimands the
two `ε`-success sets coincide, so disjointness fails. -/
example : ¬ Disjoint ({x : ℝ | |x - (0 : ℝ)| ≤ (0 : ℝ)} : Set ℝ)
    ({x : ℝ | |x - (0 : ℝ)| ≤ (0 : ℝ)} : Set ℝ) := by
  have h0 : |(0 : ℝ) - 0| ≤ (0 : ℝ) := by simp
  intro h
  exact (Set.disjoint_left.mp h h0) h0

/-- Vacuity: with equal estimands the separation hypothesis is impossible. -/
example (τ : Bool → ℝ) (h : τ true = τ false) :
    ¬ ∃ ε : ℝ, 0 ≤ ε ∧ 2 * ε < |τ true - τ false| := by
  intro ⟨ε, hε, hsep⟩
  rw [h, sub_self, abs_zero] at hsep
  linarith

/-- Constant Gaussian kernel (randomized): every observation draws `N(0, 1)` independently
of the input. -/
noncomputable def gaussKernel : Kernel Bool ℝ :=
  Kernel.const Bool (gaussianReal (0 : ℝ) 1)

instance : IsMarkovKernel gaussKernel := by
  refine IsMarkovKernel.mk fun _ => ?_
  show IsProbabilityMeasure (gaussianReal (0 : ℝ) 1)
  exact inferInstance

/-- Randomized-kernel use: a constant Gaussian kernel fires the kernel bound. The
conclusion is the kernel theorem's disjunction verbatim; no output-law computation is
needed. -/
example :
    let P : Bool → Measure Bool := fun _ => fairCoin;
    let τ : Bool → ℝ := fun b => if b then 0 else 1;
    1 / 2 ≤ ((P true).bind gaussKernel).real {y | (1 / 4 : ℝ) < |y - τ true|} ∨
      1 / 2 ≤ ((P false).bind gaussKernel).real {y | (1 / 4 : ℝ) < |y - τ false|} := by
  intro P τ
  have hP : P true = P false := rfl
  have hI : IsProbabilityMeasure (P true) := by
    show IsProbabilityMeasure fairCoin
    exact inferInstance
  have hε : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hsep : 2 * (1 / 4 : ℝ) < |τ true - τ false| := by
    show 2 * (1 / 4 : ℝ) < |(0 : ℝ) - 1|
    norm_num
  exact MathlibExt.Probability.Statistics.exists_measureReal_failure_ge_half_kernel
    P τ hP hε hsep

/-- Deterministic-kernel use: `Kernel.deterministic` recovers the deterministic bound as a
corollary of the kernel bound. -/
example :
    let P : Bool → Measure Bool := fun _ => fairCoin;
    let τ : Bool → ℝ := fun b => if b then 0 else 1;
    1 / 2 ≤ ((P true).bind (Kernel.deterministic coinSign Measurable.of_discrete)).real
        {y | (1 / 4 : ℝ) < |y - τ true|} ∨
      1 / 2 ≤ ((P false).bind (Kernel.deterministic coinSign Measurable.of_discrete)).real
        {y | (1 / 4 : ℝ) < |y - τ false|} := by
  intro P τ
  have hP : P true = P false := rfl
  have hδ : Measurable coinSign := Measurable.of_discrete
  have hI : IsProbabilityMeasure (P true) := by
    show IsProbabilityMeasure fairCoin
    exact inferInstance
  have hε : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hsep : 2 * (1 / 4 : ℝ) < |τ true - τ false| := by
    show 2 * (1 / 4 : ℝ) < |(0 : ℝ) - 1|
    norm_num
  exact MathlibExt.Probability.Statistics.exists_measureReal_failure_ge_half_of_deterministic
    P τ hP hδ hε hsep

end MathlibExtTest.Probability.Statistics.Identifiability
