/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.HellySelection

@[expose] public section

open Filter ProbabilityTheory Set
open scoped Topology

namespace MathlibExtTest.Probability.HellySelection

/-- The step function at `c`, zero before `c` and one from `c` on, as a
Stieltjes function. -/
private noncomputable def step (c : ℝ) : StieltjesFunction ℝ where
  toFun := fun x => if x < c then (0 : ℝ) else 1
  mono' := by
    intro a b hab
    by_cases ha : a < c
    · by_cases hb : b < c
      · simp [ha, hb]
      · simp [ha, hb]
    · by_cases hb : b < c
      · exact absurd (lt_of_le_of_lt hab hb) ha
      · simp [ha, hb]
  right_continuous' := by
    intro x
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    by_cases hx : x < c
    · refine ⟨c - x, sub_pos.mpr hx, fun y hy hyx => ?_⟩
      have hy_lt : y < c := by
        have h1 := hyx
        rw [Real.dist_eq, abs_lt] at h1
        linarith [h1.2]
      rw [ite_eq_left hy_lt, ite_eq_left hx]
      simp [hε]
    · push Not at hx
      refine ⟨1, one_pos, fun y hy _hyx => ?_⟩
      have hy_ge : c ≤ y := le_trans hx (Set.mem_Ici.mp hy)
      rw [ite_eq_right (not_lt.mpr hy_ge), ite_eq_right (not_lt.mpr hx)]
      simp [hε]

/-- The step function has the endpoint limits of the distribution of a point mass. -/
private theorem step_isDistributionFunction (c : ℝ) : IsDistributionFunction (step c) where
  tendsto_atBot := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_atBot.mpr ⟨c - 1, fun _ h => h⟩] with y hy
    show (0 : ℝ) = if y < c then (0 : ℝ) else 1
    rw [ite_eq_left (lt_of_le_of_lt hy (by linarith))]
  tendsto_atTop := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_atTop.mpr ⟨c + 1, fun _ h => h⟩] with y hy
    show (1 : ℝ) = if y < c then (0 : ℝ) else 1
    rw [ite_eq_right (not_lt.mpr (le_trans (by linarith) hy))]

/-- Helly's selection theorem restates with the exact public signature. -/
example (F : ℕ → StieltjesFunction ℝ) (hF : ∀ n, IsDistributionFunction (F n)) :
    ∃ (φ : ℕ → ℕ) (G : StieltjesFunction ℝ),
      StrictMono φ ∧
      ∀ x, ContinuousAt (↑G) x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x)) :=
  helly_selection F hF

/-- The step distribution function is non-negative and bounded by `1`. -/
example (c x : ℝ) : 0 ≤ (if x < c then (0 : ℝ) else 1) ∧
    (if x < c then (0 : ℝ) else 1) ≤ 1 := by
  have h := step_isDistributionFunction c
  exact ⟨h.nonneg x, h.le_one x⟩

/-- Helly's theorem applied to the constant sequence of point-mass
distribution functions: a convergent subsequence exists. -/
example :
    ∃ (φ : ℕ → ℕ) (G : StieltjesFunction ℝ),
      StrictMono φ ∧
      ∀ x, ContinuousAt (↑G) x →
        Tendsto (fun k => (fun _ => if x < (0 : ℝ) then (0 : ℝ) else 1) (φ k))
          atTop (𝓝 (G x)) :=
  helly_selection (fun _ => step 0) (fun _ => step_isDistributionFunction 0)

/-- Helly's theorem applied to the genuinely non-constant sequence of
point masses at `n`: the mass escapes to `+∞`, so the subsequential limit
is allowed to lose mass — the theorem still produces a monotone,
right-continuous subsequential limit. -/
example :
    ∃ (φ : ℕ → ℕ) (G : StieltjesFunction ℝ),
      StrictMono φ ∧
      ∀ x, ContinuousAt (↑G) x →
        Tendsto (fun k => (if x < (φ k : ℝ) then (0 : ℝ) else 1))
          atTop (𝓝 (G x)) := by
  apply helly_selection (fun n => step (n : ℝ))
  intro n
  exact step_isDistributionFunction (n : ℝ)

/-- Right-limit regularization preserves the expected pointwise values. -/
example (f : ℝ → ℝ) (hf : Monotone f) (x : ℝ) :
    hf.stieltjesFunction x = Function.rightLim f x := rfl

/-- The distribution contract includes both unit-interval bounds and right continuity. -/
example (F : StieltjesFunction ℝ) (hF : IsDistributionFunction F) (x : ℝ) :
    0 ≤ F x ∧ F x ≤ 1 ∧ ContinuousWithinAt F (Ici x) x :=
  ⟨hF.nonneg x, hF.le_one x, F.right_continuous x⟩

/-- The selected Stieltjes bundle exposes the standard interval-measure formula. -/
example (G : StieltjesFunction ℝ) (a b : ℝ) :
    G.measure (Ioc a b) = ENNReal.ofReal (G b - G a) :=
  G.measure_Ioc a b

/-- The closed right endpoint includes the unit jump at `c`. -/
example (c : ℝ) : (step c).measure (Ioc (c - 1) c) = 1 := by
  rw [StieltjesFunction.measure_Ioc]
  simp [step, show c - 1 < c by linarith]

/-- An interval open at the jump excludes its mass. -/
example (c : ℝ) : (step c).measure (Ioc c (c + 1)) = 0 := by
  rw [StieltjesFunction.measure_Ioc]
  simp [step, show ¬c + 1 < c by linarith]

/-- Both endpoint limits give the point-mass Stieltjes measure total mass one. -/
example (c : ℝ) : (step c).measure univ = 1 := by
  have h := step_isDistributionFunction c
  simpa using (step c).measure_univ h.tendsto_atBot h.tendsto_atTop

/-- The concrete point-mass fixture is a probability measure through the standard API. -/
example (c : ℝ) : MeasureTheory.IsProbabilityMeasure (step c).measure := by
  have h := step_isDistributionFunction c
  exact (step c).isProbabilityMeasure h.tendsto_atBot h.tendsto_atTop

/-- The public unit-interval API applies directly to the standard bundle. -/
example (F : StieltjesFunction ℝ) (hF : IsDistributionFunction F) (x : ℝ) :
    F x ∈ Icc (0 : ℝ) 1 := hF.mem_Icc x

/-- The escaping family has different distributions already at indices zero and one. -/
example : step 0 0 = 1 ∧ step 1 0 = 0 := by
  simp [step]

/-- For each fixed real argument, point masses at `n` converge to zero. -/
example (x : ℝ) : Tendsto (fun n : ℕ => step (n : ℝ) x) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt x
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_atTop.mpr ⟨N, fun _ hn => hn⟩] with n hn
  have hx : x < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
  simp [step, hx]

/-- Point masses at `-n` converge to one at every fixed real argument. -/
example (x : ℝ) : Tendsto (fun n : ℕ => step (-(n : ℝ)) x) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-x)
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_atTop.mpr ⟨N, fun _ hn => hn⟩] with n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : ¬x < -(n : ℝ) := by linarith
  simp [step, hx]

/-- The zero limit is a Stieltjes function but fails the distribution limit at `+∞`. -/
example : ¬IsDistributionFunction (StieltjesFunction.const ℝ 0) := by
  intro h
  have hz : Tendsto (StieltjesFunction.const ℝ 0 : ℝ → ℝ) atTop (𝓝 0) :=
    tendsto_const_nhds
  have heq : (0 : ℝ) = 1 := tendsto_nhds_unique hz h.tendsto_atTop
  norm_num at heq

/-- The one limit fails the distribution limit at `-∞`. -/
example : ¬IsDistributionFunction (StieltjesFunction.const ℝ 1) := by
  intro h
  have ho : Tendsto (StieltjesFunction.const ℝ 1 : ℝ → ℝ) atBot (𝓝 1) :=
    tendsto_const_nhds
  have heq : (1 : ℝ) = 0 := tendsto_nhds_unique ho h.tendsto_atBot
  norm_num at heq

-- `#print axioms` for the public and reused declarations: only the standard triple.
#print axioms ProbabilityTheory.IsDistributionFunction
#print axioms ProbabilityTheory.helly_selection
#print axioms ProbabilityTheory.IsDistributionFunction.nonneg
#print axioms ProbabilityTheory.IsDistributionFunction.le_one
#print axioms ProbabilityTheory.IsDistributionFunction.mem_Icc
#print axioms StieltjesFunction
#print axioms StieltjesFunction.instCoeFun
#print axioms Monotone.stieltjesFunction
#print axioms step
#print axioms step_isDistributionFunction

end MathlibExtTest.Probability.HellySelection
