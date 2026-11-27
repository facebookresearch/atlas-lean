/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.MachineLearning.Bandit.CanonicalModel
import Mathlib.Probability.Distributions.Cauchy

/-!
# Canonical bandit model tests

Checks of the canonical bandit model on concrete instances and edge cases: pull counts of an
explicit history, the horizon zero, conditions (a) and (b) for the coordinates of the canonical
model, uniqueness of the law, the regret of a constant policy on a bandit with point-mass rewards
(zero for the best arm, positive otherwise), the zero regret of every policy when all arms have
the same reward law with a finite mean, and a bandit with Cauchy rewards, to which the canonical
law and its characterization apply although its rewards have no finite mean.
-/

namespace CSLibExtTest.MachineLearning.Bandit

open MeasureTheory ProbabilityTheory Finset Cslib.MachineLearning.Bandit

/-! ## Pull counts of an explicit history -/

/-- A history of three rounds with two arms: arm `0`, then arm `1`, then arm `0`. -/
noncomputable def h3 : History 2 3 := ![(0, 1), (1, 0), (0, 5)]

example : pullCount 0 h3 = 2 := by decide

example : pullCount 1 h3 = 1 := by decide

example : ∑ i, pullCount i h3 = 3 := sum_pullCount h3

example : pullCount 1 h3 ≤ 3 := pullCount_le 1 h3

/-- Appending a round with arm `1` adds one to its pull count and nothing to arm `0`'s. -/
example (x : ℝ) : pullCount 1 (Fin.snoc h3 (1, x) : History 2 4) = 2 ∧
    pullCount 0 (Fin.snoc h3 (1, x) : History 2 4) = 2 := by
  simp [pullCount_snoc, show pullCount 1 h3 = 1 by decide, show pullCount 0 h3 = 2 by decide]

/-- No arm is pulled in the empty history. -/
example {k : ℕ} (i : Fin k) (h : History k 0) : pullCount i h = 0 := by
  simpa using pullCount_le i h

/-! ## A bandit with point-mass rewards and constant policies -/

/-- The bandit whose arm `i` always pays `c i`. -/
noncomputable def diracBandit {k : ℕ} (c : Fin k → ℝ) : StochasticBandit k where
  law i := Measure.dirac (c i)
  isProbabilityMeasure_law _ := inferInstance

theorem diracBandit_hasFiniteMeans {k : ℕ} (c : Fin k → ℝ) : (diracBandit c).HasFiniteMeans :=
  fun _ ↦ integrable_dirac (by simp)

theorem diracBandit_mean {k : ℕ} (c : Fin k → ℝ) (i : Fin k) : (diracBandit c).mean i = c i := by
  simp [StochasticBandit.mean, diracBandit]

/-- The policy that always pulls arm `i`. -/
noncomputable def constPolicy {k : ℕ} (i : Fin k) : Policy k where
  kernel _ := Kernel.const _ (Measure.dirac i)
  isMarkovKernel_kernel _ := inferInstance

/-- Under a constant policy, the expected mean of the arm chosen in every round is the mean of
the pulled arm. -/
theorem integral_mean_constPolicy {k n : ℕ} (ν : StochasticBandit k) (i : Fin k) (t : Fin n) :
    ∫ h, ν.mean (h t).1 ∂canonicalLaw ν (constPolicy i) n = ν.mean i := by
  have hm : StronglyMeasurable (fun q : History k t × Fin k ↦ ν.mean q.2) :=
    ((measurable_of_countable ν.mean).comp measurable_snd).stronglyMeasurable
  have hint : Integrable (fun q : History k t × Fin k ↦ ν.mean q.2)
      (canonicalLaw ν (constPolicy i) t ⊗ₘ (constPolicy i).kernel t) :=
    (integrable_const (∑ j, |ν.mean j|)).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun q ↦ single_le_sum (f := fun j ↦ |ν.mean j|) (fun _ _ ↦ abs_nonneg _)
        (mem_univ q.2))
  rw [← integral_map (History.measurable_take_action t).aemeasurable hm.aestronglyMeasurable,
    map_take_action_canonicalLaw, Measure.integral_compProd hint]
  simp [constPolicy]

/-- The regret of the policy that always pulls arm `i` is `n (μ* - μ_i)`. -/
theorem regret_constPolicy {k : ℕ} [NeZero k] (ν : StochasticBandit k) (hν : ν.HasFiniteMeans)
    (i : Fin k) (n : ℕ) :
    regret ν (constPolicy i) n = n * (ν.maxMean - ν.mean i) := by
  rw [regret, integral_finsetSum _ fun t _ ↦ integrable_reward ν _ hν t]
  simp [integral_reward ν _ hν, integral_mean_constPolicy, mul_sub]

/-- Two arms paying `0` and `1`: the largest mean is `1`. -/
example : (diracBandit ![0, 1]).maxMean = 1 := by
  refine le_antisymm (sup'_le _ _ fun i _ ↦ ?_) ?_
  · fin_cases i <;> simp [diracBandit_mean]
  · simpa [diracBandit_mean] using (diracBandit ![0, 1]).mean_le_maxMean 1

/-- Always pulling the better arm has zero regret, always pulling the worse one has regret `n`. -/
example (n : ℕ) : regret (diracBandit ![0, 1]) (constPolicy 1) n = 0 ∧
    regret (diracBandit ![0, 1]) (constPolicy 0) n = n := by
  have hmax : (diracBandit ![0, 1]).maxMean = 1 := by
    refine le_antisymm (sup'_le _ _ fun i _ ↦ ?_) ?_
    · fin_cases i <;> simp [diracBandit_mean]
    · simpa [diracBandit_mean] using (diracBandit ![0, 1]).mean_le_maxMean 1
  simp [regret_constPolicy _ (diracBandit_hasFiniteMeans _), hmax, diracBandit_mean]

/-! ## Horizon zero -/

example {k : ℕ} (ν : StochasticBandit k) (π : Policy k) :
    canonicalLaw ν π 0 = Measure.dirac default := canonicalLaw_zero ν π

example {k : ℕ} [NeZero k] (ν : StochasticBandit k) (π : Policy k) : regret ν π 0 = 0 := by
  simp [regret]

/-! ## Structure of the canonical law -/

example {k : ℕ} (ν : StochasticBandit k) (π : Policy k) (n : ℕ) :
    IsProbabilityMeasure (canonicalLaw ν π n) := inferInstance

/-- The first round's arm has the law of the policy's first kernel at the empty history. -/
example {k : ℕ} (ν : StochasticBandit k) (π : Policy k) :
    (canonicalLaw ν π 1).map (fun h ↦ (Fin.take 0 (Nat.zero_le 1) h, (h 0).1)) =
      Measure.dirac default ⊗ₘ π.kernel 0 :=
  map_take_action_canonicalLaw ν π 0

/-- Conditions (a) and (b) hold for the coordinates of the canonical bandit model itself. -/
example {k : ℕ} [NeZero k] (ν : StochasticBandit k) (π : Policy k) (n : ℕ) (t : Fin n) :
    condDistrib (fun h : History k n ↦ (h t).1) (fun h ↦ Fin.take t t.isLt.le h)
        (canonicalLaw ν π n)
      =ᵐ[(canonicalLaw ν π n).map (Fin.take t t.isLt.le)] π.kernel t ∧
    condDistrib (fun h : History k n ↦ (h t).2) (fun h ↦ (Fin.take t t.isLt.le h, (h t).1))
        (canonicalLaw ν π n)
      =ᵐ[(canonicalLaw ν π n).map fun h ↦ (Fin.take t t.isLt.le h, (h t).1)]
        ν.rewardKernel t :=
  (map_eq_canonicalLaw_iff ν π (canonicalLaw ν π n) measurable_id).1 Measure.map_id t

/-- Uniqueness of the law (Proposition 4.8): two probability spaces whose histories satisfy
conditions (a) and (b) give the histories the same law. -/
example {k : ℕ} [NeZero k] (ν : StochasticBandit k) (π : Policy k) (n : ℕ)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {H : Ω → History k n}
    {H' : Ω' → History k n} (hH : Measurable H) (hH' : Measurable H')
    (hP : ∀ t : Fin n,
      condDistrib (fun ω ↦ (H ω t).1) (fun ω ↦ Fin.take t t.isLt.le (H ω)) P
          =ᵐ[P.map fun ω ↦ Fin.take t t.isLt.le (H ω)] π.kernel t ∧
        condDistrib (fun ω ↦ (H ω t).2) (fun ω ↦ (Fin.take t t.isLt.le (H ω), (H ω t).1)) P
          =ᵐ[P.map fun ω ↦ (Fin.take t t.isLt.le (H ω), (H ω t).1)] ν.rewardKernel t)
    (hP' : ∀ t : Fin n,
      condDistrib (fun ω ↦ (H' ω t).1) (fun ω ↦ Fin.take t t.isLt.le (H' ω)) P'
          =ᵐ[P'.map fun ω ↦ Fin.take t t.isLt.le (H' ω)] π.kernel t ∧
        condDistrib (fun ω ↦ (H' ω t).2) (fun ω ↦ (Fin.take t t.isLt.le (H' ω), (H' ω t).1)) P'
          =ᵐ[P'.map fun ω ↦ (Fin.take t t.isLt.le (H' ω), (H' ω t).1)] ν.rewardKernel t) :
    P.map H = P'.map H' :=
  ((map_eq_canonicalLaw_iff ν π P hH).2 hP).trans ((map_eq_canonicalLaw_iff ν π P' hH').2 hP').symm

/-! ## Arms with one common reward law -/

/-- When every arm has the same reward law, every policy has zero regret. -/
example {k : ℕ} [NeZero k] (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Integrable (fun x ↦ x) Q) (π : Policy k) (n : ℕ) :
    regret ⟨fun _ ↦ Q, fun _ ↦ inferInstance⟩ π n = 0 := by
  set ν : StochasticBandit k := ⟨fun _ ↦ Q, fun _ ↦ inferInstance⟩
  have hν : ν.HasFiniteMeans := fun _ ↦ hQ
  have hmean : ν.mean = fun _ ↦ ∫ x, x ∂Q := rfl
  rw [regret, integral_finsetSum _ fun t _ ↦ integrable_reward ν π hν t]
  simp [integral_reward ν π hν, StochasticBandit.maxMean, hmean]

/-! ## A bandit without finite means -/

/-- A two-armed bandit with standard Cauchy rewards, which have no finite mean (a classical fact,
not proved here). The model makes no moment assumption: the canonical law is defined and is a
probability measure, and the characterization by conditions (a) and (b) applies. -/
noncomputable def cauchyBandit : StochasticBandit 2 where
  law _ := cauchyMeasure 0 1
  isProbabilityMeasure_law _ := inferInstance

example (π : Policy 2) (n : ℕ) : IsProbabilityMeasure (canonicalLaw cauchyBandit π n) :=
  inferInstance

example (π : Policy 2) (n : ℕ) (t : Fin n) :
    condDistrib (fun h : History 2 n ↦ (h t).2) (fun h ↦ (Fin.take t t.isLt.le h, (h t).1))
        (canonicalLaw cauchyBandit π n)
      =ᵐ[(canonicalLaw cauchyBandit π n).map fun h ↦ (Fin.take t t.isLt.le h, (h t).1)]
        cauchyBandit.rewardKernel t :=
  ((map_eq_canonicalLaw_iff cauchyBandit π (canonicalLaw cauchyBandit π n) measurable_id).1
    Measure.map_id t).2

end CSLibExtTest.MachineLearning.Bandit
