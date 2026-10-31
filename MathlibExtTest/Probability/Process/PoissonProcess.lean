/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.PoissonProcess

public import Mathlib.Probability.ProductMeasure

import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open MeasureTheory ProbabilityTheory ProbabilityTheory.PoissonProcess
open scoped NNReal ENNReal

namespace MathlibExtTest.Probability.Process.PoissonProcess

/-! ### Definitions unfold as expected -/

/-- No arrival has happened before the first interarrival time. -/
example {Ω : Type*} (T : ℕ → Ω → ℝ) (ω : Ω) : arrivalTime T 0 ω = 0 := by
  simp [arrivalTime]

example {Ω : Type*} (T : ℕ → Ω → ℝ) (ω : Ω) : arrivalTime T 2 ω = T 0 ω + T 1 ω := by
  simp [arrivalTime, Finset.sum_range_succ]

/-- With interarrival times all equal to `1`, the arrival times are `1, 2, 3, …`, so two arrivals
lie in `[0, 2.5]`. -/
example : count (fun _ (_ : Unit) ↦ (1 : ℝ)) (5 / 2) () = 2 := by
  have h : {n : ℕ | arrivalTime (fun _ (_ : Unit) ↦ (1 : ℝ)) (n + 1) () ≤ ((5 / 2 : ℝ≥0) : ℝ)}
      = {0, 1} := by
    ext n
    simp only [arrivalTime, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    push_cast
    constructor
    · intro hn
      have : (n : ℝ) < 2 := by linarith
      have : n < 2 := by exact_mod_cast this
      omega
    · rintro (rfl | rfl) <;> norm_num
  rw [count, h, Set.ncard_pair (by norm_num)]

/-- The thinning by marks that are all `false` keeps nothing. -/
example {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (t : ℝ≥0) (ω : Ω) :
    thinning N (fun _ _ ↦ false) t ω = 0 := by
  simp [thinning]

/-- The thinning by marks that are all `true` keeps everything. -/
example {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (t : ℝ≥0) (ω : Ω) :
    thinning N (fun _ _ ↦ true) t ω = N t ω := by
  simp [thinning]

/-! ### Non-vacuity of `IsPoissonProcess` -/

/-- The Poisson law of mean `0` is the point mass at `0`. -/
theorem poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  ext s hs
  rw [poissonMeasure, Measure.sum_apply _ hs, Measure.dirac_apply' _ hs,
    tsum_eq_single 0 fun i hi ↦ by simp [zero_pow hi]]
  by_cases h : 0 ∈ s <;> simp [h]

/-- Boundary case: the zero process is a Poisson process of rate `0` (on the one-point probability
space). The witness of positive rate is `isPoissonProcess_expCount` below. -/
theorem isPoissonProcess_zero : IsPoissonProcess (fun _ _ ↦ (0 : ℕ)) 0 (Measure.dirac ()) where
  ae_zero := by simp
  ae_monotone := by simp [monotone_const]
  hasIndepIncrements := by
    intro n t _
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets _
    classical
    simp only [Measure.dirac_apply, Set.indicator, Pi.one_apply]
    rw [Finset.prod_boole]
    simp only [Set.mem_iInter]
    congr
  hasLaw_sub := by
    intro s t _
    refine ⟨aemeasurable_const, ?_⟩
    simp [poissonMeasure_zero]

/-! ### The exponential counting process on a concrete probability space -/

/-- The coordinates of the infinite product of rate-`2` exponential laws are i.i.d. rate-`2`
exponential. -/
theorem expCoord_hasLaw (i : ℕ) :
    HasLaw (fun ω : ℕ → ℝ ↦ ω i) (expMeasure ((2 : ℝ≥0) : ℝ))
      (Measure.infinitePi fun _ : ℕ ↦ expMeasure 2) := by
  have : IsProbabilityMeasure (expMeasure 2) := isProbabilityMeasure_expMeasure (by norm_num)
  exact ⟨(measurable_pi_apply i).aemeasurable, by
    simpa using Measure.infinitePi_map_eval (fun _ : ℕ ↦ expMeasure 2) i⟩

/-- The coordinates of the infinite product of rate-`2` exponential laws are independent. -/
theorem expCoord_iIndepFun :
    iIndepFun (fun (i : ℕ) (ω : ℕ → ℝ) ↦ ω i) (Measure.infinitePi fun _ : ℕ ↦ expMeasure 2) := by
  have : IsProbabilityMeasure (expMeasure 2) := isProbabilityMeasure_expMeasure (by norm_num)
  exact iIndepFun_infinitePi (X := fun _ (x : ℝ) ↦ x) fun _ ↦ measurable_id

/-- **Non-vacuity of `IsPoissonProcess` at positive rate**: on the infinite product of rate-`2`
exponential laws, the coordinate counting process is a Poisson process of rate `2`. -/
theorem isPoissonProcess_expCount :
    IsPoissonProcess (count fun (i : ℕ) (ω : ℕ → ℝ) ↦ ω i) 2
      (Measure.infinitePi fun _ : ℕ ↦ expMeasure 2) :=
  isPoissonProcess_count (by norm_num) expCoord_hasLaw expCoord_iIndepFun

/-- In particular `N t ~ Poisson(2 t)`. -/
example (t : ℝ≥0) :
    HasLaw (count (fun (i : ℕ) (ω : ℕ → ℝ) ↦ ω i) t) (poissonMeasure (2 * t))
      (Measure.infinitePi fun _ : ℕ ↦ expMeasure 2) :=
  hasLaw_count (by norm_num) expCoord_hasLaw expCoord_iIndepFun t

/-- The probability of no arrival in `(1, 3]` is `e^{-4}`. -/
example :
    (Measure.infinitePi fun _ : ℕ ↦ expMeasure 2)
        {ω | count (fun (i : ℕ) (ω : ℕ → ℝ) ↦ ω i) 3 ω -
          count (fun (i : ℕ) (ω : ℕ → ℝ) ↦ ω i) 1 ω = 0} =
      ENNReal.ofReal (Real.exp (-4)) := by
  have h := (isPoissonProcess_expCount.hasLaw_sub (show (1 : ℝ≥0) ≤ 3 by norm_num)).measure_eq
    (p := fun k : ℕ ↦ k = 0) (MeasurableSet.of_discrete)
  have h31 : (3 : ℝ≥0) - 1 = 2 := tsub_eq_of_eq_add (by norm_num)
  rw [Set.ofPred_eq_eq_singleton, poissonMeasure_singleton, h31] at h
  rw [h]
  norm_num

/-- The increments over `(0, 1]` and `(1, 3]` are independent with laws `Poisson(2)` and
`Poisson(4)`. -/
example :
    HasLaw (fun ω (i : Fin 2) ↦ count (fun (i : ℕ) (ω : ℕ → ℝ) ↦ ω i) (![0, 1, 3] i.succ) ω -
        count (fun (i : ℕ) (ω : ℕ → ℝ) ↦ ω i) (![0, 1, 3] i.castSucc) ω)
      (Measure.pi ![poissonMeasure 2, poissonMeasure 4])
      (Measure.infinitePi fun _ : ℕ ↦ expMeasure 2) := by
  have hmono : Monotone (![0, 1, 3] : Fin 3 → ℝ≥0) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  convert hasLaw_count_increments (by norm_num) expCoord_hasLaw expCoord_iIndepFun 2 _ hmono
    using 2
  have h31 : (3 : ℝ≥0) - 1 = 2 := tsub_eq_of_eq_add (by norm_num)
  funext i
  fin_cases i
  · simp
  · simp [h31]
    norm_num

/-! ### Superposition and thinning instances -/

/-- Superposing two independent rate-`1` processes gives rate `2`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {N₁ N₂ : ℝ≥0 → Ω → ℕ}
    (h₁ : IsPoissonProcess N₁ 1 P) (h₂ : IsPoissonProcess N₂ 1 P)
    (hind : IndepFun (fun ω t ↦ N₁ t ω) (fun ω t ↦ N₂ t ω) P) :
    IsPoissonProcess (N₁ + N₂) 2 P := by
  simpa [one_add_one_eq_two] using h₁.add h₂ hind

/-- Keeping each point with probability `1 / 2` halves the rate. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℝ≥0 → Ω → ℕ} {B : ℕ → Ω → Bool} (h : IsPoissonProcess N 2 P)
    (hBm : ∀ i, Measurable (B i)) (hB : ∀ i, P.real {ω | B i ω = true} = (1 / 2 : ℝ≥0))
    (hBind : iIndepFun B P) (hNB : IndepFun (fun ω t ↦ N t ω) (fun ω i ↦ B i ω) P) :
    IsPoissonProcess (thinning N B) 1 P := by
  have := h.thinning (by norm_num) hBm hB hBind hNB
  rwa [show (1 / 2 : ℝ≥0) * 2 = 1 by norm_num] at this

/-- Boundary case `p = 0`: the thinned process is a rate-`0` process. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℝ≥0 → Ω → ℕ} {r : ℝ≥0} {B : ℕ → Ω → Bool} (h : IsPoissonProcess N r P)
    (hBm : ∀ i, Measurable (B i)) (hB : ∀ i, P.real {ω | B i ω = true} = (0 : ℝ≥0))
    (hBind : iIndepFun B P) (hNB : IndepFun (fun ω t ↦ N t ω) (fun ω i ↦ B i ω) P) :
    IsPoissonProcess (thinning N B) 0 P := by
  simpa using h.thinning (zero_le_one' ℝ≥0) hBm hB hBind hNB

/-- The increment from time `0` is Poisson of mean `r t`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ} {r : ℝ≥0}
    (h : IsPoissonProcess N r P) (t : ℝ≥0) :
    HasLaw (fun ω ↦ N t ω - N 0 ω) (poissonMeasure (r * t)) P := by
  simpa using h.hasLaw_sub (bot_le : (0 : ℝ≥0) ≤ t)

end MathlibExtTest.Probability.Process.PoissonProcess
