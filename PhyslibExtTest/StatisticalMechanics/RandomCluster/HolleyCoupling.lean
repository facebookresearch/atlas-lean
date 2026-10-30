/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.HolleyCoupling

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.HolleyCoupling`

On the two-coordinate space `ConfigSpace (Fin 2)`, with the Bernoulli product mass functions
`bern (1/4)` and `bern (3/4)` (each coordinate open with probability `1/4` resp. `3/4`):
* `measOfMass` gives the expected values on the event "coordinate `0` open" and is a
  probability measure;
* the Holley lattice condition holds for the pair `(bern (1/4), bern (3/4))`, both mass functions
  are strictly positive everywhere and normalized;
* `holley_stochasticallyDominated` applies and yields `1/4 ≤ 3/4` on the event
  "coordinate `0` open";
* `holley_exists_monotoneCoupling` applies and yields a monotone coupling `κ`, whose
  marginals and order support are read off.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.HolleyCoupling

open MeasureTheory _root_.StatMech _root_.StatMech.FK

/-- The Bernoulli product mass function on two coordinates: each coordinate is open with
probability `a`, independently. -/
noncomputable def bern (a : ℝ) (ω : ConfigSpace (Fin 2)) : ℝ :=
  (if ω 0 then a else 1 - a) * (if ω 1 then a else 1 - a)

/-- The Bernoulli product mass function is nonnegative for `a ∈ [0, 1]`. -/
theorem bern_nonneg {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : 0 ≤ bern a := fun ω => by
  unfold bern
  apply mul_nonneg <;> split <;> linarith

/-- The Bernoulli product mass function is strictly positive everywhere for `a ∈ (0, 1)`. -/
theorem bern_pos_apply {a : ℝ} (h0 : 0 < a) (h1 : a < 1) (ω : ConfigSpace (Fin 2)) :
    0 < bern a ω := by
  unfold bern
  apply mul_pos <;> split <;> linarith

/-- The total mass of `bern a` is `1`. -/
theorem bern_sum (a : ℝ) : ∑ ω, bern a ω = 1 := by
  have h := (Fintype.prod_sum (fun (_ : Fin 2) (b : Bool) => if b then a else 1 - a)).symm
  simp only [bern, Fin.prod_univ_two] at h ⊢
  rw [h]
  simp

/-- The Holley lattice condition for the pair `(bern (1/4), bern (3/4))`. -/
theorem bern_holley (a b : ConfigSpace (Fin 2)) :
    bern (1 / 4) a * bern (3 / 4) b ≤ bern (1 / 4) (a ⊓ b) * bern (3 / 4) (a ⊔ b) := by
  simp only [bern, Pi.inf_apply, Pi.sup_apply]
  rcases Bool.eq_false_or_eq_true (a 0) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (a 1) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (b 0) with h2 | h2 <;>
  rcases Bool.eq_false_or_eq_true (b 1) with h3 | h3 <;>
  norm_num [h0, h1, h2, h3]

/-- The event "coordinate `0` is open". -/
def open0 : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

/-- `open0` is increasing. -/
theorem isIncreasing_open0 : IsIncreasing open0 := by
  intro x y hxy hx
  have h := hxy 0
  simp only [open0, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

/-- The mass of `open0` under `bern a` is `a`. -/
theorem bern_real_open0 {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    (measOfMass (bern a)).real open0 = a := by
  classical
  rw [measOfMass_real _ (bern_nonneg h0 h1)]
  have h := (Fintype.prod_sum
    (fun (i : Fin 2) (c : Bool) => if i = 0 then (if c then a else 0)
      else (if c then a else 1 - a))).symm
  simp only [Fin.prod_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero] at h
  have hsum : (∑ ω : ConfigSpace (Fin 2), if ω ∈ open0 then bern a ω else 0)
      = ∑ ω : ConfigSpace (Fin 2), (if ω 0 then a else 0) * (if ω 1 then a else 1 - a) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [open0, Set.mem_ofPred_eq, bern]
    rcases Bool.eq_false_or_eq_true (ω 0) with h | h <;> simp [h]
  rw [hsum, h]
  simp

-- `measOfMass (bern a)` is a probability measure.
example : IsProbabilityMeasure (measOfMass (bern (1 / 4))) :=
  measOfMass_isProbabilityMeasure _ (bern_nonneg (by norm_num) (by norm_num)) (bern_sum _)

-- `measOfMass` evaluates the event "coordinate `0` open" to its Bernoulli probability.
example : (measOfMass (bern (3 / 4))).real open0 = 3 / 4 :=
  bern_real_open0 (by norm_num) (by norm_num)

/-- Holley's inequality: `bern (1/4)` is stochastically dominated by `bern (3/4)`. -/
theorem bern_dominated : measOfMass (bern (1 / 4)) ≼ measOfMass (bern (3 / 4)) :=
  holley_stochasticallyDominated (bern_nonneg (by norm_num) (by norm_num))
    (bern_nonneg (by norm_num) (by norm_num)) (by rw [bern_sum, bern_sum]) bern_holley

-- Applied to "coordinate `0` open", the domination is the inequality `1/4 ≤ 3/4`.
example : (measOfMass (bern (1 / 4))).real open0 ≤ (measOfMass (bern (3 / 4))).real open0 :=
  bern_dominated open0 (DiscreteMeasurableSpace.forall_measurableSet _) isIncreasing_open0

-- Holley's coupling theorem: there is a monotone coupling of `bern (1/4)` and `bern (3/4)`;
-- its marginals are the two measures and it gives no mass to unordered pairs.
example : ∃ κ : Measure (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)),
    IsFiniteMeasure κ ∧ κ.fst = measOfMass (bern (1 / 4)) ∧
      κ.snd = measOfMass (bern (3 / 4)) ∧ κ (orderSet (Fin 2))ᶜ = 0 := by
  obtain ⟨κ, hfin, hκ⟩ := holley_exists_monotoneCoupling (μ₁ := bern (1 / 4))
    (μ₂ := bern (3 / 4))
    (lt_of_le_of_ne (bern_nonneg (by norm_num) (by norm_num))
      (fun h => (bern_pos_apply (a := 1 / 4) (by norm_num) (by norm_num) 0).ne
        (congrFun h 0)))
    (lt_of_le_of_ne (bern_nonneg (by norm_num) (by norm_num))
      (fun h => (bern_pos_apply (a := 3 / 4) (by norm_num) (by norm_num) 0).ne
        (congrFun h 0)))
    (bern_sum _) (bern_sum _) bern_holley
  exact ⟨κ, hfin, hκ.fst_eq, hκ.snd_eq, hκ.supported⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.HolleyCoupling
