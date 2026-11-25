/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Probability.Causality.ConfoundingStandardization

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MathlibExt.Probability.Causality
open MathlibExt.Probability.Causality.FiniteRiskModel

namespace ConfoundingRevalidation

noncomputable section

local instance (priority := 10) (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def simplex {α : Type*} [Fintype α] (f : α → ℝ)
    (hn : ∀ a, 0 ≤ f a) (hs : ∑ a, f a = 1) : Convexity.StdSimplex ℝ α where
  weights := Finsupp.equivFunOnFinite.symm f
  nonneg := by intro a; exact hn a
  total := by rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]; exact hs

noncomputable def finiteLaw {α : Type*} [Fintype α] [MeasurableSpace α]
    (w : α → ℝ) : Measure α := ∑ a, ENNReal.ofReal (w a) • Measure.dirac a

theorem finiteLaw_apply {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (w : α → ℝ) (hn : ∀ a, 0 ≤ w a) (S : Set α) :
    finiteLaw w S = ENNReal.ofReal (∑ a, if a ∈ S then w a else 0) := by
  classical
  rw [finiteLaw, Measure.finsetSum_apply, ENNReal.ofReal_sum_of_nonneg
    (fun a _ => by split_ifs <;> simp [hn a])]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : a ∈ S <;> simp [Measure.smul_apply, Measure.dirac_apply, Set.indicator, h]

theorem finiteLaw_real {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (w : α → ℝ) (hn : ∀ a, 0 ≤ w a) (S : Set α) :
    (finiteLaw w).real S = ∑ a, if a ∈ S then w a else 0 := by
  classical
  rw [Measure.real, finiteLaw_apply w hn, ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg fun a _ => by split_ifs <;> simp [hn a]

theorem finiteLaw_probability {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (w : α → ℝ) (hn : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) : IsProbabilityMeasure (finiteLaw w) := by
  constructor
  simp [finiteLaw_apply w hn, hs]

abbrev JointAtom (n : ℕ) := Bool × Fin (n + 1) × Bool

def exposure {n : ℕ} : Set (JointAtom n) := {a | a.1 = true}
def outcome {n : ℕ} : Set (JointAtom n) := {a | a.2.2 = true}
def confounder {n : ℕ} (a : JointAtom n) : Fin (n + 1) := a.2.1

noncomputable def jointLaw {n : ℕ} (m : FiniteRiskModel n) : Measure (JointAtom n) :=
  finiteLaw fun a => m.jointMass a.1 a.2.1 a.2.2

instance jointLaw_probability {n : ℕ} (m : FiniteRiskModel n) :
    IsProbabilityMeasure (jointLaw m) :=
  finiteLaw_probability _ (fun a => m.jointMass_nonneg a.1 a.2.1 a.2.2)
    (by simpa only [Fintype.sum_prod_type] using m.jointMass_sum)

theorem jointLaw_hasJointLaw {n : ℕ} (m : FiniteRiskModel n) :
    m.HasJointLaw (jointLaw m) exposure outcome confounder := by
  classical
  intro e u d
  have hset : binaryEvent exposure e ∩ confounder ⁻¹' {u} ∩ binaryEvent outcome d =
      ({(e, u, d)} : Set (JointAtom n)) := by
    ext ⟨e', u', d'⟩
    cases e <;> cases e' <;> cases d <;> cases d' <;>
      simp only [binaryEvent, exposure, outcome, confounder, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
        not_false_eq_true, not_true_eq_false, and_true, true_and, and_false, false_and]
  rw [hset]
  unfold jointLaw
  rw [finiteLaw_real (fun a : JointAtom n => m.jointMass a.1 a.2.1 a.2.2)
    (fun a => m.jointMass_nonneg a.1 a.2.1 a.2.2)]
  simp

noncomputable def positiveModel : FiniteRiskModel 1 where
  exposureProb := 1 / 2
  exposureProb_mem := by norm_num
  confounderLaw e := simplex (fun u => if e then (if u = 0 then 1 / 5 else 4 / 5)
      else (if u = 0 then 3 / 5 else 2 / 5))
    (by intro u; cases e <;> fin_cases u <;> norm_num)
    (by cases e <;> norm_num [Fin.sum_univ_succ])
  control_mass_pos := by intro u; fin_cases u <;> norm_num [simplex]
  risk e u := if e then (if u = 0 then 1 / 5 else 3 / 5)
    else (if u = 0 then 1 / 10 else 3 / 10)
  risk_mem := by intro e u; cases e <;> fin_cases u <;> norm_num

abbrev μ := jointLaw positiveModel

theorem marginal_client : μ.real (confounder ⁻¹' {0}) = 2 / 5 ∧
    μ.real (confounder ⁻¹' {1}) = 3 / 5 := by
  constructor
  · rw [← marginalMass_eq_measureReal MeasurableSet.of_discrete MeasurableSet.of_discrete
      (measurable_of_finite confounder) (jointLaw_hasJointLaw positiveModel)]
    norm_num [marginalMass, mass, positiveModel, simplex]
  · rw [← marginalMass_eq_measureReal MeasurableSet.of_discrete MeasurableSet.of_discrete
      (measurable_of_finite confounder) (jointLaw_hasJointLaw positiveModel)]
    norm_num [marginalMass, mass, positiveModel, simplex]

theorem arm_client (e : Bool) : μ.real (binaryEvent exposure e) = 1 / 2 := by
  rw [← armProb_eq_measureReal MeasurableSet.of_discrete MeasurableSet.of_discrete
    (measurable_of_finite confounder) (jointLaw_hasJointLaw positiveModel)]
  cases e <;> norm_num [armProb, positiveModel]

theorem mass_client (e : Bool) (u : Fin 2) :
    (μ[|binaryEvent exposure e]).real (confounder ⁻¹' {u}) =
      if e then (if u = 0 then 1 / 5 else 4 / 5)
      else (if u = 0 then 3 / 5 else 2 / 5) := by
  rw [← mass_eq_cond MeasurableSet.of_discrete MeasurableSet.of_discrete
    (measurable_of_finite confounder) (jointLaw_hasJointLaw positiveModel)]
  rfl

theorem risk_client (e : Bool) (u : Fin 2) :
    (μ[|binaryEvent exposure e ∩ confounder ⁻¹' {u}]).real outcome =
      if e then (if u = 0 then 1 / 5 else 3 / 5)
      else (if u = 0 then 1 / 10 else 3 / 10) := by
  rw [← risk_eq_cond MeasurableSet.of_discrete MeasurableSet.of_discrete
    (measurable_of_finite confounder) (jointLaw_hasJointLaw positiveModel) e u
    (by cases e <;> fin_cases u <;> norm_num [mass, positiveModel, simplex])]
  rfl

theorem observedRisk_client (e : Bool) :
    (μ[|binaryEvent exposure e]).real outcome = if e then 13 / 25 else 9 / 50 := by
  rw [← observedRisk_eq_cond MeasurableSet.of_discrete MeasurableSet.of_discrete
    (measurable_of_finite confounder) (jointLaw_hasJointLaw positiveModel)]
  cases e <;> norm_num [observedRisk, Fin.sum_univ_succ, mass, positiveModel, simplex]

theorem observedRR_client :
    (μ[|exposure]).real outcome / (μ[|exposureᶜ]).real outcome = 26 / 9 := by
  rw [← observedRR_eq_cond_ratio MeasurableSet.of_discrete MeasurableSet.of_discrete
    (measurable_of_finite confounder) (jointLaw_hasJointLaw positiveModel)]
  norm_num [observedRR, observedRisk, Fin.sum_univ_succ, mass, positiveModel, simplex]

theorem standardizedRisk_client (e : Bool) :
    (∑ u : Fin 2, μ.real (confounder ⁻¹' {u}) *
      (if μ (binaryEvent exposure e ∩ confounder ⁻¹' {u}) = 0
       then positiveModel.risk e u
       else (μ[|binaryEvent exposure e ∩ confounder ⁻¹' {u}]).real outcome)) =
      if e then 11 / 25 else 11 / 50 := by
  rw [← standardizedRisk_eq_sum_cond MeasurableSet.of_discrete MeasurableSet.of_discrete
    (measurable_of_finite confounder) (jointLaw_hasJointLaw positiveModel) e]
  cases e <;> norm_num [standardizedRisk, marginalMass, mass, Fin.sum_univ_succ,
    positiveModel, simplex]


theorem jointLaw_real {n : ℕ} (m : FiniteRiskModel n) (S : Set (JointAtom n)) :
    (jointLaw m).real S = ∑ e, ∑ u, ∑ d, if (e, u, d) ∈ S then m.jointMass e u d else 0 := by
  rw [jointLaw, finiteLaw_real (fun a : JointAtom n => m.jointMass a.1 a.2.1 a.2.2)
    (fun a => m.jointMass_nonneg a.1 a.2.1 a.2.2)]
  simp only [Fintype.sum_prod_type]

theorem positive_atoms (e : Bool) (u : Fin 2) (d : Bool) :
    μ.real (binaryEvent exposure e ∩ confounder ⁻¹' {u} ∩ binaryEvent outcome d) =
      if e then (if u = 0 then (if d then 1 / 50 else 2 / 25)
        else (if d then 6 / 25 else 4 / 25))
      else (if u = 0 then (if d then 3 / 100 else 27 / 100)
        else (if d then 3 / 50 else 7 / 50)) := by
  rw [jointLaw_hasJointLaw positiveModel]
  cases e <;> fin_cases u <;> cases d <;>
    norm_num [jointMass, armProb, mass, positiveModel, simplex]

noncomputable def mutatedModel : FiniteRiskModel 1 :=
  { positiveModel with
    risk := fun e u => if e then (if u = 0 then 1 / 5 else 3 / 5)
      else (if u = 0 then 1 / 5 else 3 / 10)
    risk_mem := by intro e u; cases e <;> fin_cases u <;> norm_num }

theorem mutation_refuted : ¬ mutatedModel.HasJointLaw μ exposure outcome confounder := by
  intro h
  have ha := h false 0 true
  rw [positive_atoms] at ha
  norm_num [mutatedModel, jointMass, armProb, mass, positiveModel, simplex] at ha

noncomputable def nullModel (version : Bool) : FiniteRiskModel 1 where
  exposureProb := 1 / 2
  exposureProb_mem := by norm_num
  confounderLaw e := simplex (fun u => if e then (if u = 0 then 0 else 1) else 1 / 2)
    (by intro u; cases e <;> fin_cases u <;> norm_num)
    (by cases e <;> norm_num [Fin.sum_univ_succ])
  control_mass_pos := by intro u; norm_num [simplex]
  risk e u := if u = 0 then (if e && version then 3 / 4 else 1 / 4) else 1 / 2
  risk_mem := by intro e u; cases e <;> cases version <;> fin_cases u <;> norm_num

abbrev ν := jointLaw (nullModel false)

theorem nullLaw_same : jointLaw (nullModel true) = ν := by
  unfold jointLaw
  congr 1
  funext ⟨e, u, d⟩
  cases e <;> fin_cases u <;> cases d <;>
    norm_num [jointMass, armProb, mass, nullModel, simplex]

theorem null_hasJointLaw (version : Bool) :
    (nullModel version).HasJointLaw ν exposure outcome confounder := by
  cases version
  · exact jointLaw_hasJointLaw _
  · rw [← nullLaw_same]
    exact jointLaw_hasJointLaw _

theorem null_cell : ν (exposure ∩ confounder ⁻¹' {0}) = 0 := by
  apply (measureReal_eq_zero_iff).mp
  rw [jointLaw_real]
  norm_num [Fintype.sum_bool, Fin.sum_univ_succ, exposure, confounder,
    jointMass, armProb, mass, nullModel, simplex]

theorem null_marginal : ν.real (confounder ⁻¹' {0}) = 1 / 4 := by
  rw [← marginalMass_eq_measureReal MeasurableSet.of_discrete MeasurableSet.of_discrete
    (measurable_of_finite confounder) (null_hasJointLaw false)]
  norm_num [marginalMass, mass, nullModel, simplex]

theorem null_positivity_fails (version : Bool) : ¬ 0 < (nullModel version).mass true 0 := by
  norm_num [mass, nullModel, simplex]

theorem null_positive_risk_client (version : Bool) :
    (ν[|exposure ∩ confounder ⁻¹' {1}]).real outcome = 1 / 2 := by
  have h := risk_eq_cond MeasurableSet.of_discrete MeasurableSet.of_discrete
    (measurable_of_finite confounder) (null_hasJointLaw version) true 1
    (by norm_num [mass, nullModel, simplex])
  simpa [binaryEvent, nullModel] using h.symm

theorem null_standardization_client (version : Bool) :
    (∑ u : Fin 2, ν.real (confounder ⁻¹' {u}) *
      (if ν (binaryEvent exposure true ∩ confounder ⁻¹' {u}) = 0
       then (nullModel version).risk true u
       else (ν[|binaryEvent exposure true ∩ confounder ⁻¹' {u}]).real outcome)) =
      if version then 9 / 16 else 7 / 16 := by
  rw [← standardizedRisk_eq_sum_cond MeasurableSet.of_discrete MeasurableSet.of_discrete
    (measurable_of_finite confounder) (null_hasJointLaw version) true]
  cases version <;> norm_num [standardizedRisk, marginalMass, mass, Fin.sum_univ_succ,
    nullModel, simplex]

theorem null_kernel_branch (version : Bool) :
    (if ν (binaryEvent exposure true ∩ confounder ⁻¹' {0}) = 0
     then (nullModel version).risk true 0
     else (ν[|binaryEvent exposure true ∩ confounder ⁻¹' {0}]).real outcome) =
      if version then 3 / 4 else 1 / 4 := by
  simp [binaryEvent, null_cell, nullModel]


abbrev CausalAtom := Bool × Fin 2 × Bool × Bool

def bit (b : Bool) : ℝ := if b then 1 else 0

def bern (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

noncomputable def causalWeight (a : CausalAtom) : ℝ :=
  positiveModel.armProb a.1 * positiveModel.mass a.1 a.2.1 *
    bern (positiveModel.risk false a.2.1) a.2.2.1 *
    bern (positiveModel.risk true a.2.1) a.2.2.2

theorem causalWeight_nonneg (a : CausalAtom) : 0 ≤ causalWeight a := by
  rcases a with ⟨e, u, y₀, y₁⟩
  cases e <;> fin_cases u <;> cases y₀ <;> cases y₁ <;>
    norm_num [causalWeight, bern, armProb, mass, positiveModel, simplex]

theorem causalWeight_total : ∑ a, causalWeight a = 1 := by
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ,
    causalWeight, bern, armProb, mass, positiveModel, simplex]

noncomputable def κ : Measure CausalAtom := finiteLaw causalWeight

instance causalLaw_probability : IsProbabilityMeasure κ :=
  finiteLaw_probability causalWeight causalWeight_nonneg causalWeight_total

def causalExposure : Set CausalAtom := {a | a.1 = true}
def causalConfounder (a : CausalAtom) : Fin 2 := a.2.1
def potentialControl (a : CausalAtom) : ℝ := bit a.2.2.1
def potentialTreated (a : CausalAtom) : ℝ := bit a.2.2.2

theorem potentialControl_binary (a : CausalAtom) :
    potentialControl a = 0 ∨ potentialControl a = 1 := by
  cases h : a.2.2.1 <;> simp [potentialControl, bit, h]

theorem potentialTreated_binary (a : CausalAtom) :
    potentialTreated a = 0 ∨ potentialTreated a = 1 := by
  cases h : a.2.2.2 <;> simp [potentialTreated, bit, h]

theorem causal_marginal (u : Fin 2) :
    κ.real (causalConfounder ⁻¹' {u}) = if u = 0 then 2 / 5 else 3 / 5 := by
  rw [κ, finiteLaw_real causalWeight causalWeight_nonneg]
  fin_cases u <;> norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ,
    causalConfounder, causalWeight, bern, armProb, mass, positiveModel, simplex]

theorem causal_treated_cell (u : Fin 2) :
    κ.real (causalExposure ∩ causalConfounder ⁻¹' {u}) =
      if u = 0 then 1 / 10 else 2 / 5 := by
  rw [κ, finiteLaw_real causalWeight causalWeight_nonneg]
  fin_cases u <;> norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ,
    causalExposure, causalConfounder, causalWeight, bern, armProb, mass, positiveModel, simplex]

theorem causal_propensity (u : Fin 2) :
    propensity κ causalExposure causalConfounder u = if u = 0 then 1 / 4 else 2 / 3 := by
  rw [propensity, causal_marginal, causal_treated_cell]
  fin_cases u <;> norm_num

noncomputable def pairWeight (B : Set (ℝ × ℝ)) (u : Fin 2) : ℝ :=
  ∑ y₀ : Bool, ∑ y₁ : Bool, if (bit y₀, bit y₁) ∈ B then
    bern (positiveModel.risk false u) y₀ * bern (positiveModel.risk true u) y₁ else 0

theorem treated_pair_factorization (B : Set (ℝ × ℝ)) (u : Fin 2) :
    κ.real (causalExposure ∩ (fun a => (potentialControl a, potentialTreated a)) ⁻¹' B ∩
      causalConfounder ⁻¹' {u}) =
      κ.real (causalExposure ∩ causalConfounder ⁻¹' {u}) * pairWeight B u := by
  rw [causal_treated_cell, κ, finiteLaw_real causalWeight causalWeight_nonneg]
  fin_cases u <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ, pairWeight,
      causalExposure, causalConfounder, potentialControl, potentialTreated, bit,
      causalWeight, bern, armProb, mass, positiveModel, simplex] <;>
    split_ifs <;> norm_num

theorem pair_factorization (B : Set (ℝ × ℝ)) (u : Fin 2) :
    κ.real ((fun a => (potentialControl a, potentialTreated a)) ⁻¹' B ∩
      causalConfounder ⁻¹' {u}) = κ.real (causalConfounder ⁻¹' {u}) * pairWeight B u := by
  rw [causal_marginal, κ, finiteLaw_real causalWeight causalWeight_nonneg]
  fin_cases u <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ, pairWeight,
      causalConfounder, potentialControl, potentialTreated, bit,
      causalWeight, bern, armProb, mass, positiveModel, simplex] <;>
    split_ifs <;> norm_num

theorem causal_ignorability : StronglyIgnorable κ causalExposure
    (fun a => (potentialControl a, potentialTreated a)) causalConfounder := by
  constructor
  · intro B _ u
    rw [treated_pair_factorization, pair_factorization]
    ring
  · intro u _
    rw [causal_propensity]
    fin_cases u <;> norm_num

theorem observed_consistency (a : CausalAtom) :
    observed causalExposure potentialControl potentialTreated a =
      if a.1 then bit a.2.2.2 else bit a.2.2.1 := by
  cases h : a.1
  · rw [observed_eq_on_control causalExposure potentialControl potentialTreated
      (by simp [causalExposure, h])]
    simp [potentialControl]
  · rw [observed_eq_on_treated causalExposure potentialControl potentialTreated
      (by simp [causalExposure, h])]
    simp [potentialTreated]

theorem causal_hasJointLaw : positiveModel.HasJointLaw κ causalExposure
    (observed causalExposure potentialControl potentialTreated ⁻¹' {1}) causalConfounder := by
  intro e u d
  rw [κ, finiteLaw_real causalWeight causalWeight_nonneg]
  cases e <;> fin_cases u <;> cases d <;>
    simp only [binaryEvent, ↓reduceIte, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, observed_consistency] <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ,
      binaryEvent, causalExposure, causalConfounder, bit,
      causalWeight, bern, jointMass, armProb, mass, positiveModel, simplex,
      observed, Set.indicator, potentialControl, potentialTreated]

theorem potential_risks : κ.real (potentialControl ⁻¹' {1}) = 11 / 50 ∧
    κ.real (potentialTreated ⁻¹' {1}) = 11 / 25 := by
  constructor <;> rw [κ, finiteLaw_real causalWeight causalWeight_nonneg] <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ,
      potentialControl, potentialTreated, bit, causalWeight, bern, armProb, mass,
      positiveModel, simplex]

theorem causalRR_client :
    κ.real (potentialTreated ⁻¹' {1}) / κ.real (potentialControl ⁻¹' {1}) = 2 := by
  rw [← standardizedRR_eq_causalRR MeasurableSet.of_discrete
    (measurable_of_finite causalConfounder) (measurable_of_finite potentialControl)
    (measurable_of_finite potentialTreated) potentialControl_binary potentialTreated_binary
    causal_ignorability causal_hasJointLaw]
  norm_num [standardizedRR, standardizedRisk, marginalMass, mass, Fin.sum_univ_succ,
    positiveModel, simplex]


theorem positive_risk_extrema (e : Bool) :
    Finset.univ.sup' Finset.univ_nonempty (positiveModel.risk e) =
      (if e then 3 / 5 else 3 / 10) ∧
    Finset.univ.inf' Finset.univ_nonempty (positiveModel.risk e) =
      (if e then 1 / 5 else 1 / 10) := by
  constructor
  · apply le_antisymm
    · apply Finset.sup'_le
      intro u _
      cases e <;> fin_cases u <;> norm_num [positiveModel]
    · convert Finset.le_sup' (positiveModel.risk e) (Finset.mem_univ (1 : Fin 2)) using 1
      cases e <;> norm_num [positiveModel]
  · apply le_antisymm
    · convert Finset.inf'_le (positiveModel.risk e) (Finset.mem_univ (0 : Fin 2)) using 1
      cases e <;> norm_num [positiveModel]
    · apply Finset.le_inf'
      intro u _
      cases e <;> fin_cases u <;> norm_num [positiveModel]

theorem positive_strengths : positiveModel.exposureConfounderRR = 2 ∧
    positiveModel.confounderOutcomeRR = 3 := by
  constructor
  · unfold exposureConfounderRR
    apply le_antisymm
    · apply Finset.sup'_le
      intro u _
      fin_cases u <;> norm_num [mass, positiveModel, simplex]
    · convert Finset.le_sup' (fun u => positiveModel.mass true u / positiveModel.mass false u)
        (Finset.mem_univ (1 : Fin 2)) using 1
      norm_num [mass, positiveModel, simplex]
  · have hArm (e : Bool) : positiveModel.armConfounderOutcomeRR e = 3 := by
      rw [armConfounderOutcomeRR, (positive_risk_extrema e).1, (positive_risk_extrema e).2]
      cases e <;> norm_num
    simp only [confounderOutcomeRR, hArm, max_self]

theorem confounding_bound_client : (13 : ℝ) / 9 ≤ 3 / 2 := by
  have h := confounding_causalRR_le_boundingFactor MeasurableSet.of_discrete
    (measurable_of_finite causalConfounder) (measurable_of_finite potentialControl)
    (measurable_of_finite potentialTreated) potentialControl_binary potentialTreated_binary
    causal_ignorability causal_hasJointLaw
  rw [potential_risks.1, potential_risks.2, positive_strengths.1, positive_strengths.2] at h
  convert h using 1 <;>
    norm_num [observedRR, observedRisk, Fin.sum_univ_succ, mass, positiveModel, simplex,
      confoundingBoundingFactor]

noncomputable def stratumModel (common : Bool) (c : Fin 2) : FiniteRiskModel 0 where
  exposureProb := 1 / 2
  exposureProb_mem := by norm_num
  confounderLaw _ := simplex (fun _ => 1) (fun _ => by norm_num)
    (by norm_num [Fin.sum_univ_succ])
  control_mass_pos := by intro u; norm_num [simplex]
  risk e _ := if e then (if common && c != 0 then 1 else 1 / 2)
    else (if c = 0 then 1 / 4 else 1 / 2)
  risk_mem := by intro e u; cases e <;> cases common <;> fin_cases c <;> norm_num

noncomputable def stratumWeights (zeroFirst : Bool) : Convexity.StdSimplex ℝ (Fin 2) :=
  simplex (fun c => if zeroFirst then (if c = 0 then 0 else 1) else 1 / 2)
    (by intro c; cases zeroFirst <;> fin_cases c <;> norm_num)
    (by cases zeroFirst <;> norm_num [Fin.sum_univ_succ])

theorem stratum_risks (common : Bool) (c : Fin 2) (e : Bool) :
    (stratumModel common c).standardizedRisk e =
      if e then (if common && c != 0 then 1 else 1 / 2)
      else (if c = 0 then 1 / 4 else 1 / 2) := by
  cases e <;> cases common <;> fin_cases c <;>
    norm_num [standardizedRisk, marginalMass, mass, Fin.sum_univ_succ, stratumModel, simplex]

theorem stratum_corrected (common : Bool) (c : Fin 2) :
    (stratumModel common c).observedRR /
      confoundingBoundingFactor (stratumModel common c).exposureConfounderRR
        (stratumModel common c).confounderOutcomeRR =
      if common || c == 0 then 2 else 1 := by
  cases common <;> fin_cases c <;>
    norm_num [observedRR, observedRisk, exposureConfounderRR, confounderOutcomeRR,
      armConfounderOutcomeRR, confoundingBoundingFactor, mass, Fin.sum_univ_succ,
      stratumModel, simplex, Fin.univ_succ]

theorem stratum_denominator_positive (common zeroFirst : Bool) :
    0 < ∑ c, (stratumWeights zeroFirst).weights c *
      (stratumModel common c).standardizedRisk false := by
  simp only [stratum_risks]
  cases zeroFirst <;> norm_num [stratumWeights, simplex, Fin.sum_univ_succ]

theorem stratum_aggregate (common zeroFirst : Bool) :
    strataStandardizedRR (stratumWeights zeroFirst) (stratumModel common) =
      if common then 2 else (if zeroFirst then 1 else 4 / 3) := by
  unfold strataStandardizedRR
  simp only [stratum_risks]
  cases common <;> cases zeroFirst <;>
    norm_num [stratumWeights, simplex, Fin.sum_univ_succ]

theorem corrected_minimum :
    Finset.univ.inf' Finset.univ_nonempty (fun c : Fin 2 =>
      (stratumModel false c).observedRR /
        confoundingBoundingFactor (stratumModel false c).exposureConfounderRR
          (stratumModel false c).confounderOutcomeRR) = 1 := by
  simp only [stratum_corrected]
  norm_num [Finset.univ_fin2, Finset.inf'_insert]

theorem strata_min_client (zeroFirst : Bool) :
    (1 : ℝ) ≤ if zeroFirst then 1 else 4 / 3 := by
  have h := strataStandardizedRR_ge_min (stratumWeights zeroFirst) (stratumModel false)
  rwa [corrected_minimum, stratum_aggregate] at h

theorem stratum_common (c : Fin 2) : (stratumModel true c).standardizedRR = 2 := by
  rw [standardizedRR, stratum_risks, stratum_risks]
  fin_cases c <;> norm_num

theorem corrected_maximum :
    Finset.univ.sup' Finset.univ_nonempty (fun c : Fin 2 =>
      (stratumModel true c).observedRR /
        confoundingBoundingFactor (stratumModel true c).exposureConfounderRR
          (stratumModel true c).confounderOutcomeRR) = 2 := by
  simp only [stratum_corrected]
  norm_num [Finset.univ_fin2, Finset.sup'_insert]

theorem strata_max_client (zeroFirst : Bool) : (2 : ℝ) ≤
    strataStandardizedRR (stratumWeights zeroFirst) (stratumModel true) := by
  have h := strataStandardizedRR_ge_max_of_common (stratumWeights zeroFirst)
    (stratumModel true) stratum_common
  rwa [corrected_maximum] at h

end

end ConfoundingRevalidation

#print axioms ConfoundingRevalidation.finiteLaw_apply
#print axioms ConfoundingRevalidation.finiteLaw_real
#print axioms ConfoundingRevalidation.finiteLaw_probability
#print axioms ConfoundingRevalidation.jointLaw_hasJointLaw
#print axioms ConfoundingRevalidation.marginal_client
#print axioms ConfoundingRevalidation.arm_client
#print axioms ConfoundingRevalidation.mass_client
#print axioms ConfoundingRevalidation.risk_client
#print axioms ConfoundingRevalidation.observedRisk_client
#print axioms ConfoundingRevalidation.observedRR_client
#print axioms ConfoundingRevalidation.standardizedRisk_client
#print axioms ConfoundingRevalidation.jointLaw_real
#print axioms ConfoundingRevalidation.positive_atoms
#print axioms ConfoundingRevalidation.mutation_refuted
#print axioms ConfoundingRevalidation.nullLaw_same
#print axioms ConfoundingRevalidation.null_hasJointLaw
#print axioms ConfoundingRevalidation.null_cell
#print axioms ConfoundingRevalidation.null_marginal
#print axioms ConfoundingRevalidation.null_positivity_fails
#print axioms ConfoundingRevalidation.null_positive_risk_client
#print axioms ConfoundingRevalidation.null_standardization_client
#print axioms ConfoundingRevalidation.null_kernel_branch
#print axioms ConfoundingRevalidation.causalWeight_nonneg
#print axioms ConfoundingRevalidation.causalWeight_total
#print axioms ConfoundingRevalidation.potentialControl_binary
#print axioms ConfoundingRevalidation.potentialTreated_binary
#print axioms ConfoundingRevalidation.causal_marginal
#print axioms ConfoundingRevalidation.causal_treated_cell
#print axioms ConfoundingRevalidation.causal_propensity
#print axioms ConfoundingRevalidation.treated_pair_factorization
#print axioms ConfoundingRevalidation.pair_factorization
#print axioms ConfoundingRevalidation.causal_ignorability
#print axioms ConfoundingRevalidation.observed_consistency
#print axioms ConfoundingRevalidation.causal_hasJointLaw
#print axioms ConfoundingRevalidation.potential_risks
#print axioms ConfoundingRevalidation.causalRR_client
#print axioms ConfoundingRevalidation.positive_risk_extrema
#print axioms ConfoundingRevalidation.positive_strengths
#print axioms ConfoundingRevalidation.confounding_bound_client
#print axioms ConfoundingRevalidation.stratum_risks
#print axioms ConfoundingRevalidation.stratum_corrected
#print axioms ConfoundingRevalidation.stratum_denominator_positive
#print axioms ConfoundingRevalidation.stratum_aggregate
#print axioms ConfoundingRevalidation.corrected_minimum
#print axioms ConfoundingRevalidation.strata_min_client
#print axioms ConfoundingRevalidation.stratum_common
#print axioms ConfoundingRevalidation.corrected_maximum
#print axioms ConfoundingRevalidation.strata_max_client
