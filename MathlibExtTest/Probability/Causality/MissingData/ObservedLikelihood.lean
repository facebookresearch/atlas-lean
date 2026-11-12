/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.MissingData.ObservedLikelihood
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Basic.ENNReal.Operations
import Mathlib.Basic.ENNReal.Inv

/-! # Boundary tests for observed-likelihood ignorability

One-variable (`Bool`) and two-variable (`Bool × Bool`) checks T1-T6 for
realized MAR: no missing data, all missing, MAR failure with flipped ordering,
complete-case bias, variation independence, and zero realized-pattern mass.
-/

@[expose] public section

open scoped ENNReal Topology BigOperators

namespace MathlibExtTest.Probability.Causality.MissingData.ObservedLikelihood

/-- One-variable observation: `true` observes `y`, `false` observes nothing. -/
def obsOne : Bool → Bool → Option Bool :=
  fun y m => if m then some y else none

/-- Point-mass full-data model: unit mass on `y = θ`. -/
def Fpoint :
    ProbabilityTheory.NormalizedDensityFamily Bool Bool
      MeasureTheory.Measure.count :=
  { dens := fun θ y => if y = θ then 1 else 0
    measurable := fun θ => (measurable_of_finite _).aemeasurable
    normalized := fun θ => by
      rw [MeasureTheory.lintegral_count, tsum_fintype, Fintype.sum_bool]
      cases θ
      · rw [ite_eq_left rfl,
          ite_eq_right (by decide : (true : Bool) ≠ false), zero_add]
      · rw [ite_eq_right (by decide : (false : Bool) ≠ true),
          ite_eq_left rfl, add_zero] }

/-- T2 response: constant pattern `false`, independent of `y`. -/
noncomputable def gT2 : Unit → Bool → PMF Bool :=
  fun _ _ => PMF.pure false

/-- T3 response: `y = true` uses `ψ`, `y = false` is fair. -/
noncomputable def gT3 : Bool → Bool → PMF Bool :=
  fun ψ y => if y then (if ψ then PMF.pure false else PMF.pure true)
    else PMF.ofFintype (fun _ => 2⁻¹) (by
      rw [Fintype.sum_bool]
      have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
      have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by simp
      have hc : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
        ENNReal.mul_inv_cancel h2ne0 h2netop
      calc (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 2 * 2⁻¹ := (two_mul _).symm
        _ = 1 := hc)

/-- Two-variable observation: always `x`, `v` only if `m`. -/
def obsTwo : (Bool × Bool) → Bool → (Bool × Option Bool) :=
  fun y m => (y.1, if m then some y.2 else none)

/-- T4 model: half mass on `(true, true)` and `(false, false)`. -/
noncomputable def Ftwo :
    ProbabilityTheory.NormalizedDensityFamily (Bool × Bool) Unit
      MeasureTheory.Measure.count :=
  { dens := fun _ y =>
      if y = (true, true) then 2⁻¹
      else if y = (false, false) then 2⁻¹ else 0
    measurable := fun _ => (measurable_of_finite _).aemeasurable
    normalized := fun _ => by
      rw [MeasureTheory.lintegral_count, tsum_fintype,
        Fintype.sum_prod_type]
      simp only [Fintype.sum_bool]
      have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
      have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by simp
      have hc : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
        ENNReal.mul_inv_cancel h2ne0 h2netop
      have hsum : (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 1 :=
        calc (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 2 * 2⁻¹ := (two_mul _).symm
          _ = 1 := hc
      simp [hsum, add_zero, zero_add] }

/-- T4 response: `true` with prob 1 if `x`, else fair. -/
noncomputable def gT4 : Unit → (Bool × Bool) → PMF Bool :=
  fun _ y => if y.1 then PMF.pure true
    else PMF.ofFintype (fun _ => 2⁻¹) (by
      rw [Fintype.sum_bool]
      have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
      have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by simp
      have hc : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
        ENNReal.mul_inv_cancel h2ne0 h2netop
      calc (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 2 * 2⁻¹ := (two_mul _).symm
        _ = 1 := hc)

/-- T5 model: uniform `2⁻¹` over `y` for every `θ`. -/
noncomputable def Fhalf :
    ProbabilityTheory.NormalizedDensityFamily Bool Bool
      MeasureTheory.Measure.count :=
  { dens := fun _ _ => 2⁻¹
    measurable := fun _ => (measurable_of_finite _).aemeasurable
    normalized := fun _ => by
      rw [MeasureTheory.lintegral_count, tsum_fintype, Fintype.sum_bool]
      have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
      have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by simp
      have hc : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
        ENNReal.mul_inv_cancel h2ne0 h2netop
      calc (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 2 * 2⁻¹ := (two_mul _).symm
        _ = 1 := hc }

/-- T5 response: fair pattern independent of `ψ` and `y`. -/
noncomputable def gT5 : Bool → Bool → PMF Bool :=
  fun _ _ => PMF.ofFintype (fun _ => 2⁻¹) (by
    rw [Fintype.sum_bool]
    have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
    have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by simp
    have hc : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
      ENNReal.mul_inv_cancel h2ne0 h2netop
    calc (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 2 * 2⁻¹ := (two_mul _).symm
      _ = 1 := hc)

/-- T6 response: pattern `false` always, so prob 0 of `true`. -/
noncomputable def gT6 : Unit → Bool → PMF Bool :=
  fun _ _ => PMF.pure false

/-- T1: with nothing missing, realized MAR holds for any response law. -/
theorem T1_marHolds {Ψ : Type} (g : Ψ → Bool → PMF Bool) :
    ∀ ψ y y', obsOne y true = obsOne true true →
      obsOne y' true = obsOne true true → g ψ y true = g ψ y' true := by
  intro ψ y y' h1 h2
  simp [obsOne] at h1 h2
  rw [h1, h2]

/-- T1: the ignorable likelihood equals the full-data likelihood. -/
theorem T1_likelihood (θ : Bool) :
    (∑' y, {y | obsOne y true = obsOne true true}.indicator
      (fun y => Fpoint.dens θ y) y) = Fpoint.dens θ true := by
  have hF : ∀ θ y, Fpoint.dens θ y =
      (if y = θ then (1 : ℝ≥0∞) else 0) := fun θ y => rfl
  rw [tsum_fintype, Fintype.sum_bool]
  have hm : (false : Bool) ∉ {y | obsOne y true = obsOne true true} := by
    decide
  have hp : (true : Bool) ∈ {y | obsOne y true = obsOne true true} :=
    rfl
  rw [Set.indicator_of_notMem hm, Set.indicator_of_mem hp, hF, add_zero]

/-- T2: a `y`-free response law satisfies realized MAR when all is missing. -/
theorem T2_marHolds :
    ∀ (ψ : Unit) (y y' : Bool), obsOne y false = obsOne true false →
      obsOne y' false = obsOne true false →
      gT2 ψ y false = gT2 ψ y' false := by
  intro ψ y y' _ _
  rfl

/-- T2: a completely missing observation carries no information. -/
theorem T2_likelihood (θ : Bool) :
    (∑' y, {y | obsOne y false = obsOne true false}.indicator
      (fun y => Fpoint.dens θ y) y) = 1 := by
  have hA : ∀ y : Bool, y ∈ {y | obsOne y false = obsOne true false} := by
    intro y
    simp [obsOne]
  have hF : ∀ θ y, Fpoint.dens θ y =
      (if y = θ then (1 : ℝ≥0∞) else 0) := fun θ y => rfl
  have htsum : ∀ y, {y | obsOne y false = obsOne true false}.indicator
      (fun y => Fpoint.dens θ y) y = Fpoint.dens θ y := by
    intro y
    exact Set.indicator_of_mem (hA y) _
  simp only [htsum]
  have hnorm := Fpoint.normalized θ
  rw [MeasureTheory.lintegral_count] at hnorm
  exact hnorm

/-- T3: missingness depending on the outcome violates realized MAR. -/
theorem T3_marFails :
    ¬ ∀ (ψ : Bool) (y y' : Bool), obsOne y false = obsOne true false →
      obsOne y' false = obsOne true false →
      gT3 ψ y false = gT3 ψ y' false := by
  intro hMAR
  have h := hMAR false true false rfl rfl
  have hg1 : gT3 false true false = 0 := by
    have : gT3 false true = PMF.pure true := rfl
    rw [this, PMF.pure_apply,
      ite_eq_right (by decide : (false : Bool) ≠ true)]
  have hg2 : gT3 false false false = 2⁻¹ := by
    have : gT3 false false =
        PMF.ofFintype (fun _ : Bool => (2⁻¹ : ℝ≥0∞)) (by
          rw [Fintype.sum_bool]
          have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
          have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by simp
          have hc : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
            ENNReal.mul_inv_cancel h2ne0 h2netop
          calc (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 2 * 2⁻¹ := (two_mul _).symm
            _ = 1 := hc) := rfl
    rw [this, PMF.ofFintype_apply]
  rw [hg1, hg2] at h
  have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  have hne : (2⁻¹ : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.inv_ne_zero]
    exact h2netop
  exact hne h.symm

/-- T3: joint likelihood values showing the `θ`-ordering flips with `ψ`. -/
theorem T3_L1values :
    Set.univ.indicator (fun p : Bool × Bool => ∑' y,
      {y | obsOne y false = obsOne true false}.indicator
        (fun y => Fpoint.dens p.1 y * gT3 p.2 y false) y)
      (true, false) = 0 ∧
    Set.univ.indicator (fun p : Bool × Bool => ∑' y,
      {y | obsOne y false = obsOne true false}.indicator
        (fun y => Fpoint.dens p.1 y * gT3 p.2 y false) y)
      (false, false) = 2⁻¹ ∧
    Set.univ.indicator (fun p : Bool × Bool => ∑' y,
      {y | obsOne y false = obsOne true false}.indicator
        (fun y => Fpoint.dens p.1 y * gT3 p.2 y false) y)
      (true, true) = 1 ∧
    Set.univ.indicator (fun p : Bool × Bool => ∑' y,
      {y | obsOne y false = obsOne true false}.indicator
        (fun y => Fpoint.dens p.1 y * gT3 p.2 y false) y)
      (false, true) = 2⁻¹ := by
  have hF : ∀ θ y, Fpoint.dens θ y =
      (if y = θ then (1 : ℝ≥0∞) else 0) := fun θ y => rfl
  have hA : ∀ y : Bool, y ∈ {y | obsOne y false = obsOne true false} := by
    intro y
    simp [obsOne]
  have hU : ∀ p : Bool × Bool, p ∈ (Set.univ : Set (Bool × Bool)) :=
    fun p => Set.mem_univ p
  rw [Set.indicator_of_mem (hU _), Set.indicator_of_mem (hU _),
    Set.indicator_of_mem (hU _), Set.indicator_of_mem (hU _)]
  rw [tsum_fintype, tsum_fintype, tsum_fintype, tsum_fintype]
  simp only [Fintype.sum_bool, Set.indicator_of_mem (hA _), hF]
  have hgTF : gT3 false true false = 0 := by
    have : gT3 false true = PMF.pure true := rfl
    rw [this, PMF.pure_apply,
      ite_eq_right (by decide : (false : Bool) ≠ true)]
  have hgFF : gT3 false false false = 2⁻¹ := by
    simp [gT3, PMF.ofFintype_apply]
  have hgTT : gT3 true true false = 1 := by
    have : gT3 true true = PMF.pure false := rfl
    rw [this, PMF.pure_apply, ite_eq_left rfl]
  have hgFT : gT3 true false false = 2⁻¹ := by
    simp [gT3, PMF.ofFintype_apply]
  simp [hgTF, hgFF, hgTT, hgFT,
    mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add]

/-- T3: the `θ`-ordering of `L1` flips with `ψ`. -/
theorem T3_ordering :
    Set.univ.indicator (fun p : Bool × Bool => ∑' y,
      {y | obsOne y false = obsOne true false}.indicator
        (fun y => Fpoint.dens p.1 y * gT3 p.2 y false) y)
      (true, false) <
    Set.univ.indicator (fun p : Bool × Bool => ∑' y,
      {y | obsOne y false = obsOne true false}.indicator
        (fun y => Fpoint.dens p.1 y * gT3 p.2 y false) y)
      (false, false) ∧
    Set.univ.indicator (fun p : Bool × Bool => ∑' y,
      {y | obsOne y false = obsOne true false}.indicator
        (fun y => Fpoint.dens p.1 y * gT3 p.2 y false) y)
      (false, true) <
    Set.univ.indicator (fun p : Bool × Bool => ∑' y,
      {y | obsOne y false = obsOne true false}.indicator
        (fun y => Fpoint.dens p.1 y * gT3 p.2 y false) y)
      (true, true) := by
  have hv := T3_L1values
  rw [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
  have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  have hne : (2⁻¹ : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.inv_ne_zero]
    exact h2netop
  have hpos : (0 : ℝ≥0∞) < 2⁻¹ := by
    rw [pos_iff_ne_zero]
    exact hne
  have hc : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
    ENNReal.mul_inv_cancel h2ne0 h2netop
  have hsum : (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 1 :=
    calc (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 2 * 2⁻¹ := (two_mul _).symm
      _ = 1 := hc
  have hInvNeTop : (2⁻¹ : ℝ≥0∞) ≠ ⊤ := by simp
  have hlt : (2⁻¹ : ℝ≥0∞) < 1 := by
    calc (2⁻¹ : ℝ≥0∞) = 2⁻¹ + 0 := (add_zero _).symm
      _ < 2⁻¹ + 2⁻¹ := ENNReal.add_lt_add_left hInvNeTop hpos
      _ = 1 := hsum
  exact ⟨hpos, hlt⟩

/-- T3: no product factorization `L1 = a ψ * b θ` exists. -/
theorem T3_noFactor :
    ¬ ∃ (a : Bool → ℝ≥0∞) (b : Bool → ℝ≥0∞), ∀ θ ψ,
      Set.univ.indicator (fun p : Bool × Bool => ∑' y,
        {y | obsOne y false = obsOne true false}.indicator
          (fun y => Fpoint.dens p.1 y * gT3 p.2 y false) y)
        (θ, ψ) = a ψ * b θ := by
  intro h
  obtain ⟨a, b, hab⟩ := h
  have hv := T3_L1values
  have e1 := hab true false
  have e2 := hab false false
  have e3 := hab true true
  have e4 := hab false true
  rw [hv.1] at e1
  rw [hv.2.1] at e2
  rw [hv.2.2.1] at e3
  rw [hv.2.2.2] at e4
  have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  have hne : (2⁻¹ : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.inv_ne_zero]
    exact h2netop
  have haF : a false ≠ 0 := by
    intro ha0
    rw [ha0, zero_mul] at e2
    exact hne e2
  have hbT : b true = 0 := by
    have hor : a false = 0 ∨ b true = 0 := mul_eq_zero.mp e1.symm
    cases hor with
    | inl h0 => exact absurd h0 haF
    | inr h0 => exact h0
  rw [hbT, mul_zero] at e3
  exact zero_ne_one e3.symm

/-- T4: MAR holds for every realization when `g` uses only `x`. -/
theorem T4_marHolds :
    ∀ (y₀ : Bool × Bool) (m₀ : Bool) (_ : Unit) (y y' : Bool × Bool),
      obsTwo y m₀ = obsTwo y₀ m₀ → obsTwo y' m₀ = obsTwo y₀ m₀ →
        gT4 () y m₀ = gT4 () y' m₀ := by
  intro y₀ m₀ _ y y' h1 h2
  simp [obsTwo, Prod.mk.injEq] at h1 h2
  have hx : y.1 = y'.1 := h1.1.trans h2.1.symm
  simp [gT4, hx]

/-- T4: complete-case mean of `v` is `2/3` in `ℝ≥0∞`. -/
theorem T4_ccMean :
    (∑ y : Bool × Bool, Ftwo.dens () y * gT4 () y true *
      (if y.2 then (1 : ℝ≥0∞) else 0)) /
      (∑ y : Bool × Bool, Ftwo.dens () y * gT4 () y true) =
      2 / 3 := by
  have hF : ∀ y, Ftwo.dens () y =
      (if y = (true, true) then (2⁻¹ : ℝ≥0∞)
      else if y = (false, false) then 2⁻¹ else 0) := fun y => rfl
  simp only [hF, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [gT4, PMF.pure_apply, PMF.ofFintype_apply,
    mul_zero, zero_mul, mul_one, add_zero, zero_add]
  have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
  have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  have h3ne0 : (3 : ℝ≥0∞) ≠ 0 := by simp
  have h3netop : (3 : ℝ≥0∞) ≠ ⊤ := by simp
  have hc2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
    ENNReal.mul_inv_cancel h2ne0 h2netop
  have h44 : (2 : ℝ≥0∞) * 2 = 4 := by norm_num
  have h4 : (2⁻¹ : ℝ≥0∞) * 2⁻¹ = 4⁻¹ := by
    calc (2⁻¹ : ℝ≥0∞) * 2⁻¹ = (2 * 2)⁻¹ :=
          (ENNReal.mul_inv (Or.inl h2ne0) (Or.inl h2netop)).symm
      _ = 4⁻¹ := by rw [h44]
  have h2eq : (2⁻¹ : ℝ≥0∞) = 2 * 4⁻¹ := by
    rw [← h4, ← mul_assoc, hc2, one_mul]
  have h34 : (2⁻¹ : ℝ≥0∞) + 4⁻¹ = 3 * 4⁻¹ := by
    rw [h2eq]
    nth_rewrite 2 [← one_mul (4⁻¹ : ℝ≥0∞)]
    rw [← add_mul]
    congr 1
    norm_num
  have h4inv : ((4⁻¹ : ℝ≥0∞))⁻¹ = 4 := inv_inv _
  have h3mul : ((3 : ℝ≥0∞) * 4⁻¹)⁻¹ = 3⁻¹ * 4 := by
    have hmul := ENNReal.mul_inv (a := (3 : ℝ≥0∞)) (b := (4⁻¹ : ℝ≥0∞))
      (Or.inl h3ne0) (Or.inl h3netop)
    rw [hmul, h4inv]
  calc (2⁻¹ : ℝ≥0∞) / (2⁻¹ + 2⁻¹ * 2⁻¹)
      = 2⁻¹ * (3 * 4⁻¹)⁻¹ := by rw [div_eq_mul_inv, h4, h34]
    _ = 2⁻¹ * (3⁻¹ * 4) := by rw [h3mul]
    _ = 2 * 3⁻¹ := by
        rw [← h44]
        have hinv : (2⁻¹ : ℝ≥0∞) * 2 = 1 := by rw [mul_comm, hc2]
        calc (2⁻¹ : ℝ≥0∞) * (3⁻¹ * (2*2)) = (2⁻¹*2)*(3⁻¹*2) := by ring
          _ = 1 * (3⁻¹*2) := by rw [hinv]
          _ = 2 * 3⁻¹ := by rw [one_mul, mul_comm]
    _ = 2 / 3 := by rw [div_eq_mul_inv]

/-- T4: population mean of `v` is `1/2` in `ℝ≥0∞`. -/
theorem T4_popMean :
    (∑ y : Bool × Bool, Ftwo.dens () y *
      (if y.2 then (1 : ℝ≥0∞) else 0)) = 2⁻¹ := by
  have hF : ∀ y, Ftwo.dens () y =
      (if y = (true, true) then (2⁻¹ : ℝ≥0∞)
      else if y = (false, false) then 2⁻¹ else 0) := fun y => rfl
  simp only [hF, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [mul_zero, mul_one, add_zero]

/-- T5: realized MAR holds for the diagonal joint space case. -/
theorem T5_marHolds :
    ∀ (ψ : Bool) (y y' : Bool), obsOne y true = obsOne true true →
      obsOne y' true = obsOne true true → gT5 ψ y true = gT5 ψ y' true := by
  intro ψ y y' h1 h2
  simp [obsOne] at h1 h2
  rw [h1, h2]

/-- T5: the diagonal is not a product of its projections. -/
theorem T5_hSfails :
    ¬ ({p : Bool × Bool | p.1 = p.2} =
      (Prod.fst '' {p : Bool × Bool | p.1 = p.2}) ×ˢ
        (Prod.snd '' {p : Bool × Bool | p.1 = p.2})) := by
  intro hS
  have hT : (true : Bool) ∈ Prod.fst '' {p : Bool × Bool | p.1 = p.2} := by
    rw [Set.mem_image]
    exact ⟨(true, true), rfl, rfl⟩
  have hF : (false : Bool) ∈ Prod.snd '' {p : Bool × Bool | p.1 = p.2} := by
    rw [Set.mem_image]
    exact ⟨(false, false), rfl, rfl⟩
  have hmem : (true, false) ∈ (Prod.fst '' {p : Bool × Bool | p.1 = p.2}) ×ˢ
      (Prod.snd '' {p : Bool × Bool | p.1 = p.2}) :=
    Set.mem_prod.mpr ⟨hT, hF⟩
  rw [← hS] at hmem
  exact absurd hmem (by decide)

/-- T5: `L1` is `0` off the diagonal and nonzero on it. -/
theorem T5_L1values :
    {p : Bool × Bool | p.1 = p.2}.indicator
      (fun p : Bool × Bool => ∑' y,
        {y | obsOne y true = obsOne true true}.indicator
          (fun y => Fhalf.dens p.1 y * gT5 p.2 y true) y)
      (true, false) = 0 ∧
    {p : Bool × Bool | p.1 = p.2}.indicator
      (fun p : Bool × Bool => ∑' y,
        {y | obsOne y true = obsOne true true}.indicator
          (fun y => Fhalf.dens p.1 y * gT5 p.2 y true) y)
      (true, true) =
      2⁻¹ * 2⁻¹ ∧
    {p : Bool × Bool | p.1 = p.2}.indicator
      (fun p : Bool × Bool => ∑' y,
        {y | obsOne y true = obsOne true true}.indicator
          (fun y => Fhalf.dens p.1 y * gT5 p.2 y true) y)
      (false, false) =
      2⁻¹ * 2⁻¹ := by
  have hF : ∀ θ y, Fhalf.dens θ y = (2⁻¹ : ℝ≥0∞) := fun θ y => rfl
  have hG : ∀ ψ y, gT5 ψ y true = (2⁻¹ : ℝ≥0∞) := by
    intro ψ y
    simp [gT5, PMF.ofFintype_apply]
  have hA : ∀ y : Bool, {y | obsOne y true = obsOne true true}.indicator
      (fun y => Fhalf.dens true y * gT5 true y true) y =
      (if y = true then 2⁻¹ * 2⁻¹ else 0) := by
    intro y
    by_cases hy : y ∈ {y | obsOne y true = obsOne true true}
    · rw [Set.indicator_of_mem hy, hF, hG]
      have hoy : obsOne y true = obsOne true true := hy
      simp [obsOne] at hoy
      rw [ite_eq_left hoy]
    · rw [Set.indicator_of_notMem hy]
      have hoy : y ≠ true := by
        intro heq
        rw [heq] at hy
        exact hy rfl
      rw [ite_eq_right hoy]
  have hdiag : ∀ (θ ψ : Bool), θ = ψ →
      {p : Bool × Bool | p.1 = p.2}.indicator
        (fun p : Bool × Bool => ∑' y,
          {y | obsOne y true = obsOne true true}.indicator
            (fun y => Fhalf.dens p.1 y * gT5 p.2 y true) y)
        (θ, ψ) = 2⁻¹ * 2⁻¹ := by
    intro θ ψ heq
    subst heq
    cases θ
    · rw [Set.indicator_of_mem (by decide : ((false : Bool), false) ∈
        {p : Bool × Bool | p.1 = p.2})]
      rw [tsum_fintype, Fintype.sum_bool]
      simp only [Set.indicator_of_notMem (by decide : (false : Bool) ∉
        {y | obsOne y true = obsOne true true}), Set.indicator_of_mem
        (show (true : Bool) ∈ {y | obsOne y true = obsOne true true}
        from rfl), hF, hG, add_zero]
    · rw [Set.indicator_of_mem (by decide : ((true : Bool), true) ∈
        {p : Bool × Bool | p.1 = p.2})]
      rw [tsum_fintype, Fintype.sum_bool]
      simp only [Set.indicator_of_notMem (by decide : (false : Bool) ∉
        {y | obsOne y true = obsOne true true}), Set.indicator_of_mem
        (show (true : Bool) ∈ {y | obsOne y true = obsOne true true}
        from rfl), hF, hG, add_zero]
  have hoff : {p : Bool × Bool | p.1 = p.2}.indicator
      (fun p : Bool × Bool => ∑' y,
        {y | obsOne y true = obsOne true true}.indicator
          (fun y => Fhalf.dens p.1 y * gT5 p.2 y true) y)
      (true, false) = 0 :=
    Set.indicator_of_notMem (by decide : (true, false) ∉
      {p : Bool × Bool | p.1 = p.2}) _
  exact ⟨hoff, hdiag true true rfl, hdiag false false rfl⟩

/-- T5: without variation independence no product factorization exists. -/
theorem T5_noFactor :
    ¬ ∃ (a : Bool → ℝ≥0∞) (b : Bool → ℝ≥0∞), ∀ θ ψ,
      {p : Bool × Bool | p.1 = p.2}.indicator
        (fun p : Bool × Bool => ∑' y,
          {y | obsOne y true = obsOne true true}.indicator
            (fun y => Fhalf.dens p.1 y * gT5 p.2 y true) y)
        (θ, ψ) = a ψ * b θ := by
  intro h
  obtain ⟨a, b, hab⟩ := h
  have hv := T5_L1values
  have e1 := hab true false
  have e2 := hab true true
  have e3 := hab false false
  rw [hv.1] at e1
  rw [hv.2.1] at e2
  rw [hv.2.2] at e3
  have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  have hne : (2⁻¹ : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.inv_ne_zero]
    exact h2netop
  have hne2 : (2⁻¹ : ℝ≥0∞) * 2⁻¹ ≠ 0 := mul_ne_zero hne hne
  have hbT : b true ≠ 0 := by
    intro hb0
    rw [hb0, mul_zero] at e2
    exact hne2 e2
  have haF : a false = 0 := by
    have hor : a false = 0 ∨ b true = 0 := mul_eq_zero.mp e1.symm
    cases hor with
    | inl h0 => exact h0
    | inr h0 => exact absurd h0 hbT
  have hbF : b false ≠ 0 := by
    intro hb0
    rw [hb0, mul_zero] at e3
    exact hne2 e3
  have e4 := hab false true
  have hoff : {p : Bool × Bool | p.1 = p.2}.indicator
      (fun p : Bool × Bool => ∑' y,
        {y | obsOne y true = obsOne true true}.indicator
          (fun y => Fhalf.dens p.1 y * gT5 p.2 y true) y)
      (false, true) = 0 :=
    Set.indicator_of_notMem (by decide : (false, true) ∉
      {p : Bool × Bool | p.1 = p.2}) _
  rw [hoff] at e4
  have hor : a true = 0 ∨ b false = 0 := mul_eq_zero.mp e4.symm
  cases hor with
  | inl h0 =>
    have e5 := hab true true
    rw [hv.2.1] at e5
    rw [h0, zero_mul] at e5
    exact hne2 e5
  | inr h0 => exact absurd h0 hbF

/-- T6: realized MAR holds even when the realized pattern has prob 0. -/
theorem T6_marHolds :
    ∀ (ψ : Unit) (y y' : Bool), obsOne y true = obsOne true true →
      obsOne y' true = obsOne true true → gT6 ψ y true = gT6 ψ y' true := by
  intro ψ y y' h1 h2
  simp [obsOne] at h1 h2
  rw [h1, h2]

/-- T6: with zero realized-pattern mass the joint likelihood vanishes. -/
theorem T6_L1zero :
    Set.univ.indicator (fun p : Bool × Unit => ∑' y,
      {y | obsOne y true = obsOne true true}.indicator
        (fun y => Fpoint.dens p.1 y * gT6 p.2 y true) y)
      (true, ()) = 0 ∧
    Set.univ.indicator (fun p : Bool × Unit => ∑' y,
      {y | obsOne y true = obsOne true true}.indicator
        (fun y => Fpoint.dens p.1 y * gT6 p.2 y true) y)
      (false, ()) = 0 := by
  have hG : ∀ y, gT6 () y true = (0 : ℝ≥0∞) := by
    intro y
    have : gT6 () y = PMF.pure false := rfl
    rw [this, PMF.pure_apply,
      ite_eq_right (by decide : (true : Bool) ≠ false)]
  have hF : ∀ θ y, Fpoint.dens θ y =
      (if y = θ then (1 : ℝ≥0∞) else 0) := fun θ y => rfl
  have hU : ∀ p : Bool × Unit, p ∈ (Set.univ : Set (Bool × Unit)) :=
    fun p => Set.mem_univ p
  rw [Set.indicator_of_mem (hU _), Set.indicator_of_mem (hU _)]
  constructor <;> apply ENNReal.tsum_eq_zero.mpr <;> intro y <;>
    by_cases hy : y ∈ {y | obsOne y true = obsOne true true}
  · rw [Set.indicator_of_mem hy, hG, mul_zero]
  · rw [Set.indicator_of_notMem hy]
  · rw [Set.indicator_of_mem hy, hG, mul_zero]
  · rw [Set.indicator_of_notMem hy]

/-- T6: the ignorable likelihood still separates `θ = true` and `false`. -/
theorem T6_L2values :
    (∑' y, {y | obsOne y true = obsOne true true}.indicator
      (fun y => Fpoint.dens true y) y) = 1 ∧
    (∑' y, {y | obsOne y true = obsOne true true}.indicator
      (fun y => Fpoint.dens false y) y) = 0 := by
  have h1 := T1_likelihood true
  have h2 := T1_likelihood false
  have hF1 : Fpoint.dens true true = (1 : ℝ≥0∞) := rfl
  have hF2 : Fpoint.dens false true = (0 : ℝ≥0∞) := rfl
  rw [hF1] at h1
  rw [hF2] at h2
  exact ⟨h1, h2⟩

/-- T6: Theorem 1 (ii) fails without `g ψ y₀ m₀ ≠ 0`. -/
theorem T6_equivFails :
    ¬ (Set.univ.indicator (fun p : Bool × Unit => ∑' y,
        {y | obsOne y true = obsOne true true}.indicator
          (fun y => Fpoint.dens p.1 y * gT6 p.2 y true) y)
        (true, ()) ≤
      Set.univ.indicator (fun p : Bool × Unit => ∑' y,
        {y | obsOne y true = obsOne true true}.indicator
          (fun y => Fpoint.dens p.1 y * gT6 p.2 y true) y)
        (false, ()) ↔
      (∑' y, {y | obsOne y true = obsOne true true}.indicator
        (fun y => Fpoint.dens true y) y) ≤
      ∑' y, {y | obsOne y true = obsOne true true}.indicator
        (fun y => Fpoint.dens false y) y) := by
  have hz := T6_L1zero
  have hv := T6_L2values
  rw [hz.1, hz.2, hv.1, hv.2]
  intro h
  have hle : (0 : ℝ≥0∞) ≤ 0 := le_rfl
  have h10 : ¬((1 : ℝ≥0∞) ≤ 0) := not_le_of_gt zero_lt_one
  exact h10 (h.mp hle)

end MathlibExtTest.Probability.Causality.MissingData.ObservedLikelihood
