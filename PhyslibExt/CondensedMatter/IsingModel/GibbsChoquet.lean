/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.StochasticOrder.StochasticDomination
public import PhyslibExt.CondensedMatter.IsingModel.GibbsSimplex

/-!
# Mixtures of the plus and minus states

Stochastic sandwiches force equality when the extremes agree, and segments between two distinct
states have the extremes as endpoints.

## i. Overview

If two probability measures are both sandwiched between `μ⁻` and `μ⁺` in the stochastic order and
`μ⁻ = μ⁺`, they are equal, since increasing events generate the σ-algebra. The mixtures `a μ⁻ + b
μ⁺` with `a + b = 1` are DLR states when `μ⁻` and `μ⁺` are, are distinct for distinct parameters
when `μ⁻ ≠ μ⁺`, and equal an endpoint only for the trivial parameters.

## ii. Key results

- `StatMech.Ising.upMeasSystem` : measurable increasing events
- `StatMech.Ising.gibbs_sandwiched_eq_of_phases_eq` : sandwiched measures coincide when the extremes
  agree
- `StatMech.Ising.gibbsMix` : the mixture `a μ⁻ + b μ⁺`
- `StatMech.Ising.isDLRState_gibbsMix` : mixtures of DLR states are DLR states
- `StatMech.Ising.gibbsMix_param_injective` : distinct parameters give distinct mixtures

## iii. Table of contents

- A. Increasing events and the stochastic order
- B. Mixtures

## iv. References

- H.-O. Georgii, *Gibbs Measures and Phase Transitions*, de Gruyter (1988; 2nd ed. 2011), Chapter 7
- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems: A Concrete Mathematical
  Introduction*, Cambridge University Press (2017), Chapter 6
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped BigOperators ENNReal StatMech


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}

variable {E : Type*}

/-! ## A. Increasing events and the stochastic order -/

/-- The measurable increasing events of the configuration space. -/
def upMeasSystem (E : Type*) : Set (Set (ConfigSpace E)) :=
  {A | MeasurableSet A ∧ IsUpperSet A}

lemma upTrue_isUpperSet (x : E) : IsUpperSet {ω : ConfigSpace E | ω x = true} := by
  intro a b hab ha
  simp only [Set.mem_ofPred_eq] at *
  have h := hab x; rw [ha] at h
  cases hb : b x
  · rw [hb] at h; exact absurd h (by simp)
  · rfl

lemma upTrue_measurableSet (x : E) :
    MeasurableSet {ω : ConfigSpace E | ω x = true} := by
  have hpre : {ω : ConfigSpace E | ω x = true} = (ConfigSpace.eval x) ⁻¹' {true} := by
    ext ω; simp [ConfigSpace.eval]
  rw [hpre]; exact (measurable_pi_apply x) (by trivial)

lemma upTrue_mem (x : E) : {ω : ConfigSpace E | ω x = true} ∈ upMeasSystem E :=
  ⟨upTrue_measurableSet x, upTrue_isUpperSet x⟩

lemma isPiSystem_upMeas : IsPiSystem (upMeasSystem E) := by
  rintro A ⟨hAm, hAu⟩ B ⟨hBm, hBu⟩ _
  exact ⟨hAm.inter hBm, hAu.inter hBu⟩

lemma generateFrom_upMeas :
    MeasurableSpace.generateFrom (upMeasSystem E)
      = (inferInstance : MeasurableSpace (ConfigSpace E)) := by
  apply le_antisymm
  · apply generateFrom_le; rintro A ⟨hAm, _⟩; exact hAm
  · rw [ConfigSpace.measurableSpace_eq_iSup_comap]
    refine iSup_le (fun x => ?_)
    set G := MeasurableSpace.generateFrom (upMeasSystem E) with hG
    have hT : MeasurableSet[G] {ω : ConfigSpace E | ω x = true} :=
      measurableSet_generateFrom (upTrue_mem x)
    have hTc : MeasurableSet[G] {ω : ConfigSpace E | ω x = true}ᶜ := hT.compl
    have hEmpty : MeasurableSet[G] (∅ : Set (ConfigSpace E)) := @MeasurableSet.empty _ G
    intro s hs
    obtain ⟨t, _, rfl⟩ := hs
    classical
    have key : (ConfigSpace.eval x) ⁻¹' t
        = (if true ∈ t then {ω : ConfigSpace E | ω x = true} else ∅)
          ∪ (if false ∈ t then {ω : ConfigSpace E | ω x = true}ᶜ else ∅) := by
      ext ω
      simp only [Set.mem_preimage, ConfigSpace.eval_apply, Set.mem_union]
      cases hw : ω x <;> simp [hw]
    change MeasurableSet[G] _
    rw [key]
    refine (?_ : MeasurableSet[G] _).union (?_ : MeasurableSet[G] _)
    · split <;> [exact hT; exact hEmpty]
    · split <;> [exact hTc; exact hEmpty]

lemma StochasticallyDominated.antisymm {μ ν : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h₁ : μ ≼ ν) (h₂ : ν ≼ μ) : μ = ν := by
  refine ext_of_generate_finite (upMeasSystem E)
    generateFrom_upMeas.symm isPiSystem_upMeas ?_ ?_
  · rintro A ⟨hAm, hAu⟩
    have hle : μ.real A ≤ ν.real A := h₁ A hAm hAu
    have hge : ν.real A ≤ μ.real A := h₂ A hAm hAu
    have hre : μ.real A = ν.real A := le_antisymm hle hge
    unfold Measure.real at hre
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top ν A)).mp hre
  · rw [measure_univ, measure_univ]

lemma gibbs_unique_of_phases_eq {μm μp μ : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μm] [IsProbabilityMeasure μp] [IsProbabilityMeasure μ]
    (hsw₁ : μm ≼ μ) (hsw₂ : μ ≼ μp) (hphase : μp = μm) :
    μ = μm := by
  have h₂ : μ ≼ μm := by rw [← hphase]; exact hsw₂
  exact StochasticallyDominated.antisymm h₂ hsw₁

lemma gibbs_sandwiched_eq_of_phases_eq {μm μp μ μ' : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μm] [IsProbabilityMeasure μp]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hsw₁ : μm ≼ μ) (hsw₂ : μ ≼ μp) (hsw₁' : μm ≼ μ') (hsw₂' : μ' ≼ μp)
    (hphase : μp = μm) : μ = μ' := by
  rw [gibbs_unique_of_phases_eq hsw₁ hsw₂ hphase,
    gibbs_unique_of_phases_eq hsw₁' hsw₂' hphase]

/-! ## B. Mixtures -/

/-- The mixture `a μ⁻ + b μ⁺` of two measures. -/
noncomputable def gibbsMix (a b : ℝ≥0∞) (μm μp : Measure (ConfigSpace E)) :
    Measure (ConfigSpace E) :=
  a • μm + b • μp

@[simp] lemma gibbsMix_apply (a b : ℝ≥0∞) (μm μp : Measure (ConfigSpace E))
    (s : Set (ConfigSpace E)) :
    gibbsMix a b μm μp s = a * μm s + b * μp s := by
  simp [gibbsMix, Measure.add_apply, Measure.smul_apply]

@[simp] lemma gibbsMix_one_zero (μm μp : Measure (ConfigSpace E)) :
    gibbsMix 1 0 μm μp = μm := by simp [gibbsMix]

@[simp] lemma gibbsMix_zero_one (μm μp : Measure (ConfigSpace E)) :
    gibbsMix 0 1 μm μp = μp := by simp [gibbsMix]

lemma isDLRState_gibbsMix (β h : ℝ) {a b : ℝ≥0∞} (hab : a + b = 1)
    (μm μp : Measure (ConfigSpace (Site d))) [IsFiniteMeasure μm] [IsFiniteMeasure μp]
    [IsFiniteMeasure (gibbsMix a b μm μp)]
    (h₁ : IsDLRState d β h μm) (h₂ : IsDLRState d β h μp) :
    IsDLRState d β h (gibbsMix a b μm μp) := by
  have : IsFiniteMeasure (a • μm + b • μp) := ‹IsFiniteMeasure (gibbsMix a b μm μp)›
  exact convex_isDLRState β h hab μm μp h₁ h₂

lemma gibbsMix_isProbabilityMeasure {a b : ℝ≥0∞}
    (hab : a + b = 1) (μm μp : Measure (ConfigSpace E))
    [IsProbabilityMeasure μm] [IsProbabilityMeasure μp] :
    IsProbabilityMeasure (gibbsMix a b μm μp) := by
  refine ⟨?_⟩
  rw [gibbsMix_apply, measure_univ, measure_univ, mul_one, mul_one, hab]

lemma exists_real_ne_of_ne {μm μp : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μm] [IsProbabilityMeasure μp] (hne : μm ≠ μp) :
    ∃ A, MeasurableSet A ∧ μm.real A ≠ μp.real A := by
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  refine hne (Measure.ext (fun A hA => ?_))
  have hre : μm.real A = μp.real A := hc A hA
  unfold Measure.real at hre
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μm A) (measure_ne_top μp A)).mp hre

lemma gibbsMix_coeff_unique {μm μp : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μm] [IsProbabilityMeasure μp] (hne : μm ≠ μp)
    {a b a' b' : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (ha' : a' ≠ ⊤) (hb' : b' ≠ ⊤)
    (hab : a + b = 1) (hab' : a' + b' = 1)
    (heq : gibbsMix a b μm μp = gibbsMix a' b' μm μp) : a = a' := by
  obtain ⟨A, hAm, hAne⟩ := exists_real_ne_of_ne hne
  have h1 := congrArg (fun m => m A) heq
  simp only [gibbsMix_apply] at h1
  have hμA : μm A ≠ ⊤ := measure_ne_top μm A
  have hνA : μp A ≠ ⊤ := measure_ne_top μp A
  have h1r : a.toReal * μm.real A + b.toReal * μp.real A
           = a'.toReal * μm.real A + b'.toReal * μp.real A := by
    have hcast := congrArg ENNReal.toReal h1
    simp only [ENNReal.toReal_add (ENNReal.mul_ne_top ha hμA) (ENNReal.mul_ne_top hb hνA),
      ENNReal.toReal_add (ENNReal.mul_ne_top ha' hμA) (ENNReal.mul_ne_top hb' hνA),
      ENNReal.toReal_mul] at hcast
    exact hcast
  have hsum : a.toReal + b.toReal = 1 := by
    rw [← ENNReal.toReal_add ha hb, hab, ENNReal.toReal_one]
  have hsum' : a'.toReal + b'.toReal = 1 := by
    rw [← ENNReal.toReal_add ha' hb', hab', ENNReal.toReal_one]
  have hbr : b.toReal = 1 - a.toReal := by linarith
  have hbr' : b'.toReal = 1 - a'.toReal := by linarith
  rw [hbr, hbr'] at h1r
  have hdiff : (a.toReal - a'.toReal) * (μm.real A - μp.real A) = 0 := by nlinarith [h1r]
  rcases mul_eq_zero.mp hdiff with hz | hz
  · exact (ENNReal.toReal_eq_toReal_iff' ha ha').mp (by linarith)
  · exact absurd (by linarith : μm.real A = μp.real A) hAne

lemma gibbsMix_coeff_unique_pair {μm μp : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μm] [IsProbabilityMeasure μp] (hne : μm ≠ μp)
    {a b a' b' : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (ha' : a' ≠ ⊤) (hb' : b' ≠ ⊤)
    (hab : a + b = 1) (hab' : a' + b' = 1)
    (heq : gibbsMix a b μm μp = gibbsMix a' b' μm μp) : a = a' ∧ b = b' := by
  have ha_eq : a = a' := gibbsMix_coeff_unique hne ha hb ha' hb' hab hab' heq
  refine ⟨ha_eq, ?_⟩
  have hsum : a' + b = a' + b' := by
    rw [hab', ← hab, ha_eq]
  exact (ENNReal.add_right_inj ha').mp hsum

lemma gibbsMix_ne_minus {μm μp : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μm] [IsProbabilityMeasure μp] (hne : μm ≠ μp)
    {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hab : a + b = 1) (hb0 : b ≠ 0) :
    gibbsMix a b μm μp ≠ μm := by
  intro hcontra
  have hcontra' : gibbsMix a b μm μp = gibbsMix 1 0 μm μp :=
    hcontra.trans (gibbsMix_one_zero μm μp).symm
  have hpair := gibbsMix_coeff_unique_pair hne ha hb ENNReal.one_ne_top (by simp) hab (by simp)
      hcontra'
  exact hb0 hpair.2

lemma gibbsMix_ne_plus {μm μp : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μm] [IsProbabilityMeasure μp] (hne : μm ≠ μp)
    {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hab : a + b = 1) (ha0 : a ≠ 0) :
    gibbsMix a b μm μp ≠ μp := by
  intro hcontra
  have hcontra' : gibbsMix a b μm μp = gibbsMix 0 1 μm μp :=
    hcontra.trans (gibbsMix_zero_one μm μp).symm
  have hpair := gibbsMix_coeff_unique_pair hne ha hb (by simp) ENNReal.one_ne_top hab (by simp)
      hcontra'
  exact ha0 hpair.1

lemma minusState_extreme_in_segment {μm μp : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μm] [IsProbabilityMeasure μp] (hne : μm ≠ μp)
    {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hab : a + b = 1)
    (heq : gibbsMix a b μm μp = μm) : a = 1 ∧ b = 0 := by
  have heq' : gibbsMix a b μm μp = gibbsMix 1 0 μm μp :=
    heq.trans (gibbsMix_one_zero μm μp).symm
  exact gibbsMix_coeff_unique_pair hne ha hb ENNReal.one_ne_top (by simp) hab (by simp) heq'

lemma plusState_extreme_in_segment {μm μp : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μm] [IsProbabilityMeasure μp] (hne : μm ≠ μp)
    {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hab : a + b = 1)
    (heq : gibbsMix a b μm μp = μp) : a = 0 ∧ b = 1 := by
  have heq' : gibbsMix a b μm μp = gibbsMix 0 1 μm μp :=
    heq.trans (gibbsMix_zero_one μm μp).symm
  exact gibbsMix_coeff_unique_pair hne ha hb (by simp) ENNReal.one_ne_top hab (by simp) heq'

lemma gibbsMix_param_injective {μm μp : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μm] [IsProbabilityMeasure μp] (hne : μm ≠ μp)
    {a a' : ℝ≥0∞} (ha : a ≤ 1) (ha' : a' ≤ 1)
    (heq : gibbsMix a (1 - a) μm μp = gibbsMix a' (1 - a') μm μp) : a = a' := by
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hat' : a' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha'
  have hbt : (1 - a) ≠ ⊤ := by
    have : (1 : ℝ≥0∞) - a ≤ 1 := tsub_le_self
    exact ne_top_of_le_ne_top ENNReal.one_ne_top this
  have hbt' : (1 - a') ≠ ⊤ := by
    have : (1 : ℝ≥0∞) - a' ≤ 1 := tsub_le_self
    exact ne_top_of_le_ne_top ENNReal.one_ne_top this
  have hab : a + (1 - a) = 1 := add_tsub_cancel_of_le ha
  have hab' : a' + (1 - a') = 1 := add_tsub_cancel_of_le ha'
  exact gibbsMix_coeff_unique hne hat hbt hat' hbt' hab hab' heq

end Ising

end StatMech
