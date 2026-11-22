/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.PlusStateTICylinder
public import PhyslibExt.CondensedMatter.IsingModel.PressureSurfaceVolume
public import MathlibExt.Probability.Configuration.MonotoneLimit

/-!
# Translation invariance from boundary influence bounds

Shift differences of plus box measures bounded by the boundary fraction of the box imply translation
invariance.

## i. Overview

The fraction of bonds of `Λ_n` that touch its boundary tends to `0`. If the shift differences of
integrals of cylinder functions against the plus box measures are bounded by a constant times this
fraction (`ibs_PlusBoundaryInfluence`), they decay, and the plus state is translation invariant,
ergodic and extreme. The file also shows that equal one-site densities give decay of shifted
coordinates.

## ii. Key results

- `StatMech.Ising.ibs_boundaryFraction` : the boundary fraction of a box
- `StatMech.Ising.ibs_PlusBoundaryInfluence` : boundary influence bounds
- `StatMech.Ising.ibs_plusState_isTranslationInvariant_of_boundaryInfluence` : translation
  invariance
- `StatMech.Ising.ibs_plusState_ergodic_extreme_of_boundaryInfluence` : ergodicity and extremality

## iii. Table of contents

- A. Shifted coordinates
- B. The boundary fraction
- C. Boundary influence

## iv. References

- H.-O. Georgii, *Gibbs Measures and Phase Transitions*, de Gruyter (1988; 2nd ed. 2011), Chapter 5
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}

lemma ibs_isClopen_spinUp (x : Site d) :
    IsClopen {ω : ConfigSpace (Site d) | ω x = true} := by
  have h : {ω : ConfigSpace (Site d) | ω x = true} = (fun ω => ω x) ⁻¹' {true} := rfl
  rw [h]
  exact IsClopen.preimage (isClopen_discrete _) (continuous_apply x)

lemma ibs_measurableSet_spinUp (x : Site d) :
    MeasurableSet {ω : ConfigSpace (Site d) | ω x = true} :=
  (ibs_isClopen_spinUp x).isClosed.measurableSet

lemma ibs_integral_coordBcf (x : Site d) (μ : Measure (ConfigSpace (Site d)))
    [IsFiniteMeasure μ] :
    (∫ ω, pstc_coordBcf x ω ∂μ) = μ.real {ω | ω x = true} := by
  have heq : (fun ω => pstc_coordBcf x ω)
      = Set.indicator {ω : ConfigSpace (Site d) | ω x = true} (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [pstc_coordBcf_apply, Set.indicator]
    by_cases h : ω x <;> simp [h, Set.mem_ofPred_eq]
  rw [heq, MeasureTheory.integral_indicator_const (1 : ℝ) (ibs_measurableSet_spinUp x)]
  simp [Measure.real]

/-! ## A. Shifted coordinates -/

lemma ibs_coordBcf_comp_shift (x : Site d) (g : Multiplicative (Site d))
    (ω : ConfigSpace (Site d)) :
    pstc_coordBcf x (shift g ω) = pstc_coordBcf (g⁻¹ • x) ω := rfl

lemma ibs_decayFun_coord (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (x : Site d) (n : ℕ) :
    pstc_decayFun μ g (pstc_coordBcf x) n
      = ((μ n : Measure (ConfigSpace (Site d))).real {ω | ω x = true})
        - ((μ n : Measure (ConfigSpace (Site d))).real {ω | ω (g⁻¹ • x) = true}) := by
  unfold pstc_decayFun
  rw [ibs_integral_coordBcf x]
  congr 1
  rw [show (fun ω => pstc_coordBcf x (shift g ω)) = (fun ω => pstc_coordBcf (g⁻¹ • x) ω) from rfl]
  rw [ibs_integral_coordBcf (g⁻¹ • x)]

lemma ibs_plus_siteProb_tendsto (β h : ℝ) (φ : ℕ → ℕ) (x : Site d)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h)) :
    Tendsto (fun n => (plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
        {ω | ω x = true}) atTop
      (𝓝 ((plusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true})) :=
  StatMech.WeakConvergesTo.tendsto_real_of_isClopen hconv (ibs_isClopen_spinUp x)

lemma ibs_minus_siteProb_tendsto (β h : ℝ) (φ : ℕ → ℕ) (x : Site d)
    (hconv : WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h)) :
    Tendsto (fun n => (minusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
        {ω | ω x = true}) atTop
      (𝓝 ((minusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true})) :=
  StatMech.WeakConvergesTo.tendsto_real_of_isClopen hconv (ibs_isClopen_spinUp x)

lemma ibs_plus_coord_decay_of_density_eq (β h : ℝ) (φ : ℕ → ℕ) (g : Multiplicative (Site d))
    (x : Site d)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
    (hdens : (plusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true}
      = (plusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω (g⁻¹ • x) = true}) :
    Tendsto (pstc_decayFun (fun n => plusMeasure d (φ n) β h) g (pstc_coordBcf x))
      atTop (𝓝 0) := by
  have h1 := ibs_plus_siteProb_tendsto β h φ x hconv
  have h2 := ibs_plus_siteProb_tendsto β h φ (g⁻¹ • x) hconv
  have hdecayeq : pstc_decayFun (fun n => plusMeasure d (φ n) β h) g (pstc_coordBcf x)
      = fun n => ((plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true})
        - ((plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
            {ω | ω (g⁻¹ • x) = true}) := by
    funext n; exact ibs_decayFun_coord _ g x n
  rw [hdecayeq]
  have := h1.sub h2
  rw [hdens, sub_self] at this
  exact this

lemma ibs_minus_coord_decay_of_density_eq (β h : ℝ) (φ : ℕ → ℕ) (g : Multiplicative (Site d))
    (x : Site d)
    (hconv : WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h))
    (hdens : (minusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true}
      = (minusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω (g⁻¹ • x) = true}) :
    Tendsto (pstc_decayFun (fun n => minusMeasure d (φ n) β h) g (pstc_coordBcf x))
      atTop (𝓝 0) := by
  have h1 := ibs_minus_siteProb_tendsto β h φ x hconv
  have h2 := ibs_minus_siteProb_tendsto β h φ (g⁻¹ • x) hconv
  have hdecayeq : pstc_decayFun (fun n => minusMeasure d (φ n) β h) g (pstc_coordBcf x)
      = fun n => ((minusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true})
        - ((minusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
            {ω | ω (g⁻¹ • x) = true}) := by
    funext n; exact ibs_decayFun_coord _ g x n
  rw [hdecayeq]
  have := h1.sub h2
  rw [hdens, sub_self] at this
  exact this

/-! ## B. The boundary fraction -/

/-- The number of bonds touching but not inside `Λ_n`, divided by the number of sites of `Λ_n`. -/
noncomputable def ibs_boundaryFraction (d n : ℕ) : ℝ :=
  ((bondFinsetTouch d n \ bondFinsetInternal d n).card : ℝ) / ((boxFinset d n).card : ℝ)

lemma ibs_boundaryFraction_nonneg (d n : ℕ) : 0 ≤ ibs_boundaryFraction d n := by
  unfold ibs_boundaryFraction; positivity

lemma ibs_boundaryFraction_tendsto_zero (hd : 1 ≤ d) :
    Tendsto (ibs_boundaryFraction d) atTop (𝓝 0) :=
  psv_ratio_card_tendsto_zero d hd

lemma ibs_boundaryFraction_comp_tendsto_zero (hd : 1 ≤ d) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tendsto (fun n => ibs_boundaryFraction d (φ n)) atTop (𝓝 0) :=
  (ibs_boundaryFraction_tendsto_zero hd).comp hφ.tendsto_atTop

lemma ibs_decay_of_boundaryBound (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (f : ConfigSpace (Site d) →ᵇ ℝ) {φ : ℕ → ℕ}
    (hd : 1 ≤ d) (hφ : StrictMono φ) (C : ℝ)
    (hbound : ∀ n, |pstc_decayFun (fun n => μ (φ n)) g f n| ≤ C * ibs_boundaryFraction d (φ n)) :
    Tendsto (pstc_decayFun (fun n => μ (φ n)) g f) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero (fun n => abs_nonneg _) hbound
  have := (ibs_boundaryFraction_comp_tendsto_zero hd hφ).const_mul C
  rwa [mul_zero] at this

/-! ## C. Boundary influence -/

/-- Shift differences of cylinder-function integrals against the plus box measures are
`O(boundary fraction)`. -/
def ibs_PlusBoundaryInfluence (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f ∈ pstc_cylinderBcfSet d, ∃ C : ℝ, ∀ n,
    |pstc_decayFun (fun n => plusMeasure d (φ n) β h) g f n|
      ≤ C * ibs_boundaryFraction d (φ n)

/-- Shift differences of cylinder-function integrals against the minus box measures are
`O(boundary fraction)`. -/
def ibs_MinusBoundaryInfluence (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f ∈ pstc_cylinderBcfSet d, ∃ C : ℝ, ∀ n,
    |pstc_decayFun (fun n => minusMeasure d (φ n) β h) g f n|
      ≤ C * ibs_boundaryFraction d (φ n)

lemma ibs_plusCylinderDecay_of_boundaryInfluence (β h : ℝ) (g : Multiplicative (Site d))
    (φ : ℕ → ℕ) (hd : 1 ≤ d) (hφ : StrictMono φ)
    (hbi : ibs_PlusBoundaryInfluence β h g φ) :
    pstc_PlusCylinderDecay β h g φ := by
  intro f hf
  obtain ⟨C, hC⟩ := hbi f hf
  exact ibs_decay_of_boundaryBound (fun n => plusMeasure d n β h) g f hd hφ C hC

lemma ibs_minusCylinderDecay_of_boundaryInfluence (β h : ℝ) (g : Multiplicative (Site d))
    (φ : ℕ → ℕ) (hd : 1 ≤ d) (hφ : StrictMono φ)
    (hbi : ibs_MinusBoundaryInfluence β h g φ) :
    pstc_MinusCylinderDecay β h g φ := by
  intro f hf
  obtain ⟨C, hC⟩ := hbi f hf
  exact ibs_decay_of_boundaryBound (fun n => minusMeasure d n β h) g f hd hφ C hC

lemma ibs_plusBoundaryInfluence_one (β h : ℝ) (φ : ℕ → ℕ) :
    ibs_PlusBoundaryInfluence β h (1 : Multiplicative (Site d)) φ := by
  intro f _
  refine ⟨0, fun n => ?_⟩
  rw [pstc_decayFun_one]
  simp

lemma ibs_minusBoundaryInfluence_one (β h : ℝ) (φ : ℕ → ℕ) :
    ibs_MinusBoundaryInfluence β h (1 : Multiplicative (Site d)) φ := by
  intro f _
  refine ⟨0, fun n => ?_⟩
  rw [pstc_decayFun_one]
  simp

lemma ibs_plusCylinderDecay_one_via_squeeze (β h : ℝ) {φ : ℕ → ℕ} (hd : 1 ≤ d)
    (hφ : StrictMono φ) :
    pstc_PlusCylinderDecay β h (1 : Multiplicative (Site d)) φ :=
  ibs_plusCylinderDecay_of_boundaryInfluence β h (1 : Multiplicative (Site d)) φ hd hφ
    (ibs_plusBoundaryInfluence_one β h φ)

lemma ibs_plusState_isTranslationInvariant_of_boundaryInfluence (β h : ℝ) (hd : 1 ≤ d)
    (hbi : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) →
        ibs_PlusBoundaryInfluence β h g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  pstc_plusState_isTranslationInvariant_of_cylinderDecay β h
    (fun g φ hφ hconv =>
      ibs_plusCylinderDecay_of_boundaryInfluence β h g φ hd hφ (hbi g φ hφ hconv))

lemma ibs_plusState_ergodic_extreme_of_boundaryInfluence (β h : ℝ)
    (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hbi : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) →
        ibs_PlusBoundaryInfluence β h g φ) :
    IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (plusState d β h : Measure (ConfigSpace (Site d))) :=
  pstc_plusState_ergodic_extreme_of_cylinderDecay β h hd hβ hh
    (fun g φ hφ hconv =>
      ibs_plusCylinderDecay_of_boundaryInfluence β h g φ hd hφ (hbi g φ hφ hconv))

lemma ibs_minusState_ergodic_extreme_of_boundaryInfluence (β h : ℝ)
    (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
    (hbi : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) →
        ibs_MinusBoundaryInfluence β h g φ) :
    IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (minusState d β h : Measure (ConfigSpace (Site d))) :=
  pstc_minusState_ergodic_extreme_of_cylinderDecay β h hd hβ hh hdlr
    (fun g φ hφ hconv =>
      ibs_minusCylinderDecay_of_boundaryInfluence β h g φ hd hφ (hbi g φ hφ hconv))

end Ising

end StatMech
