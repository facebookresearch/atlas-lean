/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PhyslibExt.EarthScience.BlackbodyFlux
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Black enclosure radiation: power conservation

## i. Overview

A closed enclosure of finitely many diffuse black surfaces `i : ι` with areas `A i > 0`, view
factors `F i j ≥ 0` (fraction of the radiation leaving `i` that arrives at `j`), unit row sums and
area reciprocity `A i * F i j = A j * F j i`. Surface temperatures `T i ≥ 0` are absolute and
`σ > 0` is the Stefan-Boltzmann constant; the law `σ T⁴` is an adopted input.

The net power leaving surface `i` is `P i = ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4)` (watts);
it includes the area, and the net flux is `P i / A i` (watts per square metre). Positive `P i`
is a net outflow. Results: total power cancels, an isothermal neighbourhood exchanges nothing,
a hottest surface has nonnegative outflow, and `P i` is emission minus absorption of the
Lambertian blackbody flux.

## ii. Key results

- `HeatTransfer.EnclosureRadiation.sum_netPower_eq_zero`: the net powers of all surfaces
  in a black enclosure sum to zero.
- `HeatTransfer.EnclosureRadiation.netPower_eq_emitted_sub_absorbed`: net power is emitted
  hemispheric blackbody power minus absorbed power from every other surface.
- `HeatTransfer.EnclosureRadiation.netPower_nonneg_of_hottest`: a hottest surface has
  nonnegative net outflow.

## iii. Table of contents

- A. Enclosure data and net power
- B. Conservation and sign results

## iv. References

- The view-factor enclosure theory for diffuse black surfaces is classical radiative
  heat transfer (e.g. Incropera and DeWitt, *Fundamentals of Heat and Mass Transfer*,
  the enclosure-theory chapter); the hemispheric blackbody flux `σ T⁴` is
  `PhyslibExt.EarthScience.BlackbodyFlux`.

## A. Enclosure data and net power
-/

@[expose] public section

namespace HeatTransfer.EnclosureRadiation

variable {ι : Type*} [Fintype ι]

/-- Diffuse black enclosure data on the finite surface set `ι`: areas `A i > 0`, view factors
`F i j ≥ 0`, unit row sums `∑ j, F i j = 1` (closure: an opening must be an explicit node) and
area reciprocity `A i * F i j = A j * F j i`. -/
structure IsBlackEnclosure (A : ι → ℝ) (F : ι → ι → ℝ) : Prop where
  area_pos : ∀ i, 0 < A i
  viewFactor_nonneg : ∀ i j, 0 ≤ F i j
  rowSum_eq_one : ∀ i, ∑ j, F i j = 1
  reciprocity : ∀ i j, A i * F i j = A j * F j i

/-- Net radiative power leaving surface `i`:
`P i = ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4)`. Positive values are a net outflow. -/
def netPower (σ : ℝ) (A : ι → ℝ) (F : ι → ι → ℝ) (T : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4)

/-- Net radiative flux leaving surface `i`: the net power per unit area, `P i / A i`. -/
noncomputable def netFlux (σ : ℝ) (A : ι → ℝ) (F : ι → ι → ℝ) (T : ι → ℝ) (i : ι) : ℝ :=
  netPower σ A F T i / A i

/-- The net flux is the power with the area removed:
`P i / A i = ∑ j, F i j * σ * (T i ^ 4 - T j ^ 4)` for `A i > 0`. -/
lemma netFlux_eq {σ : ℝ} {A : ι → ℝ} {F : ι → ι → ℝ} {T : ι → ℝ} {i : ι} (hA : 0 < A i) :
    netFlux σ A F T i = ∑ j, F i j * σ * (T i ^ 4 - T j ^ 4) := by
  unfold netFlux netPower
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hA' : A i ≠ 0 := ne_of_gt hA
  field_simp

/-- Emission minus absorption: in a black enclosure with `σ > 0` and absolute temperatures
`T ≥ 0`, the net power of surface `i` is its area times the hemispheric integral of its
Lambertian intensity `σ T i ^ 4 / π`, minus the power `A j * F j i` times the same integral for
`T j`, arriving from every surface `j` and absorbed. -/
lemma netPower_eq_emitted_sub_absorbed {σ : ℝ} {A : ι → ℝ} {F : ι → ι → ℝ} {T : ι → ℝ}
    (hE : IsBlackEnclosure A F) (hσ : 0 < σ) (hT : ∀ i, 0 ≤ T i) (i : ι) :
    netPower σ A F T i =
      A i * (∫ θ in (0 : ℝ)..(Real.pi / 2),
          (σ * T i ^ 4 / Real.pi) * Real.cos θ * (2 * Real.pi * Real.sin θ)) -
        ∑ j, A j * F j i * (∫ θ in (0 : ℝ)..(Real.pi / 2),
          (σ * T j ^ 4 / Real.pi) * Real.cos θ * (2 * Real.pi * Real.sin θ)) := by
  have hσ0 : 0 ≤ σ := le_of_lt hσ
  have hint : ∀ k, (∫ θ in (0 : ℝ)..(Real.pi / 2),
        (σ * T k ^ 4 / Real.pi) * Real.cos θ * (2 * Real.pi * Real.sin θ))
      = σ * T k ^ 4 :=
    fun k => EarthScience.integrated_blackbody_flux_eq hσ0 (hT k)
  simp only [hint]
  unfold netPower
  have hrow := hE.rowSum_eq_one i
  have hsplit : (∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4))
      = (∑ j, A i * F i j * σ * T i ^ 4) - ∑ j, A i * F i j * σ * T j ^ 4 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hfirst : (∑ j, A i * F i j * σ * T i ^ 4) = A i * (σ * T i ^ 4) := by
    calc (∑ j, A i * F i j * σ * T i ^ 4)
        = (∑ j, F i j) * (A i * σ * T i ^ 4) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = A i * (σ * T i ^ 4) := by
          rw [hrow, one_mul]
          ring
  have hsecond : (∑ j, A i * F i j * σ * T j ^ 4)
      = ∑ j, A j * F j i * (σ * T j ^ 4) := by
    apply Finset.sum_congr rfl
    intro j _
    have hr := hE.reciprocity i j
    calc A i * F i j * σ * T j ^ 4
        = (A i * F i j) * (σ * T j ^ 4) := by ring
      _ = (A j * F j i) * (σ * T j ^ 4) := by rw [hr]
      _ = A j * F j i * (σ * T j ^ 4) := by ring
  rw [hsplit, hfirst, hsecond]

/-! ## B. Conservation and sign results -/

/-- Power conservation: the net powers of a black enclosure sum to zero. Only reciprocity is
used; no sign condition on `σ` or `T` is needed. -/
lemma sum_netPower_eq_zero {A : ι → ℝ} {F : ι → ι → ℝ} (hE : IsBlackEnclosure A F)
    (σ : ℝ) (T : ι → ℝ) :
    ∑ i, netPower σ A F T i = 0 := by
  unfold netPower
  have hsym : ∀ i j, A j * F j i * σ * (T j ^ 4 - T i ^ 4)
      = -(A i * F i j * σ * (T i ^ 4 - T j ^ 4)) := by
    intro i j
    have hrec := hE.reciprocity i j
    rw [← hrec]
    ring
  have hcomm : (∑ i, ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4))
      = ∑ i, ∑ j, A j * F j i * σ * (T j ^ 4 - T i ^ 4) := Finset.sum_comm
  have hneg : (∑ i, ∑ j, A j * F j i * σ * (T j ^ 4 - T i ^ 4))
      = -(∑ i, ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact hsym i j
  have hself : (∑ i, ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4))
      = -(∑ i, ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4)) := hcomm.trans hneg
  linarith

/-- Zero exchange at equal temperatures: if every surface has the temperature of surface `i`,
the net power of `i` is zero. -/
lemma netPower_eq_zero_of_temp_eq {σ : ℝ} {A : ι → ℝ} {F : ι → ι → ℝ} {T : ι → ℝ} {i : ι}
    (hT : ∀ j, T j = T i) :
    netPower σ A F T i = 0 := by
  unfold netPower
  apply Finset.sum_eq_zero
  intro j _
  rw [hT j, sub_self, mul_zero]

/-- A hottest surface has nonnegative net outflow: with `σ > 0`, absolute temperatures `T ≥ 0`
and `T j ≤ T k` for every `j`, the net power of `k` is `≥ 0`. -/
lemma netPower_nonneg_of_hottest {σ : ℝ} {A : ι → ℝ} {F : ι → ι → ℝ} {T : ι → ℝ}
    (hE : IsBlackEnclosure A F) (hσ : 0 < σ) (hT : ∀ i, 0 ≤ T i) {k : ι}
    (hk : ∀ j, T j ≤ T k) :
    0 ≤ netPower σ A F T k := by
  unfold netPower
  apply Finset.sum_nonneg
  intro j _
  have hA : 0 ≤ A k := le_of_lt (hE.area_pos k)
  have hF : 0 ≤ F k j := hE.viewFactor_nonneg k j
  have hs : 0 ≤ σ := le_of_lt hσ
  have hpow : T j ^ 4 ≤ T k ^ 4 := pow_le_pow_left₀ (hT j) (hk j) 4
  have hsub : 0 ≤ T k ^ 4 - T j ^ 4 := sub_nonneg.mpr hpow
  exact mul_nonneg (mul_nonneg (mul_nonneg hA hF) hs) hsub


end HeatTransfer.EnclosureRadiation
