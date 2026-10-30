/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.UniquenessFromSecant
/-!
# Edge-density comparison from a convex free energy in the logit parameter

If the wired and free edge densities, as functions of `t = logit p`, are the right and left
derivatives of a convex function, then `θ^w(p') ≤ θ^f(p)` for `p' < p`, and at `q = 2` the
infinite-volume edge marginal is unique off a countable set of `p`.

## i. Overview

The edge parameter is reparametrized by the logistic map `fsc_logistic t = eᵗ / (1 + eᵗ)`
(Mathlib's `Real.sigmoid`, see `fsc_logistic_eq_sigmoid`) with inverse `fsc_logit`.
`fsc_FreeEnergyData d N eb` asks for a convex `g` whose right derivative is the wired density
and whose left derivative is the free density of the box edge `eb`, at `q = 2`. For `t' < t`
convexity gives `g'₊(t') ≤ g'₋(t)`, which is `fsc_secant`; feeding it into
`fk_uniqueness_off_countable_q2_full` gives `fk_uniqueness_q2_secant_from_freeEnergyData`.
The softplus function `log (1 + eᵗ)` is convex with derivative `fsc_logistic`, so the shape of
`fsc_FreeEnergyData` is satisfiable (`fsc_freeEnergyData_satisfiable`); this does not establish
`fsc_FreeEnergyData` for the random-cluster densities, which stays a hypothesis here.

## ii. Key results

- `StatMech.FK.fsc_logistic`, `StatMech.FK.fsc_logit` : the logistic map and its inverse.
- `StatMech.FK.fsc_FreeEnergyData` : the convex free-energy hypothesis.
- `StatMech.FK.fsc_secant` : `θ^w(p') ≤ θ^f(p)` for `p' < p` under the hypothesis.
- `StatMech.FK.fsc_freeEnergyData_satisfiable` : softplus realizes the derivative shape.
- `StatMech.FK.fk_uniqueness_q2_secant_from_freeEnergyData` : uniqueness of the edge marginal
  off a countable set, under the hypothesis.

## iii. Table of contents

- A. The logistic reparametrization
- B. The convex free-energy hypothesis and its consequences
- C. Softplus

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 4.

-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

/-!

## A. The logistic reparametrization

-/

/-- The logistic map `t ↦ eᵗ / (1 + eᵗ)`, equal to Mathlib's `Real.sigmoid`
(`fsc_logistic_eq_sigmoid`). -/
noncomputable def fsc_logistic (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t)

/-- The logit `p ↦ log (p / (1 - p))`, inverse to `fsc_logistic` on `(0, 1)`. -/
noncomputable def fsc_logit (p : ℝ) : ℝ := Real.log (p / (1 - p))

/-- The logistic map is Mathlib's `Real.sigmoid`. -/
lemma fsc_logistic_eq_sigmoid : fsc_logistic = Real.sigmoid := by
  funext t
  rw [fsc_logistic, Real.sigmoid_def, Real.exp_neg]
  field_simp
  ring

lemma fsc_logistic_pos (t : ℝ) : 0 < fsc_logistic t := by
  unfold fsc_logistic; positivity

lemma fsc_logistic_lt_one (t : ℝ) : fsc_logistic t < 1 := by
  unfold fsc_logistic
  rw [div_lt_one (by positivity)]
  have := Real.exp_pos t; linarith

lemma fsc_logistic_mem_Ioo (t : ℝ) : fsc_logistic t ∈ Ioo (0 : ℝ) 1 :=
  ⟨fsc_logistic_pos t, fsc_logistic_lt_one t⟩

lemma fsc_logistic_strictMono : StrictMono fsc_logistic := by
  intro a b hab
  unfold fsc_logistic
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have h1 := Real.exp_pos a
  have h2 := Real.exp_pos b
  have he : Real.exp a < Real.exp b := Real.exp_lt_exp.mpr hab
  nlinarith [he, h1, h2]

lemma fsc_logistic_logit {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    fsc_logistic (fsc_logit p) = p := by
  unfold fsc_logistic fsc_logit
  have h1mp : 0 < 1 - p := by linarith
  rw [Real.exp_log (by positivity)]
  field_simp
  ring

/-!

## B. The convex free-energy hypothesis and its consequences

-/

/-- The convex free-energy hypothesis for the box edge `eb` at `q = 2`: some convex `g` has
right derivative `t ↦ θ^w(fsc_logistic t)` and left derivative `t ↦ θ^f(fsc_logistic t)`, the wired
and free infinite-volume densities of the edge. -/
def fsc_FreeEnergyData (d N : ℕ) (eb : Sym2 (boxVerts d N)) : Prop :=
  ∃ g : ℝ → ℝ, ConvexOn ℝ univ g
    ∧ (∀ t, wiredEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic t) = pressureRightDeriv g t)
    ∧ (∀ t, freeEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic t) = pressureLeftDeriv g t)

/-- Under `fsc_FreeEnergyData`, the wired edge density at `p'` is at most the free edge density
at `p` whenever `p' < p`. -/
lemma fsc_secant (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hdata : fsc_FreeEnergyData d N eb) :
    ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p'
        ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p := by
  obtain ⟨g, hg, hwired, hfree⟩ := hdata
  intro p hp p' hp' hlt
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hp'0, hp'1⟩ := hp'
  set t := fsc_logit p with ht
  set t' := fsc_logit p' with ht'
  have hpt : fsc_logistic t = p := fsc_logistic_logit hp0 hp1
  have hpt' : fsc_logistic t' = p' := fsc_logistic_logit hp'0 hp'1
  have htlt : t' < t := by
    by_contra hge
    rw [not_lt] at hge
    have := fsc_logistic_strictMono.monotone hge
    rw [hpt, hpt'] at this
    linarith
  have hw : wiredEdgeDensity d 2 (edgeIncl d N eb) p' = pressureRightDeriv g t' := by
    rw [← hpt']; exact hwired t'
  have hf : freeEdgeDensity d 2 (edgeIncl d N eb) p = pressureLeftDeriv g t := by
    rw [← hpt]; exact hfree t
  rw [hw, hf]
  exact pressureRightDeriv_le_leftDeriv_of_lt hg htlt

/-!

## C. Softplus

-/

/-- The softplus function `t ↦ log (1 + eᵗ)`. -/
noncomputable def fsc_softplus (t : ℝ) : ℝ := Real.log (1 + Real.exp t)

lemma fsc_softplus_hasDerivAt (t : ℝ) :
    HasDerivAt fsc_softplus (fsc_logistic t) t := by
  unfold fsc_softplus fsc_logistic
  have he : HasDerivAt (fun t => 1 + Real.exp t) (Real.exp t) t := by
    simpa using (Real.hasDerivAt_exp t).const_add 1
  have hpos : (1 : ℝ) + Real.exp t ≠ 0 := by positivity
  have := he.log hpos
  convert this using 1

lemma fsc_deriv_softplus : deriv fsc_softplus = fsc_logistic := by
  funext t; exact (fsc_softplus_hasDerivAt t).deriv

lemma fsc_softplus_differentiable : Differentiable ℝ fsc_softplus :=
  fun t => (fsc_softplus_hasDerivAt t).differentiableAt

lemma fsc_softplus_convexOn : ConvexOn ℝ univ fsc_softplus := by
  apply MonotoneOn.convexOn_of_deriv convex_univ
  · exact fsc_softplus_differentiable.continuous.continuousOn
  · exact fsc_softplus_differentiable.differentiableOn
  · rw [fsc_deriv_softplus, interior_univ]
    exact fsc_logistic_strictMono.monotone.monotoneOn _

lemma fsc_softplus_pressureRightDeriv (t : ℝ) :
    pressureRightDeriv fsc_softplus t = fsc_logistic t := by
  unfold pressureRightDeriv
  rw [(fsc_softplus_hasDerivAt t).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi t)]

lemma fsc_softplus_pressureLeftDeriv (t : ℝ) :
    pressureLeftDeriv fsc_softplus t = fsc_logistic t := by
  unfold pressureLeftDeriv
  rw [(fsc_softplus_hasDerivAt t).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio t)]

/-- Softplus is a convex function whose one-sided derivatives are both `fsc_logistic`, so the
derivative conditions in `fsc_FreeEnergyData` can hold for some convex function. -/
lemma fsc_freeEnergyData_satisfiable :
    ∃ g : ℝ → ℝ, ConvexOn ℝ univ g
      ∧ (∀ t, fsc_logistic t = pressureRightDeriv g t)
      ∧ (∀ t, fsc_logistic t = pressureLeftDeriv g t) :=
  ⟨fsc_softplus, fsc_softplus_convexOn,
    fun t => (fsc_softplus_pressureRightDeriv t).symm,
    fun t => (fsc_softplus_pressureLeftDeriv t).symm⟩

/-- Under `fsc_FreeEnergyData`, at `q = 2` there is a countable set `S` of parameters off which
every measure `φ` whose box-edge marginal lies between the free and wired ones has the same
marginal as both. -/
lemma fk_uniqueness_q2_secant_from_freeEnergyData (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hdata : fsc_FreeEnergyData d N eb) :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ p ∉ S, ∀ (hp : 0 < p) (hp1 : p < 1)
        (phi : Measure (ConfigSpace (Sym2 (Site d)))),
        ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
            (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ phi.real
              (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
          ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
              ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
                  (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) →
        phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
            = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
                (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
          ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
              = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
                  (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) :=
  fk_uniqueness_off_countable_q2_full d N eb (fsc_secant d N eb hdata)

end FK

end StatMech
