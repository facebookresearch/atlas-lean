/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Mathlib
import Code.FK.PressureDiff
import Code.FK.TiltSecant
import Code.FK.FKUniquenessClose3

open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice













noncomputable def fsc_logistic (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t)



noncomputable def fsc_logit (p : ℝ) : ℝ := Real.log (p / (1 - p))


theorem fsc_logistic_pos (t : ℝ) : 0 < fsc_logistic t := by
  unfold fsc_logistic; positivity




theorem fsc_logistic_lt_one (t : ℝ) : fsc_logistic t < 1 := by
  unfold fsc_logistic
  rw [div_lt_one (by positivity)]
  have := Real.exp_pos t; linarith


theorem fsc_logistic_mem_Ioo (t : ℝ) : fsc_logistic t ∈ Ioo (0 : ℝ) 1 :=
  ⟨fsc_logistic_pos t, fsc_logistic_lt_one t⟩





theorem fsc_logistic_strictMono : StrictMono fsc_logistic := by
  intro a b hab
  unfold fsc_logistic
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have h1 := Real.exp_pos a
  have h2 := Real.exp_pos b
  have he : Real.exp a < Real.exp b := Real.exp_lt_exp.mpr hab
  nlinarith [he, h1, h2]




theorem fsc_logistic_logit {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    fsc_logistic (fsc_logit p) = p := by
  unfold fsc_logistic fsc_logit
  have h1mp : 0 < 1 - p := by linarith
  rw [Real.exp_log (by positivity)]
  field_simp
  ring



























def fsc_FreeEnergyData (d N : ℕ) (eb : Sym2 (boxVerts d N)) : Prop :=
  ∃ g : ℝ → ℝ, ConvexOn ℝ univ g
    ∧ (∀ t, wiredEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic t) = pressureRightDeriv g t)
    ∧ (∀ t, freeEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic t) = pressureLeftDeriv g t)



























theorem fsc_secant (d N : ℕ) (eb : Sym2 (boxVerts d N))
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












noncomputable def fsc_softplus (t : ℝ) : ℝ := Real.log (1 + Real.exp t)


theorem fsc_softplus_hasDerivAt (t : ℝ) :
    HasDerivAt fsc_softplus (fsc_logistic t) t := by
  unfold fsc_softplus fsc_logistic
  have he : HasDerivAt (fun t => 1 + Real.exp t) (Real.exp t) t := by
    simpa using (Real.hasDerivAt_exp t).const_add 1
  have hpos : (1 : ℝ) + Real.exp t ≠ 0 := by positivity
  have := he.log hpos
  convert this using 1


theorem fsc_deriv_softplus : deriv fsc_softplus = fsc_logistic := by
  funext t; exact (fsc_softplus_hasDerivAt t).deriv


theorem fsc_softplus_differentiable : Differentiable ℝ fsc_softplus :=
  fun t => (fsc_softplus_hasDerivAt t).differentiableAt


theorem fsc_softplus_convexOn : ConvexOn ℝ univ fsc_softplus := by
  apply MonotoneOn.convexOn_of_deriv convex_univ
  · exact fsc_softplus_differentiable.continuous.continuousOn
  · exact fsc_softplus_differentiable.differentiableOn
  · rw [fsc_deriv_softplus, interior_univ]
    exact fsc_logistic_strictMono.monotone.monotoneOn _


theorem fsc_softplus_pressureRightDeriv (t : ℝ) :
    pressureRightDeriv fsc_softplus t = fsc_logistic t := by
  unfold pressureRightDeriv
  rw [(fsc_softplus_hasDerivAt t).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi t)]


theorem fsc_softplus_pressureLeftDeriv (t : ℝ) :
    pressureLeftDeriv fsc_softplus t = fsc_logistic t := by
  unfold pressureLeftDeriv
  rw [(fsc_softplus_hasDerivAt t).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio t)]













theorem fsc_freeEnergyData_satisfiable :
    ∃ g : ℝ → ℝ, ConvexOn ℝ univ g
      ∧ (∀ t, fsc_logistic t = pressureRightDeriv g t)
      ∧ (∀ t, fsc_logistic t = pressureLeftDeriv g t) :=
  ⟨fsc_softplus, fsc_softplus_convexOn,
    fun t => (fsc_softplus_pressureRightDeriv t).symm,
    fun t => (fsc_softplus_pressureLeftDeriv t).symm⟩
























theorem fk_uniqueness_q2_secant_from_freeEnergyData (d N : ℕ) (eb : Sym2 (boxVerts d N))
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
