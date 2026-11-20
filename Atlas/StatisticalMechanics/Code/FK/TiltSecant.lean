/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.FK.FKUniquenessClose3
import Code.FK.Tilt

open MeasureTheory Set Filter Topology Real
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice






































theorem secant_exponent_le_zero {q lam m ε : ℝ}
    (hq : 1 ≤ q) (hlampos : 0 < lam) (hlam1 : lam < 1) (hε : 0 < ε)
    {S V : ℕ → ℝ} (hVpos : ∀ n, 0 < V n)
    (hSV : Tendsto (fun n => S n / V n) atTop (𝓝 0))
    (hVinf : Tendsto V atTop atTop)
    (hineq : ∀ n, ε ≤ q ^ (S n) * lam ^ (m * V n) / ε) :
    m ≤ 0 := by
  have hqpos : 0 < q := lt_of_lt_of_le one_pos hq
  have hloglam : Real.log lam < 0 := Real.log_neg hlampos hlam1
  
  have hlogineq : ∀ n, 2 * Real.log ε ≤ (S n) * Real.log q + m * V n * Real.log lam := by
    intro n
    have h := hineq n
    have h2 : ε ^ 2 ≤ q ^ (S n) * lam ^ (m * V n) := by
      rw [le_div_iff₀ hε] at h; nlinarith [h]
    have hlog := Real.log_le_log (by positivity) h2
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hqpos _))
        (ne_of_gt (Real.rpow_pos_of_pos hlampos _)),
      Real.log_rpow hqpos, Real.log_rpow hlampos, Real.log_pow] at hlog
    push_cast at hlog
    nlinarith [hlog]
  
  by_contra hpos
  rw [not_le] at hpos
  
  have hdiv : ∀ n, 2 * Real.log ε / V n ≤ (S n / V n) * Real.log q + m * Real.log lam := by
    intro n
    have hVn : V n ≠ 0 := ne_of_gt (hVpos n)
    rw [div_le_iff₀ (hVpos n)]
    have hexp : ((S n / V n) * Real.log q + m * Real.log lam) * V n
        = (S n) * Real.log q + m * V n * Real.log lam := by field_simp
    rw [hexp]; exact hlogineq n
  
  have hLHS : Tendsto (fun n => 2 * Real.log ε / V n) atTop (𝓝 0) := by
    have : Tendsto (fun n => (2 * Real.log ε) * (V n)⁻¹) atTop (𝓝 ((2 * Real.log ε) * 0)) :=
      Tendsto.const_mul _ hVinf.inv_tendsto_atTop
    simpa [div_eq_mul_inv] using this
  
  have hRHS : Tendsto (fun n => (S n / V n) * Real.log q + m * Real.log lam) atTop
      (𝓝 (0 * Real.log q + m * Real.log lam)) :=
    Tendsto.add (hSV.mul_const _) tendsto_const_nhds
  rw [zero_mul, zero_add] at hRHS
  
  have hlimle : (0 : ℝ) ≤ m * Real.log lam :=
    le_of_tendsto_of_tendsto hLHS hRHS (Filter.Eventually.of_forall hdiv)
  
  nlinarith [mul_pos hpos (neg_pos.mpr hloglam)]



theorem secant_le_of_per_eps {a b : ℝ} (h : ∀ ε > 0, b ≤ a + 2 * ε) : b ≤ a := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have := h (ε / 2) (by linarith)
  linarith
















theorem secant_b_le_a_of_finiteVolumeData {q lam a b : ℝ}
    (hq : 1 ≤ q) (hlampos : 0 < lam) (hlam1 : lam < 1)
    {S V : ℕ → ℝ} (hVpos : ∀ n, 0 < V n)
    (hSV : Tendsto (fun n => S n / V n) atTop (𝓝 0))
    (hVinf : Tendsto V atTop atTop)
    (hfv : ∀ ε > 0, ∀ n, ε ≤ q ^ (S n) * lam ^ ((b - a - 2 * ε) * V n) / ε) :
    b ≤ a := by
  refine secant_le_of_per_eps (fun ε hε => ?_)
  have hm : b - a - 2 * ε ≤ 0 :=
    secant_exponent_le_zero hq hlampos hlam1 hε hVpos hSV hVinf (hfv ε hε)
  linarith
































def FKSecantData (d N : ℕ) (eb : Sym2 (boxVerts d N)) : Prop :=
  ∃ S V : ℕ → ℝ, (∀ n, 0 < V n)
    ∧ Tendsto (fun n => S n / V n) atTop (𝓝 0)
    ∧ Tendsto V atTop atTop
    ∧ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p → ∀ ε > 0, ∀ n,
        ε ≤ (2 : ℝ) ^ (S n)
          * (tiltFactor p p')
              ^ ((wiredEdgeDensity d 2 (edgeIncl d N eb) p'
                    - freeEdgeDensity d 2 (edgeIncl d N eb) p - 2 * ε) * V n) / ε















theorem hsecant_discharged (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hdata : FKSecantData d N eb) :
    ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p'
        ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p := by
  obtain ⟨S, V, hVpos, hSV, hVinf, hineq⟩ := hdata
  intro p hp p' hp' hlt
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hp'0, hp'1⟩ := hp'
  
  have hlampos : 0 < tiltFactor p p' :=
    tiltFactor_pos hp0 hp1 hp'0 hp'1
  have hlam1 : tiltFactor p p' < 1 :=
    tiltFactor_lt_one hp0 hp1 hlt
  
  exact secant_b_le_a_of_finiteVolumeData (q := (2 : ℝ)) (by norm_num) hlampos hlam1
    hVpos hSV hVinf
    (fun ε hε n => hineq p ⟨hp0, hp1⟩ p' ⟨hp'0, hp'1⟩ hlt ε hε n)
























theorem fk_uniqueness_q2_secant_from_finiteVolumeData (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hdata : FKSecantData d N eb) :
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
  fk_uniqueness_off_countable_q2_full d N eb (hsecant_discharged d N eb hdata)

end FK

end StatMech
