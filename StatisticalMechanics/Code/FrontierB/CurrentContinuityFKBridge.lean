/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FK.FKUniquenessSkeleton
import Code.FK.FKGeneralQTranslation
import Code.FK.CylinderDecayClose
import Code.FK.FKTwoBoxDecoupling

open MeasureTheory Set

namespace StatMech
namespace FrontierB

open ConfigSpace FK Lattice

variable {d : ℕ}

section FiniteEdwardsSokal

open Potts

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



private def esCoeffOpen {q : ℕ} (p : ℝ) (sigma : V → Fin q)
    (target e : Sym2 V) (b : Bool) : ℝ :=
  esCoeff G p sigma e b *
    if e = target then (if b then 1 else 0) else 1

private theorem esWeight_mul_open_eq_prod {q : ℕ} (p : ℝ)
    (sigma : V → Fin q) (omega : ConfigSpace (Sym2 V)) (target : Sym2 V) :
    esWeight G p sigma omega * (if omega target then 1 else 0) =
      ∏ e : Sym2 V, esCoeffOpen G p sigma target e (omega e) := by
  rw [esWeight_eq_prod_univ]
  by_cases htarget : omega target = true
  · rw [if_pos htarget, mul_one]
    apply Finset.prod_congr rfl
    intro e _
    unfold esCoeffOpen
    by_cases he : e = target
    · subst e
      simp [htarget]
    · simp [he]
  · simp only [Bool.not_eq_true] at htarget
    rw [if_neg (by simpa using htarget), mul_zero]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ target)
    simp [esCoeffOpen, htarget]

private theorem esCoeffOpen_bool_sum {q : ℕ} (p : ℝ)
    (sigma : V → Fin q) (target : Sym2 V)
    (htarget : target ∈ G.edgeFinset) (e : Sym2 V) :
    (∑ b : Bool, esCoeffOpen G p sigma target e b) =
      if e = target then p * monoIndicator sigma target
      else ∑ b : Bool, esCoeff G p sigma e b := by
  by_cases he : e = target
  · subst e
    simp [esCoeffOpen, esCoeff, htarget]
  · simp [esCoeffOpen, he]



theorem esWeight_open_sum_eq (q : ℕ) (p : ℝ) (sigma : V → Fin q)
    (target : Sym2 V) (htarget : target ∈ G.edgeFinset) :
    (∑ omega : ConfigSpace (Sym2 V),
        esWeight G p sigma omega * (if omega target then 1 else 0)) =
      p * monoIndicator sigma target *
        ∑ omega : ConfigSpace (Sym2 V), esWeight G p sigma omega := by
  rw [Finset.sum_congr rfl
      (fun omega _ => esWeight_mul_open_eq_prod G p sigma omega target),
    ← Fintype.prod_sum]
  simp_rw [esCoeffOpen_bool_sum G p sigma target htarget]
  rw [show (∑ omega : ConfigSpace (Sym2 V), esWeight G p sigma omega) =
      ∏ e : Sym2 V, ∑ b : Bool, esCoeff G p sigma e b by
        simp_rw [esWeight_eq_prod_univ]
        exact (Fintype.prod_sum
          (fun e : Sym2 V => fun b : Bool => esCoeff G p sigma e b)).symm]
  induction target with
  | _ x y =>
      rw [monoIndicator_mk]
      by_cases hxy : sigma x = sigma y
      · simp only [if_pos hxy, mul_one]
        calc
          (∏ e : Sym2 V,
              if e = s(x, y) then p else ∑ b : Bool, esCoeff G p sigma e b) =
              p * ∏ e ∈ (Finset.univ.erase s(x, y)),
                ∑ b : Bool, esCoeff G p sigma e b := by
            rw [← Finset.mul_prod_erase Finset.univ
              (fun e => if e = s(x, y) then p else ∑ b : Bool, esCoeff G p sigma e b)
              (Finset.mem_univ s(x, y))]
            simp only [if_pos]
            congr 1
            apply Finset.prod_congr rfl
            intro e he
            rw [if_neg (Finset.ne_of_mem_erase he)]
          _ = p * ∏ e : Sym2 V, ∑ b : Bool, esCoeff G p sigma e b := by
            congr 1
            apply Finset.prod_erase
            rw [esCoeff_bool_sum, if_pos htarget, monoIndicator_mk, if_pos hxy]
            ring
      · simp only [if_neg hxy, mul_zero]
        rw [zero_mul]
        apply Finset.prod_eq_zero (Finset.mem_univ s(x, y))
        simp



theorem edgeMargProb_fkProb_eq_p_mul_esMono (q : ℕ) (p : ℝ)
    (target : Sym2 V) (htarget : target ∈ G.edgeFinset) :
    edgeMargProb (fkProb G p (q : ℝ)) target =
      p * ∑ sigma : V → Fin q,
        esFirstMarginal G q p sigma * monoIndicator sigma target := by
  have hedge : fkProb G p (q : ℝ) = esSecondMarginal G q p := by
    funext omega
    exact (esSecondMarginal_eq_fkProb G q p omega).symm
  rw [hedge]
  unfold edgeMargProb esSecondMarginal esFirstMarginal
  have hnum :
      (∑ omega : ConfigSpace (Sym2 V),
          (if omega target then 1 else 0) *
            ∑ sigma : V → Fin q, esWeight G p sigma omega) =
        p * ∑ sigma : V → Fin q,
          (∑ omega : ConfigSpace (Sym2 V), esWeight G p sigma omega) *
            monoIndicator sigma target := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro sigma _
    calc
      (∑ omega : ConfigSpace (Sym2 V),
          (if omega target then 1 else 0) * esWeight G p sigma omega) =
          ∑ omega : ConfigSpace (Sym2 V),
            esWeight G p sigma omega * (if omega target then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro omega _
        ring
      _ = p * monoIndicator sigma target *
          ∑ omega : ConfigSpace (Sym2 V), esWeight G p sigma omega :=
        esWeight_open_sum_eq G q p sigma target htarget
      _ = p * ((∑ omega : ConfigSpace (Sym2 V), esWeight G p sigma omega) *
          monoIndicator sigma target) := by ring
  calc
    (∑ omega : ConfigSpace (Sym2 V),
        (if omega target then 1 else 0) *
          ((∑ sigma : V → Fin q, esWeight G p sigma omega) / esZ G q p)) =
        (∑ omega : ConfigSpace (Sym2 V),
          (if omega target then 1 else 0) *
            ∑ sigma : V → Fin q, esWeight G p sigma omega) / esZ G q p := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro omega _
      ring
    _ = (p * ∑ sigma : V → Fin q,
          (∑ omega : ConfigSpace (Sym2 V), esWeight G p sigma omega) *
            monoIndicator sigma target) / esZ G q p := by rw [hnum]
    _ = p * ∑ sigma : V → Fin q,
        ((∑ omega : ConfigSpace (Sym2 V), esWeight G p sigma omega) / esZ G q p) *
          monoIndicator sigma target := by
      rw [mul_div_assoc]
      congr 1
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro sigma _
      ring

end FiniteEdwardsSokal

private theorem freeInfiniteVolume_congr
    {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp1₁ : p₁ < 1)
    (hp₂ : 0 < p₂) (hp1₂ : p₂ < 1) (h : p₁ = p₂) :
    (freeInfiniteVolume d hp₁ hp1₁ (by norm_num : (0 : ℝ) < 2) :
        Measure (ConfigSpace (Sym2 (Site d)))) =
      (freeInfiniteVolume d hp₂ hp1₂ (by norm_num : (0 : ℝ) < 2) :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  subst p₂
  rfl

private theorem wiredInfiniteVolume_congr
    {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp1₁ : p₁ < 1)
    (hp₂ : 0 < p₂) (hp1₂ : p₂ < 1) (h : p₁ = p₂) :
    (wiredInfiniteVolume d hp₁ hp1₁ (by norm_num : (0 : ℝ) < 2) :
        Measure (ConfigSpace (Sym2 (Site d)))) =
      (wiredInfiniteVolume d hp₂ hp1₂ (by norm_num : (0 : ℝ) < 2) :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  subst p₂
  rfl









theorem freeInfiniteVolume_eq_wiredInfiniteVolume_of_edgeDensity_eq
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdens : ∀ (N : ℕ) (e : Sym2 (boxVerts d N)),
      freeEdgeDensity d 2 (edgeIncl d N e) p =
        wiredEdgeDensity d 2 (edgeIncl d N e) p) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) :
        Measure (ConfigSpace (Sym2 (Site d)))) =
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  classical
  apply fkgqt_measure_eq_of_multiOpen_eq
  intro T
  obtain ⟨N, t, hT⟩ := cdc_finset_in_box T
  let s : ℝ := fsc_logit p
  obtain ⟨P, hP⟩ := fuc_hcoup d N s
  have hmarg : ∀ e : Sym2 (boxVerts d N),
      edgeMargProb (fuc_freeMass d N s) e =
        edgeMargProb (fuc_wiredMass d N s) e := by
    intro e
    rw [fuc_edgeMargProb_free, fuc_edgeMargProb_wired]
    simpa [s, fsc_logistic_logit hp hp1] using hdens N e
  have hevent := fk_unique_of_edgeMarg_eq hP hmarg
    (cdc_boxMultiOpenEvent_isIncreasing N t)
  rw [fuc_eventMassProb_free, fuc_eventMassProb_wired] at hevent
  have hlog : fsc_logistic s = p := by
    simpa [s] using fsc_logistic_logit hp hp1
  have hfree := freeInfiniteVolume_congr (d := d)
    (fsc_logistic_pos s) (fsc_logistic_lt_one s) hp hp1 hlog
  have hwired := wiredInfiniteVolume_congr (d := d)
    (fsc_logistic_pos s) (fsc_logistic_lt_one s) hp hp1 hlog
  rw [hfree, hwired] at hevent
  rw [hT, ftb_fmu_eq_cdc_multiOpen,
    cdc_multiOpenEvent_image_eq_boxRestrict]
  unfold Measure.real at hevent
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) (measure_ne_top _ _)).mp hevent

end FrontierB
end StatMech
