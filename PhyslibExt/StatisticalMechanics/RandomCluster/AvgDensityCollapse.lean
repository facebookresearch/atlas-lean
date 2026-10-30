/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKPressureDeriv
public import PhyslibExt.StatisticalMechanics.RandomCluster.DensityFiniteToInfinite
public import PhyslibExt.StatisticalMechanics.RandomCluster.BoundaryDecay

/-!
# Average edge density of boxes from interior homogeneity

An averaging estimate for values in `[0, 1]`, and the average edge density of the free `q = 2` box
measure as the average of its edge marginals.

## i. Overview

An elementary averaging estimate: for values in `[0, 1]` that are within `δ` of `L` on a subset
`I ⊆ E`, the average over `E` is within `δ + 2|E \ I| / |E|` of `L`. The average edge density of the
free `q = 2` measure on `Λ_n` is the average of its edge marginals, so the estimate applies to it.

## ii. Key results

- `adc_absavg_estimate`, `adc_absavg_tendsto` : the averaging estimate and its limit form.
- `adc_avgDensity_eq_sum_edgeMarg` : the average density is the average of the edge marginals.

## iii. Table of contents

- A. Averaging estimates
- B. Average densities of boxes

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §4.6.
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

/-! ## A. Averaging estimates -/

lemma adc_absavg_estimate {ι : Type*} [DecidableEq ι] (E I : Finset ι) (hIE : I ⊆ E)
    (f : ι → ℝ) (L δ : ℝ)
    (hf0 : ∀ e ∈ E, 0 ≤ f e) (hf1 : ∀ e ∈ E, f e ≤ 1) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (hδ : 0 ≤ δ) (hin : ∀ e ∈ I, |f e - L| ≤ δ) (hE : 0 < E.card) :
    |(1 / (E.card : ℝ)) * (∑ e ∈ E, f e) - L|
      ≤ δ + ((E.card - I.card : ℝ) / E.card) := by
  have hEcard : (0 : ℝ) < (E.card : ℝ) := by exact_mod_cast hE
  have hsum : (∑ e ∈ E, f e) - L * E.card = ∑ e ∈ E, (f e - L) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  have hsplit : ∑ e ∈ E, (f e - L) = (∑ e ∈ I, (f e - L)) + ∑ e ∈ E \ I, (f e - L) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff), Finset.union_sdiff_of_subset hIE]
  have hinner : |∑ e ∈ I, (f e - L)| ≤ I.card * δ := by
    calc |∑ e ∈ I, (f e - L)| ≤ ∑ e ∈ I, |f e - L| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ I, δ := Finset.sum_le_sum (fun e he => hin e he)
      _ = I.card * δ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hICardLe : I.card ≤ E.card := Finset.card_le_card hIE
  have hcard : ((E \ I).card : ℝ) = (E.card - I.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hIE, Nat.cast_sub hICardLe]
  have hbdy : |∑ e ∈ E \ I, (f e - L)| ≤ (E.card - I.card : ℝ) := by
    calc |∑ e ∈ E \ I, (f e - L)| ≤ ∑ e ∈ E \ I, |f e - L| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ E \ I, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro e he
          rw [Finset.mem_sdiff] at he
          rw [abs_le]
          refine ⟨by have := hf0 e he.1; linarith, by have := hf1 e he.1; linarith⟩
      _ = ((E \ I).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = (E.card - I.card : ℝ) := hcard
  have htotal : |∑ e ∈ E, (f e - L)| ≤ I.card * δ + (E.card - I.card : ℝ) := by
    rw [hsplit]
    calc |(∑ e ∈ I, (f e - L)) + ∑ e ∈ E \ I, (f e - L)|
        ≤ |∑ e ∈ I, (f e - L)| + |∑ e ∈ E \ I, (f e - L)| := abs_add_le _ _
      _ ≤ I.card * δ + (E.card - I.card : ℝ) := add_le_add hinner hbdy
  have hkey : |(1 / (E.card : ℝ)) * (∑ e ∈ E, f e) - L|
      = (1 / (E.card : ℝ)) * |∑ e ∈ E, (f e - L)| := by
    rw [← hsum]
    rw [show (1 / (E.card : ℝ)) * (∑ e ∈ E, f e) - L
          = (1 / (E.card : ℝ)) * ((∑ e ∈ E, f e) - L * E.card) by field_simp]
    rw [abs_mul, abs_of_pos (by positivity)]
  rw [hkey]
  calc (1 / (E.card : ℝ)) * |∑ e ∈ E, (f e - L)|
      ≤ (1 / (E.card : ℝ)) * (I.card * δ + (E.card - I.card : ℝ)) :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
    _ ≤ δ + ((E.card - I.card : ℝ) / E.card) := by
        rw [mul_add]
        apply add_le_add
        · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hEcard]
          calc (I.card : ℝ) * δ ≤ (E.card : ℝ) * δ :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hICardLe) hδ
            _ = δ * E.card := by ring
        · rw [one_div, ← div_eq_inv_mul]

lemma adc_absavg_tendsto {ι : ℕ → Type*} [∀ n, DecidableEq (ι n)]
    (En In : (n : ℕ) → Finset (ι n)) (fn : (n : ℕ) → ι n → ℝ) (L : ℝ) (δ : ℕ → ℝ)
    (hIE : ∀ n, In n ⊆ En n)
    (hf0 : ∀ n, ∀ e ∈ En n, 0 ≤ fn n e) (hf1 : ∀ n, ∀ e ∈ En n, fn n e ≤ 1)
    (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hin : ∀ n, ∀ e ∈ In n, |fn n e - L| ≤ δ n)
    (hE : ∀ n, 0 < (En n).card)
    (hbdy : Tendsto (fun n => (((En n).card - (In n).card : ℝ)) / (En n).card)
        atTop (𝓝 0)) :
    Tendsto (fun n => (1 / ((En n).card : ℝ)) * (∑ e ∈ En n, fn n e)) atTop (𝓝 L) := by
  have hbound : ∀ n, |(1 / ((En n).card : ℝ)) * (∑ e ∈ En n, fn n e) - L|
      ≤ δ n + (((En n).card - (In n).card : ℝ)) / (En n).card :=
    fun n => adc_absavg_estimate (En n) (In n) (hIE n) (fn n) L (δ n)
      (hf0 n) (hf1 n) hL0 hL1 (hδ0 n) (hin n) (hE n)
  have hsum0 : Tendsto (fun n => δ n + (((En n).card - (In n).card : ℝ)) / (En n).card)
      atTop (𝓝 0) := by
    have := hδlim.add hbdy; simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hsum0
  obtain ⟨N, hN⟩ := hsum0 ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [Real.dist_eq, sub_zero] at h
  rw [Real.dist_eq]
  calc |(1 / ((En n).card : ℝ)) * (∑ e ∈ En n, fn n e) - L|
      ≤ δ n + (((En n).card - (In n).card : ℝ)) / (En n).card := hbound n
    _ ≤ |δ n + (((En n).card - (In n).card : ℝ)) / (En n).card| := le_abs_self _
    _ < ε := h

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## B. Average densities of boxes -/

lemma adc_openCount_eq_sum (ω : ConfigSpace (Sym2 V)) :
    (openCount G ω : ℝ) = dfi_openEdgeCount G.edgeFinset ω := by
  unfold openCount dfi_openEdgeCount
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma adc_fkExpect_openCount_eq_sum (p : ℝ) :
    fkExpect G p 2 (fun ω => (openCount G ω : ℝ))
      = ∑ e ∈ G.edgeFinset, edgeMargProb (fkProb G p 2) e := by
  unfold fkExpect
  rw [show (fun ω => fkProb G p 2 ω * (openCount G ω : ℝ))
        = (fun ω => dfi_openEdgeCount G.edgeFinset ω * fkProb G p 2 ω) from ?_]
  · exact dfi_openEdgeCount_expect G.edgeFinset (fkProb G p 2)
  · funext ω; rw [adc_openCount_eq_sum]; ring

lemma adc_avgDensity_eq_sum_edgeMarg (t : ℝ) :
    fpd_avgDensity G t
      = (1 / (G.edgeFinset.card : ℝ))
          * ∑ e ∈ G.edgeFinset, edgeMargProb (fkProb G (fsc_logistic t) 2) e := by
  unfold fpd_avgDensity
  rw [adc_fkExpect_openCount_eq_sum]

lemma adc_edgeMargProb_fkProb_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (e : Sym2 V) : 0 ≤ edgeMargProb (fkProb G p q) e := by
  unfold edgeMargProb
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg _ (fkProb_nonneg G hp hp1 hq ω)
  split <;> norm_num

lemma adc_edgeMargProb_fkProb_le_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (e : Sym2 V) : edgeMargProb (fkProb G p q) e ≤ 1 := by
  unfold edgeMargProb
  calc ∑ ω : ConfigSpace (Sym2 V), (if ω e then (1 : ℝ) else 0) * fkProb G p q ω
      ≤ ∑ ω : ConfigSpace (Sym2 V), fkProb G p q ω := by
        apply Finset.sum_le_sum
        intro ω _
        have hb : (if ω e then (1 : ℝ) else 0) ≤ 1 := by split <;> norm_num
        calc (if ω e then (1 : ℝ) else 0) * fkProb G p q ω
            ≤ 1 * fkProb G p q ω := mul_le_mul_of_nonneg_right hb (fkProb_nonneg G hp hp1 hq ω)
          _ = fkProb G p q ω := one_mul _
    _ = 1 := fkProb_sum_eq_one G hp hp1 hq

lemma adc_edgeMargProb_fkProb_mem_Icc {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (e : Sym2 V) : edgeMargProb (fkProb G p q) e ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨adc_edgeMargProb_fkProb_nonneg G hp hp1 hq e,
    adc_edgeMargProb_fkProb_le_one G hp hp1 hq e⟩

end FK

end StatMech
