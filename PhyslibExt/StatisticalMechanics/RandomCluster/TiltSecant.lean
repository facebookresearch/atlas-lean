/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.UniquenessFromSecant
/-!
# Edge-density comparison from a tilted finite-volume bound

A volume-growth argument turning a finite-volume tilt bound into the comparison
`θ^w(p') ≤ θ^f(p)` of wired and free edge densities for `p' < p`, and hence, at `q = 2`,
uniqueness of the infinite-volume edge marginal off a countable set of `p`.

## i. Overview

Suppose volumes `V n → ∞` and surface terms `S n = o(V n)` satisfy, for every `ε > 0`,
`ε ≤ q ^ (S n) λ ^ ((b - a - 2ε) V n) / ε` with `0 < λ < 1`. Taking logarithms and dividing
by `V n` forces `b - a - 2ε ≤ 0`, so `b ≤ a` (`secant_b_le_a_of_finiteVolumeData`).
`FKSecantData d N eb` packages such data for the box edge `eb` with `q = 2`,
`λ = tiltFactor p p'`, `b` the wired edge density at `p'` and `a` the free edge density at
`p`. Under that hypothesis `hsecant_discharged` gives `θ^w(p') ≤ θ^f(p)`, and
`fk_uniqueness_q2_secant_from_finiteVolumeData` feeds this into the countable-exception
uniqueness theorem `fk_uniqueness_off_countable_q2_full`.

`FKSecantData` is an assumption here; this file does not construct it.

## ii. Key results

- `StatMech.FK.secant_exponent_le_zero` : the volume-growth lemma.
- `StatMech.FK.secant_b_le_a_of_finiteVolumeData` : `b ≤ a` from the finite-volume bound.
- `StatMech.FK.FKSecantData` : the finite-volume hypothesis for one box edge at `q = 2`.
- `StatMech.FK.hsecant_discharged` : `θ^w(p') ≤ θ^f(p)` for `p' < p` under `FKSecantData`.
- `StatMech.FK.fk_uniqueness_q2_secant_from_finiteVolumeData` : uniqueness of the edge
  marginal off a countable set, under `FKSecantData`.

## iii. Table of contents

- A. The volume-growth lemma
- B. The finite-volume hypothesis and its consequences

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 4.

-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

/-!

## A. The volume-growth lemma

-/

/-- If `ε ≤ q ^ (S n) λ ^ (m V n) / ε` for all `n`, with `q ≥ 1`, `0 < λ < 1`, `V n → ∞` and
`S n / V n → 0`, then `m ≤ 0`. -/
lemma secant_exponent_le_zero {q lam m ε : ℝ}
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

/-- If for every `ε > 0` the bound `ε ≤ q ^ (S n) λ ^ ((b - a - 2ε) V n) / ε` holds for all
`n`, with `V n → ∞` and `S n = o(V n)`, then `b ≤ a`. -/
lemma secant_b_le_a_of_finiteVolumeData {q lam a b : ℝ}
    (hq : 1 ≤ q) (hlampos : 0 < lam) (hlam1 : lam < 1)
    {S V : ℕ → ℝ} (hVpos : ∀ n, 0 < V n)
    (hSV : Tendsto (fun n => S n / V n) atTop (𝓝 0))
    (hVinf : Tendsto V atTop atTop)
    (hfv : ∀ ε > 0, ∀ n, ε ≤ q ^ (S n) * lam ^ ((b - a - 2 * ε) * V n) / ε) :
    b ≤ a := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hm : b - a - 2 * (ε / 2) ≤ 0 :=
    secant_exponent_le_zero hq hlampos hlam1 (half_pos hε) hVpos hSV hVinf
      (hfv (ε / 2) (half_pos hε))
  linarith

/-!

## B. The finite-volume hypothesis and its consequences

-/

/-- Finite-volume tilt data for the box edge `eb` at `q = 2`: volumes `V n → ∞` and surface
terms `S n = o(V n)` such that, for all `p' < p` in `(0, 1)` and `ε > 0`,
`ε ≤ 2 ^ (S n) λ ^ ((θ^w(p') - θ^f(p) - 2ε) V n) / ε` with `λ = tiltFactor p p'`, where `θ^w` and
`θ^f` are the wired and free infinite-volume densities of the edge. -/
def FKSecantData (d N : ℕ) (eb : Sym2 (boxVerts d N)) : Prop :=
  ∃ S V : ℕ → ℝ, (∀ n, 0 < V n)
    ∧ Tendsto (fun n => S n / V n) atTop (𝓝 0)
    ∧ Tendsto V atTop atTop
    ∧ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p → ∀ ε > 0, ∀ n,
        ε ≤ (2 : ℝ) ^ (S n)
          * (tiltFactor p p')
              ^ ((wiredEdgeDensity d 2 (edgeIncl d N eb) p'
                    - freeEdgeDensity d 2 (edgeIncl d N eb) p - 2 * ε) * V n) / ε

/-- Under `FKSecantData`, the wired edge density at `p'` is at most the free edge density at
`p` whenever `p' < p`. -/
lemma hsecant_discharged (d N : ℕ) (eb : Sym2 (boxVerts d N))
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

/-- Under `FKSecantData`, at `q = 2` there is a countable set `S` of parameters off which every
measure `φ` whose box-edge marginal lies between the free and wired ones has the same marginal
as both. -/
lemma fk_uniqueness_q2_secant_from_finiteVolumeData (d N : ℕ) (eb : Sym2 (boxVerts d N))
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
