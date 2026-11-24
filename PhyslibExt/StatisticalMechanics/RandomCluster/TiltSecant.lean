/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.UniquenessFromSecant
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# An eventual tilt criterion for edge-density comparison

## i. Overview

Suppose `q ≥ 1`, `0 < λ < 1`, and real sequences `V n > 0`, `V n → ∞` and
`S n / V n → 0` satisfy, for each `ε > 0`,
`ε ≤ q ^ (S n) λ ^ ((b - a - 2ε) V n) / ε` for all sufficiently large `n`.
Taking logarithms and dividing by `V n` gives `b - a - 2ε ≤ 0`, so `b ≤ a`.

`FKSecantData` specializes this abstract criterion to wired and free edge densities at `q = 2`.
It is equivalent to the comparison `θ^w(p') ≤ θ^f(p)` for all `0 < p' < p < 1`.
For the converse, `S n = 0` and `V n = n + 1` suffice. These sequences need not be surface and
volume counts of boxes, and the criterion gives no independent finite-volume proof of the
comparison.
The conditional marginal uniqueness result applies `fk_uniqueness_off_countable_q2_full`.

## ii. Key results

- `StatMech.FK.secant_exponent_le_zero` : the volume-growth lemma.
- `StatMech.FK.secant_b_le_a_of_eventualTiltBound` : `b ≤ a` from the eventual tilt bound.
- `StatMech.FK.FKSecantData` : the abstract eventual tilt criterion for one box pair at `q = 2`.
- `StatMech.FK.hsecant_discharged` : `θ^w(p') ≤ θ^f(p)` for `p' < p` under `FKSecantData`.
- `StatMech.FK.fkSecantData_iff_secant` : equivalence of the criterion and the comparison.
- `StatMech.FK.fk_uniqueness_q2_secant_of_eventualTiltCriterion` : uniqueness of the edge
  marginal off a countable set, under `FKSecantData`.

## iii. Table of contents

- A. The volume-growth lemma
- B. The eventual tilt criterion and its consequences

## iv. References

- For the finite-volume random-cluster comparison, see G. Grimmett, *The Random-Cluster Model*,
  Springer (2006), Chapter 4.

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

/-- If `ε ≤ q ^ (S n) λ ^ (m V n) / ε` for all sufficiently large `n`, with `q ≥ 1`,
`0 < λ < 1`, `ε > 0`, `V n > 0`, `V n → ∞` and `S n / V n → 0`, then `m ≤ 0`. -/
lemma secant_exponent_le_zero {q lam m ε : ℝ}
    (hq : 1 ≤ q) (hlampos : 0 < lam) (hlam1 : lam < 1) (hε : 0 < ε)
    {S V : ℕ → ℝ} (hVpos : ∀ n, 0 < V n)
    (hSV : Tendsto (fun n => S n / V n) atTop (𝓝 0))
    (hVinf : Tendsto V atTop atTop)
    (hineq : ∀ᶠ n in atTop, ε ≤ q ^ (S n) * lam ^ (m * V n) / ε) :
    m ≤ 0 := by
  have hqpos : 0 < q := lt_of_lt_of_le one_pos hq
  have hloglam : Real.log lam < 0 := Real.log_neg hlampos hlam1
  have hlogineq : ∀ᶠ n in atTop,
      2 * Real.log ε ≤ (S n) * Real.log q + m * V n * Real.log lam := by
    refine hineq.mono fun n hn => ?_
    have h2 : ε ^ 2 ≤ q ^ (S n) * lam ^ (m * V n) := by
      rw [le_div_iff₀ hε] at hn; nlinarith [hn]
    have hlog := Real.log_le_log (by positivity) h2
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hqpos _))
        (ne_of_gt (Real.rpow_pos_of_pos hlampos _)),
      Real.log_rpow hqpos, Real.log_rpow hlampos, Real.log_pow] at hlog
    push_cast at hlog
    nlinarith [hlog]
  by_contra hpos
  rw [not_le] at hpos
  have hdiv : ∀ᶠ n in atTop,
      2 * Real.log ε / V n ≤ (S n / V n) * Real.log q + m * Real.log lam := by
    refine hlogineq.mono fun n hn => ?_
    have hVn : V n ≠ 0 := ne_of_gt (hVpos n)
    rw [div_le_iff₀ (hVpos n)]
    have hexp : ((S n / V n) * Real.log q + m * Real.log lam) * V n
        = (S n) * Real.log q + m * V n * Real.log lam := by field_simp
    rwa [hexp]
  have hLHS : Tendsto (fun n => 2 * Real.log ε / V n) atTop (𝓝 0) := by
    have : Tendsto (fun n => (2 * Real.log ε) * (V n)⁻¹) atTop (𝓝 ((2 * Real.log ε) * 0)) :=
      Tendsto.const_mul _ hVinf.inv_tendsto_atTop
    simpa [div_eq_mul_inv] using this
  have hRHS : Tendsto (fun n => (S n / V n) * Real.log q + m * Real.log lam) atTop
      (𝓝 (0 * Real.log q + m * Real.log lam)) :=
    Tendsto.add (hSV.mul_const _) tendsto_const_nhds
  rw [zero_mul, zero_add] at hRHS
  have hlimle : (0 : ℝ) ≤ m * Real.log lam :=
    le_of_tendsto_of_tendsto hLHS hRHS hdiv
  nlinarith [mul_pos hpos (neg_pos.mpr hloglam)]

/-- If for every `ε > 0` the bound `ε ≤ q ^ (S n) λ ^ ((b - a - 2ε) V n) / ε` holds for all
sufficiently large `n`, with `q ≥ 1`, `0 < λ < 1`, `V n > 0`, `V n → ∞` and `S n = o(V n)`,
then `b ≤ a`. -/
lemma secant_b_le_a_of_eventualTiltBound {q lam a b : ℝ}
    (hq : 1 ≤ q) (hlampos : 0 < lam) (hlam1 : lam < 1)
    {S V : ℕ → ℝ} (hVpos : ∀ n, 0 < V n)
    (hSV : Tendsto (fun n => S n / V n) atTop (𝓝 0))
    (hVinf : Tendsto V atTop atTop)
    (hfv : ∀ ε > 0, ∀ᶠ n in atTop,
      ε ≤ q ^ (S n) * lam ^ ((b - a - 2 * ε) * V n) / ε) :
    b ≤ a := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hm : b - a - 2 * (ε / 2) ≤ 0 :=
    secant_exponent_le_zero hq hlampos hlam1 (half_pos hε) hVpos hSV hVinf
      (hfv (ε / 2) (half_pos hε))
  linarith

/-- Deprecated name for `secant_b_le_a_of_eventualTiltBound`. The bound is an abstract
hypothesis, not an estimate derived from finite-volume measures. -/
@[deprecated (since := "2026-11-23")]
alias secant_b_le_a_of_finiteVolumeData := secant_b_le_a_of_eventualTiltBound

/-!

## B. The eventual tilt criterion and its consequences

-/

/-- Abstract eventual tilt criterion for the box pair `eb` at `q = 2`. There exist real
sequences `S` and `V` with `V n > 0`, `V n → ∞` and `S n / V n → 0` such that, for each
`0 < p' < p < 1` and `ε > 0`, eventually
`ε ≤ 2 ^ (S n) λ ^ ((θ^w(p') - θ^f(p) - 2ε) V n) / ε`, where `λ = tiltFactor p p'` and
`θ^w`, `θ^f` are the wired and free infinite-volume edge densities. `S` and `V` need not be box
counts. The criterion is equivalent to the secant comparison, not a finite-box estimate. -/
def FKSecantData (d N : ℕ) (eb : Sym2 (boxVerts d N)) : Prop :=
  ∃ S V : ℕ → ℝ, (∀ n, 0 < V n)
    ∧ Tendsto (fun n => S n / V n) atTop (𝓝 0)
    ∧ Tendsto V atTop atTop
    ∧ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p → ∀ ε > 0, ∀ᶠ n in atTop,
        ε ≤ (2 : ℝ) ^ (S n)
          * (tiltFactor p p')
              ^ ((wiredEdgeDensity d 2 (edgeIncl d N eb) p'
                    - freeEdgeDensity d 2 (edgeIncl d N eb) p - 2 * ε) * V n) / ε

/-- The forward implication of the eventual tilt criterion: under `FKSecantData`, the wired
edge density at `p'` is at most the free edge density at `p` for `0 < p' < p < 1`. -/
lemma hsecant_discharged (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hdata : FKSecantData d N eb) :
    ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p'
        ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p := by
  obtain ⟨S, V, hVpos, hSV, hVinf, hineq⟩ := hdata
  intro p hp p' hp' hlt
  have hlampos : 0 < tiltFactor p p' := tiltFactor_pos hp.1 hp.2 hp'.1 hp'.2
  have hlam1 : tiltFactor p p' < 1 := tiltFactor_lt_one hp.1 hp.2 hlt
  exact secant_b_le_a_of_eventualTiltBound (q := (2 : ℝ)) (by norm_num) hlampos hlam1
    hVpos hSV hVinf (hineq p hp p' hp' hlt)

/-- The abstract eventual tilt criterion for a box pair at $q = 2$ holds exactly when the
wired edge density at $p'$ is at most the free edge density at $p$ for every $0 < p' < p < 1$.
In the reverse direction one can take $S_n = 0$ and $V_n = n + 1$. For each parameter pair
and each positive tolerance, the exponent coefficient is strictly negative, so the tilt power
tends to infinity. This uses no finite-box FK measures. -/
lemma fkSecantData_iff_secant (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    FKSecantData d N eb ↔
      ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
        wiredEdgeDensity d 2 (edgeIncl d N eb) p'
          ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p := by
  refine ⟨hsecant_discharged d N eb, fun hsecant => ?_⟩
  have hV : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [tendsto_atTop.mp (tendsto_natCast_atTop_atTop (R := ℝ)) b] with n hn
    linarith
  refine ⟨fun _ => 0, fun n => (n : ℝ) + 1, fun n => by positivity, ?_, hV, ?_⟩
  · simpa only [zero_div] using tendsto_const_nhds
  intro p hp p' hp' hlt ε hε
  have hlampos : 0 < tiltFactor p p' := tiltFactor_pos hp.1 hp.2 hp'.1 hp'.2
  have hlam1 : tiltFactor p p' < 1 := tiltFactor_lt_one hp.1 hp.2 hlt
  have hm : wiredEdgeDensity d 2 (edgeIncl d N eb) p' -
      freeEdgeDensity d 2 (edgeIncl d N eb) p - 2 * ε < 0 := by
    linarith [hsecant p hp p' hp' hlt]
  have htilt := (tendsto_rpow_atBot_of_base_lt_one _ hlampos hlam1).comp
    (hV.const_mul_atTop_of_neg hm)
  filter_upwards [tendsto_atTop.mp htilt (ε * ε)] with n hn
  rwa [le_div_iff₀ hε, Real.rpow_zero, one_mul]

/-- Under the abstract eventual tilt criterion `FKSecantData` (equivalently the secant
comparison), at `q = 2` there is a countable set `S` of parameters off which every measure `φ`
whose box-edge marginal lies between the free and wired ones has the same marginal as both. -/
lemma fk_uniqueness_q2_secant_of_eventualTiltCriterion (d N : ℕ) (eb : Sym2 (boxVerts d N))
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

/-- Deprecated name for `fk_uniqueness_q2_secant_of_eventualTiltCriterion`. This is conditional
edge-marginal uniqueness under the abstract criterion, not a finite-volume derivation. -/
@[deprecated (since := "2026-11-23")]
alias fk_uniqueness_q2_secant_from_finiteVolumeData :=
  fk_uniqueness_q2_secant_of_eventualTiltCriterion

end FK

end StatMech
