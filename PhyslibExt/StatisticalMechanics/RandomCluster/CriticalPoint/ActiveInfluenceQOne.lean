/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ActiveInfluence
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.MaxInfluencePBiased
public import CSLibExt.Complexity.BooleanFunctions.CovLowerBound

/-!
# Active influences at q = 1

At `q = 1` the active random-cluster measure is the product Bernoulli measure, so the active
influence is the usual Boolean influence and KKL-type bounds apply.

## i. Overview

The file identifies the active random-cluster objects at `q = 1` (weight, partition function, mean,
covariance, open marginal) with their Bernoulli counterparts from the OSSS library, and transfers
maximal-influence bounds. `maxActiveInfluence_half` (`p = 1/2`) and
`maxActiveInfluence_qOne_corrected` are unconditional.
`maxActiveInfluence_qOne_compactWindow_of_bkkkl_u0` is conditional on the `p`-biased
hypercontractivity hypothesis `Hpb : kpb_PBiasedHC (1 - ε / 2)`.

## ii. Key results

- `activeInfluence_one_eq_influence`: at `q = 1` active influence is Bernoulli influence.
- `maxActiveInfluence_half`: KKL lower bound on the maximal influence at `p = 1/2` (unconditional).
- `maxActiveInfluence_qOne_compactWindow_of_bkkkl_u0`: the same bound for `p ∈ [ε, 1 - ε]`,
  conditional on `Hpb`.

## iii. Table of contents

- A. Reduction to the Bernoulli measure
- B. Maximal influence bounds

## iv. References

* J. Kahn, G. Kalai, N. Linial, *The influence of variables on Boolean functions*, FOCS 1988.
* M. Talagrand, *On Russo's approximate zero-one law*, Ann. Probab. 22 (1994).
-/

@[expose] public section

open scoped BigOperators
open Finset Set

namespace StatMech.BeffaraDC

open StatMech.FK
open StatMech.OSSS

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Reduction to the Bernoulli measure -/

/-- The equivalence between the edge `Finset` of `G` and its edge set, viewed as types. -/
private def edgeFinsetEquivEdgeSet : G.edgeFinset ≃ G.edgeSet where
  toFun e := ⟨e.1, by
    rw [← SimpleGraph.mem_edgeFinset]
    exact e.2⟩
  invFun e := ⟨e.1, by
    rw [SimpleGraph.mem_edgeFinset]
    exact e.2⟩
  left_inv e := by ext; rfl
  right_inv e := by ext; rfl

lemma activeWeight_one_eq_osssWeight (p : ℝ)
    (ω : ConfigSpace G.edgeSet) :
    activeWeight G (fun _ => p) 1 ω =
      OSSS.weight (OSSS.bernoulliWeight p) ω := by
  unfold activeWeight fkWeightW edgeProductW OSSS.weight OSSS.bernoulliWeight
  simp only [one_pow, mul_one]
  rw [← Finset.prod_attach G.edgeFinset
    (fun e => if extendActive G ω e then p else 1 - p)]
  rw [← Equiv.prod_comp (edgeFinsetEquivEdgeSet G)
    (fun e : G.edgeSet => if ω e then p else 1 - p)]
  apply Fintype.prod_congr
  intro e
  rw [show extendActive G ω e.1 = ω (edgeFinsetEquivEdgeSet G e) by
    exact extendActive_apply G ω (edgeFinsetEquivEdgeSet G e)]

lemma activeZ_one_eq_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    activeZ G (fun _ => p) 1 = 1 := by
  calc
    activeZ G (fun _ => p) 1 =
        OSSS.expect (OSSS.bernoulliWeight p)
          (fun _ : ConfigSpace G.edgeSet => (1 : ℝ)) := by
      unfold activeZ OSSS.expect
      apply Finset.sum_congr rfl
      intro ω _
      rw [activeWeight_one_eq_osssWeight G p ω]
      ring
    _ = 1 := OSSS.expect_one (OSSS.bernoulliWeight_isProbWeight hp0 hp1)

lemma activeProb_one_eq_osssWeight {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : ConfigSpace G.edgeSet) :
    activeProb G (fun _ => p) 1 ω =
      OSSS.weight (OSSS.bernoulliWeight p) ω := by
  rw [activeProb, activeWeight_one_eq_osssWeight G,
    activeZ_one_eq_one G hp0 hp1, div_one]

lemma activeMean_one_eq_osssExpect {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : ConfigSpace G.edgeSet → ℝ) :
    activeMean G (fun _ => p) 1 f =
      OSSS.expect (OSSS.bernoulliWeight p) f := by
  unfold activeMean OSSS.expect
  apply Finset.sum_congr rfl
  intro ω _
  rw [activeProb_one_eq_osssWeight G hp0 hp1]
  ring

lemma activeCov_one_eq_osssCov {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f g : ConfigSpace G.edgeSet → ℝ) :
    activeCov G (fun _ => p) 1 f g =
      OSSS.cov (OSSS.bernoulliWeight p) f g := by
  unfold activeCov OSSS.cov
  rw [activeMean_one_eq_osssExpect G hp0 hp1,
    activeMean_one_eq_osssExpect G hp0 hp1,
    activeMean_one_eq_osssExpect G hp0 hp1]

lemma activeProbOf_one_eq_prob {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace G.edgeSet)) :
    activeProbOf G (fun _ => p) 1 A = StatMech.prob p A := by
  rw [activeProbOf, activeMean_one_eq_osssExpect G hp0 hp1]
  exact (StatMech.TwoDim.kklw_prob_eq_expect p A).symm

lemma active_openMarginal_one_eq {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (e : G.edgeSet) :
    openMarginal (activeProb G (fun _ => p) 1) e = p := by
  apply le_antisymm
  · exact active_openMarginal_le_param G (fun _ => hp) (fun _ => hp1)
      (by norm_num) e
  · have h := active_reducedDensity_le_openMarginal G hp hp1
      (q := 1) (by norm_num) e
    simpa [reducedDensity] using h

lemma activeInfluence_one_eq_infl {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace G.edgeSet)) (hA : IsIncreasing A)
    (e : G.edgeSet) :
    activeInfluence G p 1 A e =
      OSSS.infl (OSSS.bernoulliWeight p)
        (A.indicator fun _ => (1 : ℝ)) e := by
  unfold activeInfluence
  rw [active_openMarginal_one_eq G hp hp1 e,
    activeCov_one_eq_osssCov G hp.le hp1.le]
  have hcoord : OSSS.Lindeberg.coord e = OSSS.CovLowerBound.coordI e := rfl
  rw [hcoord, OSSS.CovLowerBound.cov_comm]
  rw [OSSS.CovLowerBound.cov_coordI_mono
    (OSSS.bernoulliWeight_isProbWeight hp.le hp1.le)
    hA.indicator_monotone e]
  simp [OSSS.bernoulliWeight]
  field_simp [hp.ne', (sub_pos.mpr hp1).ne']

lemma activeInfluence_one_eq_influence {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace G.edgeSet)) (hA : IsIncreasing A)
    (e : G.edgeSet) :
    activeInfluence G p 1 A e = influence p A e :=
  (activeInfluence_one_eq_infl G hp hp1 A hA e).trans
    (StatMech.TwoDim.kklw_influence_eq_infl p A e).symm

/-! ## B. Maximal influence bounds -/

lemma maxActiveInfluence_qOne_corrected [Nonempty G.edgeSet]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace G.edgeSet)) (hA : IsIncreasing A) :
    ∃ e : G.edgeSet,
      activeProbOf G (fun _ => p) 1 A *
            (1 - activeProbOf G (fun _ => p) 1 A)
          * Real.log (Fintype.card G.edgeSet : ℝ) /
            (Fintype.card G.edgeSet : ℝ)
          / (1 + pBiasedCorrection p *
            Real.log (Fintype.card G.edgeSet : ℝ))
        ≤ activeInfluence G p 1 A e := by
  obtain ⟨e, he⟩ := maxInfluence_pbiased_corrected
    (E := G.edgeSet) hp hp1 A
  refine ⟨e, ?_⟩
  rw [activeProbOf_one_eq_prob G hp.le hp1.le,
    activeInfluence_one_eq_influence G hp hp1 A hA e]
  exact he

/-- KKL lower bound on the maximal influence at `p = 1/2` (unconditional). -/
theorem maxActiveInfluence_half [Nonempty G.edgeSet]
    (A : Set (ConfigSpace G.edgeSet)) (hA : IsIncreasing A) :
    ∃ e : G.edgeSet,
      activeProbOf G (fun _ => (1 / 2 : ℝ)) 1 A *
            (1 - activeProbOf G (fun _ => (1 / 2 : ℝ)) 1 A)
          * Real.log (Fintype.card G.edgeSet : ℝ) /
            (Fintype.card G.edgeSet : ℝ)
        ≤ activeInfluence G (1 / 2 : ℝ) 1 A e := by
  obtain ⟨e, he⟩ := maxInfluence_half (E := G.edgeSet) A
  refine ⟨e, ?_⟩
  rw [activeProbOf_one_eq_prob G (by norm_num) (by norm_num),
    activeInfluence_one_eq_influence G (by norm_num) (by norm_num) A hA e]
  exact he

/-- The same bound for `p ∈ [ε, 1 - ε]`, conditional on `Hpb`. -/
theorem maxActiveInfluence_qOne_compactWindow_of_bkkkl_u0
    {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] [Nonempty H.edgeSet]
    {ε p : ℝ} (hε0 : 0 < ε) (hp : p ∈ Set.Icc ε (1 - ε))
    (Hpb : StatMech.Probability.kpb_PBiasedHC (1 - ε / 2))
    (A : Set (ConfigSpace H.edgeSet)) (hA : IsIncreasing A) :
    ∃ e : H.edgeSet,
      activeProbOf H (fun _ => p) 1 A *
            (1 - activeProbOf H (fun _ => p) 1 A)
          * Real.log (Fintype.card H.edgeSet : ℝ) /
            (Fintype.card H.edgeSet : ℝ)
        ≤ activeInfluence H p 1 A e := by
  have hp0 : 0 < p := lt_of_lt_of_le hε0 hp.1
  have hp1 : p < 1 := by linarith [hp.2, hε0]
  obtain ⟨e, he⟩ := maxInfluence_qOne_compactWindow_of_bkkkl
    (E := H.edgeSet) hε0 hp Hpb A
  refine ⟨e, ?_⟩
  rw [activeProbOf_one_eq_prob H hp0.le hp1.le,
    activeInfluence_one_eq_influence H hp0 hp1 A hA e]
  exact he

end StatMech.BeffaraDC
