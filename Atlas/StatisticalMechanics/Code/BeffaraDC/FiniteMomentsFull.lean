/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Code.Foundations.StochasticDomination
import Code.FK.TwoPoint
import Code.FK.ComparisonHolley
import Code.FK.HolleyCoupling
import Code.BeffaraDC.ClusterMoments

open scoped BigOperators
open MeasureTheory

namespace StatMech

namespace BeffaraDC

open StatMech.FK StatMech

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]






noncomputable def fkCluster (ω : ConfigSpace (Sym2 V)) (x : V) : Finset V :=
  Finset.univ.filter (fun y => (openSub G ω).Reachable x y)





theorem fkCluster_mono {a b : ConfigSpace (Sym2 V)} (hab : a ≤ b) (x : V) :
    fkCluster G a x ⊆ fkCluster G b x := by
  intro y hy
  unfold fkCluster at hy ⊢
  rw [Finset.mem_filter] at hy ⊢
  exact ⟨hy.1, hy.2.mono (openSub_mono G hab)⟩




def fkClusterSizeLargeEvent (x : V) (N : ℕ) : Set (ConfigSpace (Sym2 V)) :=
  {ω | N ≤ (fkCluster G ω x).card}





theorem fkClusterSizeLargeEvent_isIncreasing (x : V) (N : ℕ) :
    IsIncreasing (fkClusterSizeLargeEvent G x N) := by
  intro a b hab ha
  simp only [fkClusterSizeLargeEvent, Set.mem_setOf_eq] at ha ⊢
  exact ha.trans (Finset.card_le_card (fkCluster_mono G hab x))



theorem measurableSet_fkClusterSizeLargeEvent (x : V) (N : ℕ) :
    MeasurableSet (fkClusterSizeLargeEvent G x N) :=
  DiscreteMeasurableSpace.forall_measurableSet (fkClusterSizeLargeEvent G x N)












noncomputable def fkClusterSizeTail (p q : ℝ) (x : V) (N : ℕ) : ℝ :=
  (measOfMass (fkProb G p q)).real (fkClusterSizeLargeEvent G x N)


theorem fkClusterSizeTail_nonneg (p q : ℝ) (x : V) (N : ℕ) :
    0 ≤ fkClusterSizeTail G p q x N :=
  measureReal_nonneg






theorem fkClusterSizeLargeEvent_eq_empty_of_card_lt (x : V) {N : ℕ}
    (hN : Fintype.card V < N) : fkClusterSizeLargeEvent G x N = ∅ := by
  ext ω
  simp only [fkClusterSizeLargeEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
    not_le]
  exact lt_of_le_of_lt (le_trans (Finset.card_le_card (Finset.subset_univ _))
    (le_of_eq (Finset.card_univ))) hN



theorem fkClusterSizeTail_eq_zero_of_card_lt (p q : ℝ) (x : V) {N : ℕ}
    (hN : Fintype.card V < N) : fkClusterSizeTail G p q x N = 0 := by
  unfold fkClusterSizeTail
  rw [fkClusterSizeLargeEvent_eq_empty_of_card_lt G x hN, measureReal_empty]



theorem fkClusterSizeTail_le_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (x : V) (N : ℕ) : fkClusterSizeTail G p q x N ≤ 1 := by
  haveI : IsProbabilityMeasure (measOfMass (fkProb G p q)) :=
    measOfMass_isProbabilityMeasure (fkProb G p q)
      (fun ω => fkProb_nonneg G hp hp1 hq ω) (fkProb_sum_eq_one G hp hp1 hq)
  exact measureReal_le_one (μ := measOfMass (fkProb G p q))
    (s := fkClusterSizeLargeEvent G x N)















theorem fkClusterSizeTail_le_bernoulli {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x : V) (N : ℕ) :
    fkClusterSizeTail G p q x N ≤ fkClusterSizeTail G p 1 x N :=
  fk_le_bernoulli G hp hp1 hq (fkClusterSizeLargeEvent G x N)
    (measurableSet_fkClusterSizeLargeEvent G x N)
    (fkClusterSizeLargeEvent_isIncreasing G x N)





















theorem fkClusterSizeTail_geometricTail {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x : V) {C r : ℝ} (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) :
    ∀ N, fkClusterSizeTail G p q x N ≤ C * r ^ N :=
  fun N => (fkClusterSizeTail_le_bernoulli G hp hp1 hq x N).trans (hbtail N)












theorem exists_geometricTail {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x : V) :
    ∃ C r, 0 ≤ r ∧ r < 1 ∧ ∀ N, fkClusterSizeTail G p q x N ≤ C * r ^ N := by
  refine ⟨(2 : ℝ) ^ (Fintype.card V + 1), 1 / 2, by norm_num, by norm_num, fun N => ?_⟩
  by_cases hN : Fintype.card V < N
  · rw [fkClusterSizeTail_eq_zero_of_card_lt G p q x hN]
    positivity
  · rw [not_lt] at hN
    refine (fkClusterSizeTail_le_one G hp hp1 hq x N).trans ?_
    
    have h2 : (2 : ℝ) ^ (Fintype.card V + 1) * (1 / 2) ^ N
        = (2 : ℝ) ^ (Fintype.card V + 1) / (2 : ℝ) ^ N := by
      rw [div_pow, one_pow]; ring
    rw [h2, le_div_iff₀ (by positivity)]
    have hle : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ (Fintype.card V + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [hle, pow_pos (show (0:ℝ) < 2 by norm_num) (Fintype.card V + 1)]









noncomputable def fkClusterSizeDomination {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x : V) {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) :
    ClusterSizeDomination :=
  clusterSizeDomination_of_geometricTail
    (dist := fun N => fkClusterSizeTail G p q x N) (C := C) (r := r)
    (fun N => fkClusterSizeTail_nonneg G p q x N) hr0 hr1
    (fkClusterSizeTail_geometricTail G hp hp1 hq x hbtail)

@[simp] theorem fkClusterSizeDomination_dist {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) (x : V) {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) :
    (fkClusterSizeDomination G hp hp1 hq x hr0 hr1 hbtail).dist
      = fun N => fkClusterSizeTail G p q x N := rfl












theorem fkClusterSizeMoment_lt_top {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x : V) {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) (d : ℕ) :
    clusterMoment (fun N => fkClusterSizeTail G p q x N) d
      ≤ ∑' N : ℕ, (N : ℝ) ^ d * (C * r ^ N) := by
  have h := (fkClusterSizeDomination G hp hp1 hq x hr0 hr1 hbtail).allMoments_lt_top d
  simpa using h


theorem fkClusterSizeMoment_nonneg (p q : ℝ) (x : V) (d : ℕ) :
    0 ≤ clusterMoment (fun N => fkClusterSizeTail G p q x N) d :=
  clusterMoment_nonneg (fun N => fkClusterSizeTail_nonneg G p q x N) d


















theorem bernoulliClusterSizeMoment_lt_top {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x : V) {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) (d : ℕ) :
    clusterMoment (fun N => fkClusterSizeTail G p 1 x N) d
      ≤ ∑' N : ℕ, (N : ℝ) ^ d * (C * r ^ N) :=
  fkClusterSizeMoment_lt_top G hp hp1 le_rfl x hr0 hr1 hbtail d

end BeffaraDC

end StatMech
