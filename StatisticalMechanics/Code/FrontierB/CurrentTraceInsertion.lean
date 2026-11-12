/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierB.BoxCurrentLaws
import Code.FrontierB.CurrentSelectionIndependence
import Code.FrontierB.CurrentMixingErgodicity
import Code.FK.InfiniteFiniteEnergy

open MeasureTheory
open scoped ENNReal BigOperators symmDiff

namespace StatMech.FrontierB

open Sharpness Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


def zeroCurrentEdge (e : G.edgeFinset) (m : EdgeCurrent G) : EdgeCurrent G :=
  Function.update m e 0



def forceCurrentEdgePositive (e : G.edgeFinset) (m : EdgeCurrent G) : EdgeCurrent G :=
  if m e = 0 then Function.update m e 2 else m


def twoFluxAt (e : G.edgeFinset) : EdgeCurrent G :=
  fun f => if f = e then 2 else 0

@[simp] theorem zeroCurrentEdge_apply_same (e : G.edgeFinset) (m : EdgeCurrent G) :
    zeroCurrentEdge G e m e = 0 := by
  simp [zeroCurrentEdge]

@[simp] theorem zeroCurrentEdge_apply_of_ne (e f : G.edgeFinset)
    (hfe : f ≠ e) (m : EdgeCurrent G) :
    zeroCurrentEdge G e m f = m f := by
  simp [zeroCurrentEdge, hfe]

@[simp] theorem forceCurrentEdgePositive_apply_same
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    forceCurrentEdgePositive G e m e = if m e = 0 then 2 else m e := by
  by_cases h : m e = 0 <;> simp [forceCurrentEdgePositive, h]

@[simp] theorem forceCurrentEdgePositive_apply_of_ne
    (e f : G.edgeFinset) (hfe : f ≠ e) (m : EdgeCurrent G) :
    forceCurrentEdgePositive G e m f = m f := by
  by_cases h : m e = 0 <;> simp [forceCurrentEdgePositive, h, hfe]

theorem forceCurrentEdgePositive_eq_self_iff
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    forceCurrentEdgePositive G e m = m ↔ m e ≠ 0 := by
  constructor
  · intro h hm0
    have he := congrFun h e
    simp [forceCurrentEdgePositive, hm0] at he
  · intro h
    simp [forceCurrentEdgePositive, h]

theorem forceCurrentEdgePositive_ne_zero
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    forceCurrentEdgePositive G e m e ≠ 0 := by
  by_cases h : m e = 0 <;> simp [forceCurrentEdgePositive, h]

theorem forceCurrentEdgePositive_zeroCurrentEdge
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    forceCurrentEdgePositive G e (zeroCurrentEdge G e m) =
      Function.update m e 2 := by
  funext f
  by_cases hfe : f = e
  · subst f
    simp [forceCurrentEdgePositive]
  · simp [forceCurrentEdgePositive, zeroCurrentEdge, hfe]

theorem forceCurrentEdgePositive_preimage_iff_of_eq_two
    (e : G.edgeFinset) (m a : EdgeCurrent G) (hm : m e = 2) :
    forceCurrentEdgePositive G e a = m <->
      a = m \/ a = zeroCurrentEdge G e m := by
  constructor
  · intro h
    by_cases ha : a e = 0
    · right
      funext f
      by_cases hfe : f = e
      · subst f
        simp [zeroCurrentEdge, ha]
      · have hf := congrFun h f
        simpa [forceCurrentEdgePositive, ha, zeroCurrentEdge, hfe] using hf
    · left
      simpa [forceCurrentEdgePositive, ha] using h
  · rintro (rfl | rfl)
    · simp [forceCurrentEdgePositive, hm]
    · rw [forceCurrentEdgePositive_zeroCurrentEdge]
      funext f
      by_cases hfe : f = e
      · subst f
        simp [hm]
      · simp [hfe]

theorem forceCurrentEdgePositive_preimage_iff_of_ne_two
    (e : G.edgeFinset) (m a : EdgeCurrent G) (hm0 : m e ≠ 0)
    (hm2 : m e ≠ 2) :
    forceCurrentEdgePositive G e a = m ↔ a = m := by
  constructor
  · intro h
    by_cases ha : a e = 0
    · have he := congrFun h e
      simp [forceCurrentEdgePositive, ha] at he
      exact (hm2 he.symm).elim
    · simpa [forceCurrentEdgePositive, ha] using h
  · rintro rfl
    simp [forceCurrentEdgePositive, hm0]

theorem forceCurrentEdgePositive_no_preimage_of_eq_zero
    (e : G.edgeFinset) (m a : EdgeCurrent G) (hm : m e = 0) :
    forceCurrentEdgePositive G e a ≠ m := by
  intro h
  exact forceCurrentEdgePositive_ne_zero G e a
    (by simpa [hm] using congrFun h e)

theorem sources_twoFluxAt (e : G.edgeFinset) :
    sources G (ofEdgeFun G (twoFluxAt G e)) = ∅ := by
  ext v
  simp only [mem_sources]
  apply iff_of_false
  · rw [Nat.not_odd_iff_even]
    unfold incidentFlux
    by_cases hv : v ∈ e.1
    · have hefilter : e.1 ∈ G.edgeFinset.filter (fun f => v ∈ f) := by
        exact Finset.mem_filter.mpr ⟨e.2, hv⟩
      rw [← Finset.sum_erase_add _ _ hefilter]
      have hrest : ∑ f ∈ (G.edgeFinset.filter (fun f => v ∈ f)).erase e.1,
          ofEdgeFun G (twoFluxAt G e) f = 0 := by
        apply Finset.sum_eq_zero
        intro f hf
        have hfne : f ≠ e.1 := Finset.ne_of_mem_erase hf
        have hfG : f ∈ G.edgeFinset :=
          (Finset.mem_filter.mp (Finset.mem_of_mem_erase hf)).1
        simp [ofEdgeFun, twoFluxAt, hfG, Subtype.ext_iff, hfne]
      rw [hrest]
      simp [ofEdgeFun, twoFluxAt, e.2]
    · have hzero : ∑ f ∈ G.edgeFinset.filter (fun f => v ∈ f),
          ofEdgeFun G (twoFluxAt G e) f = 0 := by
        apply Finset.sum_eq_zero
        intro f hf
        have hffilter := Finset.mem_filter.mp hf
        have hfne : f ≠ e.1 := by
          intro h
          apply hv
          simpa [h] using hffilter.2
        simp [ofEdgeFun, twoFluxAt, hffilter.1, Subtype.ext_iff, hfne]
      rw [hzero]
      exact Even.zero
  · simp

theorem forceCurrentEdgePositive_eq_add_twoFluxAt_of_zero
    (e : G.edgeFinset) (m : EdgeCurrent G) (hm : m e = 0) :
    forceCurrentEdgePositive G e m = fun f => m f + twoFluxAt G e f := by
  funext f
  by_cases hfe : f = e
  · subst f
    simp [forceCurrentEdgePositive, twoFluxAt, hm]
  · simp [forceCurrentEdgePositive, twoFluxAt, hm, hfe]


theorem sources_forceCurrentEdgePositive
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    sources G (ofEdgeFun G (forceCurrentEdgePositive G e m)) =
      sources G (ofEdgeFun G m) := by
  by_cases hm : m e = 0
  · rw [forceCurrentEdgePositive_eq_add_twoFluxAt_of_zero G e m hm,
      ← ofEdgeFun_add, sources_add, sources_twoFluxAt]
    simp
  · simp [forceCurrentEdgePositive, hm]


theorem weight_forceCurrentEdgePositive_of_zero
    (beta : ℝ) (e : G.edgeFinset) (m : EdgeCurrent G) (hm : m e = 0) :
    weight G beta (fun _ => 1)
        (ofEdgeFun G (forceCurrentEdgePositive G e m)) =
      weight G beta (fun _ => 1) (ofEdgeFun G m) * (beta ^ 2 / 2) := by
  rw [weight_ofEdgeFun, weight_ofEdgeFun]
  have hforce : forceCurrentEdgePositive G e m = Function.update m e 2 := by
    simp [forceCurrentEdgePositive, hm]
  rw [hforce]
  simp only [mul_one]
  let term : G.edgeFinset → ℕ → ℝ := fun f k => beta ^ k / Nat.factorial k
  change (∏ f ∈ Finset.univ, term f (Function.update m e 2 f)) =
    (∏ f ∈ Finset.univ, term f (m f)) * (beta ^ 2 / 2)
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ e)]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ e)]
  have hcomp :
      (∏ f ∈ (Finset.univ : Finset G.edgeFinset) \ {e},
          term f (Function.update m e 2 f)) =
        ∏ f ∈ (Finset.univ : Finset G.edgeFinset) \ {e}, term f (m f) := by
    apply Finset.prod_congr rfl
    intro f hf
    have hfe : f ≠ e := by
      have hnot := (Finset.mem_sdiff.mp hf).2
      simpa using hnot
    simp [hfe]
  rw [hcomp]
  simp only [term, hm, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  simp
  ring



theorem currentPMF_forceCurrentEdgePositive_apply_of_zero
    (beta : ℝ) (hbeta : 0 < beta) (A : Finset V)
    (hA : 0 < currentSum G beta (fun _ => 1) A)
    (e : G.edgeFinset) (m : EdgeCurrent G) (hm : m e = 0) :
    currentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) A hA
        (forceCurrentEdgePositive G e m) =
      ENNReal.ofReal (beta ^ 2 / 2) *
        currentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) A hA m := by
  rw [currentPMF_apply, currentPMF_apply]
  unfold currentRawMass
  rw [sources_forceCurrentEdgePositive]
  by_cases hsrc : sources G (ofEdgeFun G m) = A
  · simp only [hsrc, if_true]
    rw [weight_forceCurrentEdgePositive_of_zero G beta e m hm,
      ENNReal.ofReal_mul]
    · ring
    · exact Ising.acw_weight_nonneg G beta (fun _ => 1)
        hbeta.le (fun _ => zero_le_one) _
  · simp [hsrc]


theorem boundaryCurrentPMF_forceCurrentEdgePositive_apply_of_zero
    (beta : ℝ) (hbeta : 0 < beta) (interior : Finset V)
    (e : G.edgeFinset) (m : EdgeCurrent G) (hm : m e = 0) :
    boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) interior (forceCurrentEdgePositive G e m) =
      ENNReal.ofReal (beta ^ 2 / 2) *
        boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
          (fun _ => zero_le_one) interior m := by
  rw [boundaryCurrentPMF_apply, boundaryCurrentPMF_apply]
  unfold boundaryCurrentRawMass
  rw [sources_forceCurrentEdgePositive]
  by_cases hsrc : sources G (ofEdgeFun G m) ∩ interior = ∅
  · simp only [hsrc, if_true]
    rw [weight_forceCurrentEdgePositive_of_zero G beta e m hm,
      ENNReal.ofReal_mul]
    · ring
    · exact Ising.acw_weight_nonneg G beta (fun _ => 1)
        hbeta.le (fun _ => zero_le_one) _
  · simp [hsrc]

set_option maxHeartbeats 3000000 in

theorem PMF.map_forceCurrentEdgePositive_apply_of_eq_two
    (p : PMF (EdgeCurrent G)) (e : G.edgeFinset) (m : EdgeCurrent G)
    (hm : m e = 2) :
    PMF.map (forceCurrentEdgePositive G e) p m =
      p m + p (zeroCurrentEdge G e m) := by
  letI : DecidableEq (EdgeCurrent G) := Classical.decEq _
  rw [PMF.map_apply, ENNReal.tsum_eq_add_tsum_ite m]
  have hmpos : m e ≠ 0 := by omega
  have hself : forceCurrentEdgePositive G e m = m :=
    (forceCurrentEdgePositive_eq_self_iff G e m).2 hmpos
  rw [if_pos hself.symm]
  congr 1
  let z := zeroCurrentEdge G e m
  have hzeroNe : z ≠ m := by
      intro h
      have he := congrFun h e
      simp [z, zeroCurrentEdge, hm] at he
  have hforce : forceCurrentEdgePositive G e z = m := by
      rw [forceCurrentEdgePositive_zeroCurrentEdge]
      funext f
      by_cases hfe : f = e
      · subst f
        simp [hm]
      · simp [hfe]
  rw [← show (if z = m then 0 else
      if m = forceCurrentEdgePositive G e z then p z else 0) = p z by
    simp [hzeroNe, hforce]]
  apply tsum_eq_single z
  intro a hane
  by_cases ham : a = m
  · subst a
    simp
  · have hnot : forceCurrentEdgePositive G e a ≠ m := by
      intro hforce'
      rcases (forceCurrentEdgePositive_preimage_iff_of_eq_two G e m a hm).1 hforce' with
        h | h
      · exact ham h
      · exact hane h
    simp [ham, hnot.symm]

set_option maxHeartbeats 800000 in

theorem PMF.map_forceCurrentEdgePositive_apply_of_ne_two
    (p : PMF (EdgeCurrent G)) (e : G.edgeFinset) (m : EdgeCurrent G)
    (hm0 : m e ≠ 0) (hm2 : m e ≠ 2) :
    PMF.map (forceCurrentEdgePositive G e) p m = p m := by
  letI : DecidableEq (EdgeCurrent G) := Classical.decEq _
  rw [PMF.map_apply]
  have hself : forceCurrentEdgePositive G e m = m :=
    (forceCurrentEdgePositive_eq_self_iff G e m).2 hm0
  have hfm : (if m = forceCurrentEdgePositive G e m then p m else 0) = p m := by
    simp [hself]
  rw [← hfm]
  apply tsum_eq_single m
  intro a hane
  have hnot : forceCurrentEdgePositive G e a ≠ m := by
    intro hforce
    exact hane ((forceCurrentEdgePositive_preimage_iff_of_ne_two
      G e m a hm0 hm2).1 hforce)
  simp [hnot.symm]

set_option maxHeartbeats 800000 in

theorem PMF.map_forceCurrentEdgePositive_apply_of_eq_zero
    (p : PMF (EdgeCurrent G)) (e : G.edgeFinset) (m : EdgeCurrent G)
    (hm : m e = 0) :
    PMF.map (forceCurrentEdgePositive G e) p m = 0 := by
  letI : DecidableEq (EdgeCurrent G) := Classical.decEq _
  rw [PMF.map_apply]
  rw [ENNReal.tsum_eq_zero]
  intro a
  rw [if_neg]
  exact (forceCurrentEdgePositive_no_preimage_of_eq_zero G e m a hm).symm


noncomputable def currentTraceInsertionConstant (beta : ℝ) : ℝ :=
  beta ^ 2 / (beta ^ 2 + 2)

theorem currentTraceInsertionConstant_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < currentTraceInsertionConstant beta := by
  unfold currentTraceInsertionConstant
  positivity

theorem currentTraceInsertionConstant_le_one (beta : ℝ) :
    currentTraceInsertionConstant beta ≤ 1 := by
  unfold currentTraceInsertionConstant
  have hden : 0 < beta ^ 2 + 2 := by positivity
  apply (div_le_one hden).2
  linarith

set_option maxHeartbeats 800000 in

theorem currentPMF_map_forceCurrentEdgePositive_apply_bound
    (beta : ℝ) (hbeta : 0 < beta) (A : Finset V)
    (hA : 0 < currentSum G beta (fun _ => 1) A)
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        PMF.map (forceCurrentEdgePositive G e)
          (currentPMF G beta (fun _ => 1) hbeta.le
            (fun _ => zero_le_one) A hA) m ≤
      currentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) A hA m := by
  let p := currentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => zero_le_one) A hA
  by_cases hm0 : m e = 0
  · rw [PMF.map_forceCurrentEdgePositive_apply_of_eq_zero G p e m hm0]
    simp
  by_cases hm2 : m e = 2
  · rw [PMF.map_forceCurrentEdgePositive_apply_of_eq_two G p e m hm2]
    let z := zeroCurrentEdge G e m
    have hz0 : z e = 0 := zeroCurrentEdge_apply_same G e m
    have hforce : forceCurrentEdgePositive G e z = m := by
      rw [forceCurrentEdgePositive_zeroCurrentEdge]
      funext f
      by_cases hfe : f = e
      · subst f
        simp [hm2]
      · simp [hfe]
    have hratio := currentPMF_forceCurrentEdgePositive_apply_of_zero
      G beta hbeta A hA e z hz0
    rw [hforce] at hratio
    change ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (p m + p z) ≤ p m
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top p m, PMF.apply_ne_top p z⟩))
      (PMF.apply_ne_top p m)).mp
    have hratioReal := congrArg ENNReal.toReal hratio
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ beta ^ 2 / 2)]
      at hratioReal
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (currentTraceInsertionConstant_pos hbeta).le,
      ENNReal.toReal_add (PMF.apply_ne_top p m) (PMF.apply_ne_top p z)]
    unfold currentTraceInsertionConstant
    have hden : 0 < beta ^ 2 + 2 := by positivity
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    field_simp
    nlinarith
  · rw [PMF.map_forceCurrentEdgePositive_apply_of_ne_two G p e m hm0 hm2]
    exact mul_le_of_le_one_left (by positivity)
      (ENNReal.ofReal_le_one.mpr (currentTraceInsertionConstant_le_one beta))

set_option maxHeartbeats 800000 in

theorem boundaryCurrentPMF_map_forceCurrentEdgePositive_apply_bound
    (beta : ℝ) (hbeta : 0 < beta) (interior : Finset V)
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        PMF.map (forceCurrentEdgePositive G e)
          (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
            (fun _ => zero_le_one) interior) m ≤
      boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) interior m := by
  let p := boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => zero_le_one) interior
  by_cases hm0 : m e = 0
  · rw [PMF.map_forceCurrentEdgePositive_apply_of_eq_zero G p e m hm0]
    simp
  by_cases hm2 : m e = 2
  · rw [PMF.map_forceCurrentEdgePositive_apply_of_eq_two G p e m hm2]
    let z := zeroCurrentEdge G e m
    have hz0 : z e = 0 := zeroCurrentEdge_apply_same G e m
    have hforce : forceCurrentEdgePositive G e z = m := by
      rw [forceCurrentEdgePositive_zeroCurrentEdge]
      funext f
      by_cases hfe : f = e
      · subst f
        simp [hm2]
      · simp [hfe]
    have hratio := boundaryCurrentPMF_forceCurrentEdgePositive_apply_of_zero
      G beta hbeta interior e z hz0
    rw [hforce] at hratio
    change ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (p m + p z) ≤ p m
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top p m, PMF.apply_ne_top p z⟩))
      (PMF.apply_ne_top p m)).mp
    have hratioReal := congrArg ENNReal.toReal hratio
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ beta ^ 2 / 2)]
      at hratioReal
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (currentTraceInsertionConstant_pos hbeta).le,
      ENNReal.toReal_add (PMF.apply_ne_top p m) (PMF.apply_ne_top p z)]
    unfold currentTraceInsertionConstant
    have hden : 0 < beta ^ 2 + 2 := by positivity
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    field_simp
    nlinarith
  · rw [PMF.map_forceCurrentEdgePositive_apply_of_ne_two G p e m hm0 hm2]
    exact mul_le_of_le_one_left (by positivity)
      (ENNReal.ofReal_le_one.mpr (currentTraceInsertionConstant_le_one beta))



theorem PMF.toMeasure_map_le_of_apply_le
    {alpha : Type*} [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p : PMF alpha) (f : alpha → alpha) (c : ℝ≥0∞)
    (hpoint : ∀ a, c * PMF.map f p a ≤ p a)
    (S : Set alpha) :
    c * (PMF.map f p).toMeasure S ≤ p.toMeasure S := by
  rw [PMF.toMeasure_apply_eq_tsum, PMF.toMeasure_apply_eq_tsum,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ S
  · simpa [Set.indicator_of_mem ha] using hpoint a
  · simp [ha]

theorem currentPMF_forceCurrentEdgePositive_event_bound
    (beta : ℝ) (hbeta : 0 < beta) (A : Finset V)
    (hA : 0 < currentSum G beta (fun _ => 1) A)
    (e : G.edgeFinset) (S : Set (EdgeCurrent G)) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (PMF.map (forceCurrentEdgePositive G e)
          (currentPMF G beta (fun _ => 1) hbeta.le
            (fun _ => zero_le_one) A hA)).toMeasure S ≤
      (currentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) A hA).toMeasure S := by
  exact PMF.toMeasure_map_le_of_apply_le
    (currentPMF G beta (fun _ => 1) hbeta.le
      (fun _ => zero_le_one) A hA)
    (forceCurrentEdgePositive G e)
    (ENNReal.ofReal (currentTraceInsertionConstant beta))
    (currentPMF_map_forceCurrentEdgePositive_apply_bound
      G beta hbeta A hA e) S

theorem boundaryCurrentPMF_forceCurrentEdgePositive_event_bound
    (beta : ℝ) (hbeta : 0 < beta) (interior : Finset V)
    (e : G.edgeFinset) (S : Set (EdgeCurrent G)) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (PMF.map (forceCurrentEdgePositive G e)
          (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
            (fun _ => zero_le_one) interior)).toMeasure S ≤
      (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) interior).toMeasure S := by
  exact PMF.toMeasure_map_le_of_apply_le
    (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
      (fun _ => zero_le_one) interior)
    (forceCurrentEdgePositive G e)
    (ENNReal.ofReal (currentTraceInsertionConstant beta))
    (boundaryCurrentPMF_map_forceCurrentEdgePositive_apply_bound
      G beta hbeta interior e) S




def forceInfiniteCurrentEdgePositive {E : Type*} [DecidableEq E] (e : E)
    (m : InfiniteCurrentConfig E) : InfiniteCurrentConfig E :=
  if m e = 0 then Function.update m e 2 else m

@[simp] theorem forceInfiniteCurrentEdgePositive_apply_same
    {E : Type*} [DecidableEq E] (e : E) (m : InfiniteCurrentConfig E) :
    forceInfiniteCurrentEdgePositive e m e = if m e = 0 then 2 else m e := by
  by_cases h : m e = 0 <;> simp [forceInfiniteCurrentEdgePositive, h]

@[simp] theorem forceInfiniteCurrentEdgePositive_apply_of_ne
    {E : Type*} [DecidableEq E] (e f : E) (hfe : f ≠ e)
    (m : InfiniteCurrentConfig E) :
    forceInfiniteCurrentEdgePositive e m f = m f := by
  by_cases h : m e = 0 <;> simp [forceInfiniteCurrentEdgePositive, h, hfe]

theorem continuous_forceInfiniteCurrentEdgePositive
    {E : Type*} [DecidableEq E] (e : E) :
    Continuous (forceInfiniteCurrentEdgePositive e :
      InfiniteCurrentConfig E → InfiniteCurrentConfig E) := by
  refine continuous_pi fun f => ?_
  by_cases hfe : f = e
  · subst f
    simpa only [forceInfiniteCurrentEdgePositive_apply_same] using
      (continuous_of_discreteTopology
      (f := fun k : ℕ => if k = 0 then 2 else k)).comp
        (continuous_apply e : Continuous (fun m : InfiniteCurrentConfig E => m e))
  · simpa only [forceInfiniteCurrentEdgePositive_apply_of_ne e f hfe] using
      (continuous_apply f : Continuous (fun m : InfiniteCurrentConfig E => m f))

theorem currentTrace_forceInfiniteCurrentEdgePositive
    {E : Type*} [DecidableEq E] (e : E) (m : InfiniteCurrentConfig E) :
    currentTrace (forceInfiniteCurrentEdgePositive e m) =
      setOpen e (currentTrace m) := by
  funext f
  by_cases hfe : f = e
  · subst f
    by_cases hm : m e = 0
    · simp [currentTrace, forceInfiniteCurrentEdgePositive, setOpen, hm]
    · have hmpos : 0 < m e := Nat.pos_of_ne_zero hm
      simp [currentTrace, forceInfiniteCurrentEdgePositive, setOpen, hm, hmpos]
  · simp [currentTrace, forceInfiniteCurrentEdgePositive_apply_of_ne e f hfe,
      setOpen_of_ne hfe]

theorem superposedCurrentTrace_forceInfiniteCurrentEdgePositive_fst
    {E : Type*} [DecidableEq E] (e : E)
    (m n : InfiniteCurrentConfig E) :
    superposedCurrentTrace (forceInfiniteCurrentEdgePositive e m, n) =
      setOpen e (superposedCurrentTrace (m, n)) := by
  funext f
  by_cases hfe : f = e
  · subst f
    by_cases hm : m e = 0
    · simp [superposedCurrentTrace, forceInfiniteCurrentEdgePositive, hm,
        setOpen]
    · have hmpos : 0 < m e := Nat.pos_of_ne_zero hm
      simp [superposedCurrentTrace, forceInfiniteCurrentEdgePositive, hm,
        setOpen, hmpos]
  · simp [superposedCurrentTrace,
      forceInfiniteCurrentEdgePositive_apply_of_ne e f hfe,
      setOpen_of_ne hfe]

theorem forceInfiniteCurrentEdgePositive_extendBoxCurrent
    (d n : ℕ) (e : (StatMech.FK.boxGraph d n).edgeFinset)
    (m : EdgeCurrent (StatMech.FK.boxGraph d n)) :
    forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e)
        (extendBoxCurrent d n m) =
      extendBoxCurrent d n (forceCurrentEdgePositive (StatMech.FK.boxGraph d n) e m) := by
  funext f
  by_cases hfe : f = boxCurrentEdgeIncl d n e
  · subst f
    by_cases hm : m e = 0 <;>
      simp [forceInfiniteCurrentEdgePositive, forceCurrentEdgePositive, hm]
  · by_cases hfrange : f ∈ Set.range (boxCurrentEdgeIncl d n)
    · obtain ⟨g, rfl⟩ := hfrange
      have hge : g ≠ e := fun h => hfe (h ▸ rfl)
      simp [forceInfiniteCurrentEdgePositive_apply_of_ne _ _ hfe,
        forceCurrentEdgePositive_apply_of_ne _ _ _ hge]
    · rw [forceInfiniteCurrentEdgePositive_apply_of_ne _ _ hfe,
        extendBoxCurrent_outside d n m f hfrange,
        extendBoxCurrent_outside d n _ f hfrange]



theorem freeBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : (StatMech.FK.boxGraph d n).edgeFinset)
    (S : Set (InfiniteCurrentConfig (Sym2 (Site d)))) (hS : MeasurableSet S) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (freeBoxCurrentMeasure d n beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) ≤
      (freeBoxCurrentMeasure d n beta hbeta.le : Measure _) S := by
  let G := StatMech.FK.boxGraph d n
  let p := sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => zero_le_one)
  let B := extendBoxCurrent d n ⁻¹' S
  have hbound := currentPMF_forceCurrentEdgePositive_event_bound G beta hbeta ∅
    (Ising.acr_currentSum_empty_pos G beta (fun _ => 1)) e B
  have hbound' : ENNReal.ofReal (currentTraceInsertionConstant beta) *
      (PMF.map (forceCurrentEdgePositive G e) p).toMeasure B ≤
        p.toMeasure B := by
    simpa only [p, sourcelessCurrentPMF] using hbound
  have hmap : (PMF.map (forceCurrentEdgePositive G e) p).toMeasure B =
      p.toMeasure (forceCurrentEdgePositive G e ⁻¹' B) :=
    PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete MeasurableSet.of_discrete
  rw [hmap] at hbound'
  have hpre : forceCurrentEdgePositive G e ⁻¹' B =
      extendBoxCurrent d n ⁻¹'
        (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) := by
    ext m
    simp only [Set.mem_preimage, B]
    rw [forceInfiniteCurrentEdgePositive_extendBoxCurrent]
  change ENNReal.ofReal (currentTraceInsertionConstant beta) *
      Measure.map (extendBoxCurrent d n) p.toMeasure
        (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) ≤
    Measure.map (extendBoxCurrent d n) p.toMeasure S
  rw [Measure.map_apply (measurable_extendBoxCurrent d n)
      (hS.preimage (continuous_forceInfiniteCurrentEdgePositive _).measurable),
    Measure.map_apply (measurable_extendBoxCurrent d n) hS,
    ← hpre]
  exact hbound'


theorem plusBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : (StatMech.FK.boxGraph d n).edgeFinset)
    (S : Set (InfiniteCurrentConfig (Sym2 (Site d)))) (hS : MeasurableSet S) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (plusBoxCurrentMeasure d n beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) ≤
      (plusBoxCurrentMeasure d n beta hbeta.le : Measure _) S := by
  let G := StatMech.FK.boxGraph d n
  let p := boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => zero_le_one) (boxCurrentInterior d n)
  let B := extendBoxCurrent d n ⁻¹' S
  have hbound := boundaryCurrentPMF_forceCurrentEdgePositive_event_bound
    G beta hbeta (boxCurrentInterior d n) e B
  have hbound' : ENNReal.ofReal (currentTraceInsertionConstant beta) *
      (PMF.map (forceCurrentEdgePositive G e) p).toMeasure B ≤
        p.toMeasure B := by
    simpa only [p] using hbound
  have hmap : (PMF.map (forceCurrentEdgePositive G e) p).toMeasure B =
      p.toMeasure (forceCurrentEdgePositive G e ⁻¹' B) :=
    PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete MeasurableSet.of_discrete
  rw [hmap] at hbound'
  have hpre : forceCurrentEdgePositive G e ⁻¹' B =
      extendBoxCurrent d n ⁻¹'
        (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) := by
    ext m
    simp only [Set.mem_preimage, B]
    rw [forceInfiniteCurrentEdgePositive_extendBoxCurrent]
  change ENNReal.ofReal (currentTraceInsertionConstant beta) *
      Measure.map (extendBoxCurrent d n) p.toMeasure
        (forceInfiniteCurrentEdgePositive (boxCurrentEdgeIncl d n e) ⁻¹' S) ≤
    Measure.map (extendBoxCurrent d n) p.toMeasure S
  rw [Measure.map_apply (measurable_extendBoxCurrent d n)
      (hS.preimage (continuous_forceInfiniteCurrentEdgePositive _).measurable),
    Measure.map_apply (measurable_extendBoxCurrent d n) hS,
    ← hpre]
  exact hbound'



theorem eventually_boxCurrentEdgeIncl_eq
    (d : ℕ) (e : Sym2 (Site d))
    (he : e ∈ (hypercubicLattice d).edgeSet) :
    ∀ᶠ n in Filter.atTop, ∃ eb : (StatMech.FK.boxGraph d n).edgeFinset,
      boxCurrentEdgeIncl d n eb = e := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hadj : (hypercubicLattice d).Adj a b := by
        rw [← SimpleGraph.mem_edgeSet]
        exact he
      obtain ⟨N, hN⟩ := finite_subset_box ({a, b} : Set (Site d)) (Set.toFinite _)
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have ha : a ∈ box d n := box_mono d hn (hN (by simp))
      have hb : b ∈ box d n := box_mono d hn (hN (by simp))
      have himage : s(a, b) ∈ Finset.image (StatMech.FK.edgeIncl d n)
          (StatMech.FK.boxGraph d n).edgeFinset :=
        (StatMech.IsingFK.hbx_mem_image_edgeIncl_iff d n a b).2 ⟨ha, hb, hadj⟩
      rw [Finset.mem_image] at himage
      obtain ⟨f, hf, hfe⟩ := himage
      exact ⟨⟨f, hf⟩, hfe⟩

theorem infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet)
    (C : Set (InfiniteCurrentConfig (Sym2 (Site d)))) (hC : IsClopen C) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive e ⁻¹' C) ≤
      (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _) C := by
  have hconv := freeBoxCurrentMeasure_tendsto_full d beta hbeta
  have hpreClopen := hC.preimage (continuous_forceInfiniteCurrentEdgePositive e)
  have hpre := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hconv hpreClopen
  have hbase := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hconv hC
  have hpreE := (ENNReal.tendsto_coe).2 hpre
  have hbaseE := (ENNReal.tendsto_coe).2 hbase
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hpreE hbaseE
  have hcpre : Filter.Tendsto
      (fun n => ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (freeBoxCurrentMeasure d n beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive e ⁻¹' C))
      Filter.atTop (nhds (ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive e ⁻¹' C))) :=
    ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (currentTraceInsertionConstant beta)) hpreE
      (Or.inr ENNReal.ofReal_ne_top)
  apply le_of_tendsto_of_tendsto hcpre hbaseE
  filter_upwards [eventually_boxCurrentEdgeIncl_eq d e he] with n hn
  obtain ⟨eb, heb⟩ := hn
  simpa only [heb] using
    (freeBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound
      d n beta hbeta eb C hC.isOpen.measurableSet)

theorem infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet)
    (C : Set (InfiniteCurrentConfig (Sym2 (Site d)))) (hC : IsClopen C) :
    ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (infinitePlusCurrentMeasure d beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive e ⁻¹' C) ≤
      (infinitePlusCurrentMeasure d beta hbeta.le : Measure _) C := by
  have hconv := plusBoxCurrentMeasure_tendsto_full d beta hbeta
  have hpreClopen := hC.preimage (continuous_forceInfiniteCurrentEdgePositive e)
  have hpre := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hconv hpreClopen
  have hbase := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hconv hC
  have hpreE := (ENNReal.tendsto_coe).2 hpre
  have hbaseE := (ENNReal.tendsto_coe).2 hbase
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hpreE hbaseE
  have hcpre : Filter.Tendsto
      (fun n => ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (plusBoxCurrentMeasure d n beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive e ⁻¹' C))
      Filter.atTop (nhds (ENNReal.ofReal (currentTraceInsertionConstant beta) *
        (infinitePlusCurrentMeasure d beta hbeta.le : Measure _)
          (forceInfiniteCurrentEdgePositive e ⁻¹' C))) :=
    ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (currentTraceInsertionConstant beta)) hpreE
      (Or.inr ENNReal.ofReal_ne_top)
  apply le_of_tendsto_of_tendsto hcpre hbaseE
  filter_upwards [eventually_boxCurrentEdgeIncl_eq d e he] with n hn
  obtain ⟨eb, heb⟩ := hn
  simpa only [heb] using
    (plusBoxCurrentMeasure_forceInfiniteCurrentEdgePositive_bound
      d n beta hbeta eb C hC.isOpen.measurableSet)

theorem isClopen_of_mem_currentMeasurableCylinders
    {E : Type*} (C : Set (InfiniteCurrentConfig E))
    (hC : C ∈ measurableCylinders (fun _ : E => ℕ)) : IsClopen C := by
  rw [mem_measurableCylinders] at hC
  obtain ⟨S, A, _, rfl⟩ := hC
  simpa only [currentCylinder, cylinder, Finset.restrict] using
    (isClopen_currentCylinder S A)

theorem infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet)
    (C : Set (InfiniteCurrentConfig (Sym2 (Site d))))
    (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => ℕ)) :
    currentTraceInsertionConstant beta *
        (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
          (forceInfiniteCurrentEdgePositive e ⁻¹' C) ≤
      (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real C := by
  have h := infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound
    d beta hbeta e he C (isClopen_of_mem_currentMeasurableCylinders C hC)
  have hreal := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr h
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (currentTraceInsertionConstant_pos hbeta).le] at hreal
  exact hreal

theorem infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet)
    (C : Set (InfiniteCurrentConfig (Sym2 (Site d))))
    (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => ℕ)) :
    currentTraceInsertionConstant beta *
        (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
          (forceInfiniteCurrentEdgePositive e ⁻¹' C) ≤
      (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real C := by
  have h := infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_clopen_bound
    d beta hbeta e he C (isClopen_of_mem_currentMeasurableCylinders C hC)
  have hreal := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr h
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (currentTraceInsertionConstant_pos hbeta).le] at hreal
  exact hreal



theorem currentModification_bound_of_cylinders
    {E : Type*} [Countable E]
    (mu : Measure (InfiniteCurrentConfig E)) [IsProbabilityMeasure mu]
    (f : InfiniteCurrentConfig E → InfiniteCurrentConfig E) (hf : Measurable f)
    (c : ℝ) (hc : 0 ≤ c)
    (hcyl : ∀ C ∈ measurableCylinders (fun _ : E => ℕ),
      c * mu.real (f ⁻¹' C) ≤ mu.real C)
    (A : Set (InfiniteCurrentConfig E)) (hA : MeasurableSet A) :
    c * mu.real (f ⁻¹' A) ≤ mu.real A := by
  let nu : Measure (InfiniteCurrentConfig E) := mu.map f
  let lam : Measure (InfiniteCurrentConfig E) := mu + nu
  have hfA : MeasurableSet (f ⁻¹' A) := hA.preimage hf
  refine le_of_forall_pos_le_add fun eps heps => ?_
  let delta : ℝ := eps / (c + 1)
  have hc1 : 0 < c + 1 := by linarith
  have hdelta : 0 < delta := div_pos heps hc1
  obtain ⟨C, hCmem, happrox⟩ := current_exists_cylinder_symmDiff_lt lam hA
    (epsilon := ENNReal.ofReal delta) (by simpa using hdelta)
  have hC : MeasurableSet C :=
    MeasurableSet.of_mem_measurableCylinders hCmem
  have hsd : MeasurableSet (C ∆ A) := hC.symmDiff hA
  have hlamReal : lam.real (C ∆ A) < delta := by
    have htop : lam (C ∆ A) ≠ ⊤ := measure_ne_top lam _
    have h := (ENNReal.toReal_lt_toReal htop (by simp)).2 happrox
    rwa [ENNReal.toReal_ofReal hdelta.le] at h
  have hmu_le : mu.real (C ∆ A) ≤ lam.real (C ∆ A) := by
    unfold Measure.real
    apply ENNReal.toReal_mono (measure_ne_top lam _)
    exact Measure.le_iff'.mp (Measure.le_add_right le_rfl) (C ∆ A)
  have hnu_le : nu.real (C ∆ A) ≤ lam.real (C ∆ A) := by
    unfold Measure.real
    apply ENNReal.toReal_mono (measure_ne_top lam _)
    exact Measure.le_iff'.mp (Measure.le_add_left le_rfl) (C ∆ A)
  have hmuDiff : |mu.real C - mu.real A| < delta :=
    lt_of_le_of_lt
      (abs_measureReal_sub_le_measureReal_symmDiff
        hC.nullMeasurableSet hA.nullMeasurableSet)
      (hmu_le.trans_lt hlamReal)
  have hnuMap : nu.real (C ∆ A) = mu.real (f ⁻¹' (C ∆ A)) := by
    unfold nu Measure.real
    rw [Measure.map_apply hf hsd]
  have hpreSd : f ⁻¹' (C ∆ A) = (f ⁻¹' C) ∆ (f ⁻¹' A) := by
    ext x
    simp
  have hnuDiff : |mu.real (f ⁻¹' C) - mu.real (f ⁻¹' A)| < delta := by
    have hpreC : MeasurableSet (f ⁻¹' C) := hC.preimage hf
    have habs : |mu.real (f ⁻¹' C) - mu.real (f ⁻¹' A)| ≤
        mu.real ((f ⁻¹' C) ∆ (f ⁻¹' A)) :=
      abs_measureReal_sub_le_measureReal_symmDiff
        hpreC.nullMeasurableSet hfA.nullMeasurableSet
    rw [← hpreSd, ← hnuMap] at habs
    exact lt_of_le_of_lt habs (hnu_le.trans_lt hlamReal)
  have hCbound := hcyl C hCmem
  obtain ⟨hmuLower, hmuUpper⟩ := abs_lt.mp hmuDiff
  obtain ⟨hnuLower, hnuUpper⟩ := abs_lt.mp hnuDiff
  dsimp [delta] at hmuLower hmuUpper hnuLower hnuUpper
  nlinarith [div_mul_cancel₀ eps (ne_of_gt hc1)]

theorem infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).map
        (forceInfiniteCurrentEdgePositive e) ≪
      (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _) := by
  apply StatMech.FK.map_absolutelyContinuous_of_real_preimage_bound
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _)
    (forceInfiniteCurrentEdgePositive e)
    (continuous_forceInfiniteCurrentEdgePositive e).measurable
    (currentTraceInsertionConstant beta)
    (currentTraceInsertionConstant_pos hbeta)
  intro A hA
  exact currentModification_bound_of_cylinders
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _)
    (forceInfiniteCurrentEdgePositive e)
    (continuous_forceInfiniteCurrentEdgePositive e).measurable
    (currentTraceInsertionConstant beta)
    (currentTraceInsertionConstant_pos hbeta).le
    (infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound
      d beta hbeta e he) A hA

theorem infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet) :
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).map
        (forceInfiniteCurrentEdgePositive e) ≪
      (infinitePlusCurrentMeasure d beta hbeta.le : Measure _) := by
  apply StatMech.FK.map_absolutelyContinuous_of_real_preimage_bound
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _)
    (forceInfiniteCurrentEdgePositive e)
    (continuous_forceInfiniteCurrentEdgePositive e).measurable
    (currentTraceInsertionConstant beta)
    (currentTraceInsertionConstant_pos hbeta)
  intro A hA
  exact currentModification_bound_of_cylinders
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _)
    (forceInfiniteCurrentEdgePositive e)
    (continuous_forceInfiniteCurrentEdgePositive e).measurable
    (currentTraceInsertionConstant beta)
    (currentTraceInsertionConstant_pos hbeta).le
    (infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_cylinder_real_bound
      d beta hbeta e he) A hA



theorem independentSuperposedTraceLaw_setOpen_absolutelyContinuous_of_fst
    {E : Type*} [Countable E] [DecidableEq E]
    (mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)) (e : E)
    (hmu : (mu : Measure _).map (forceInfiniteCurrentEdgePositive e) ≪
      (mu : Measure _)) :
    (independentSuperposedTraceLaw mu nu : Measure _).map
    (setOpen e) ≪
      (independentSuperposedTraceLaw mu nu : Measure _) := by
  let T : InfiniteCurrentConfig E × InfiniteCurrentConfig E →
      InfiniteCurrentConfig E × InfiniteCurrentConfig E :=
    Prod.map (forceInfiniteCurrentEdgePositive e) id
  have hTmeas : Measurable T :=
    (continuous_forceInfiniteCurrentEdgePositive e).measurable.prodMap measurable_id
  have hpair : (mu.prod nu : Measure _).map T ≪ (mu.prod nu : Measure _) := by
    change Measure.map (Prod.map (forceInfiniteCurrentEdgePositive e) id)
        ((mu : Measure (InfiniteCurrentConfig E)).prod
          (nu : Measure (InfiniteCurrentConfig E))) ≪
      (mu : Measure (InfiniteCurrentConfig E)).prod
        (nu : Measure (InfiniteCurrentConfig E))
    have hprod := hmu.prod
      (Measure.absolutelyContinuous_refl
        (nu : Measure (InfiniteCurrentConfig E)))
    have hmap := Measure.map_prod_map
      (mu : Measure (InfiniteCurrentConfig E))
      (nu : Measure (InfiniteCurrentConfig E))
      (continuous_forceInfiniteCurrentEdgePositive e).measurable measurable_id
    rw [← hmap]
    simpa only [Measure.map_id] using hprod
  have htrace := hpair.map continuous_superposedCurrentTrace.measurable
  have hsemiconj : (setOpen e) ∘ superposedCurrentTrace =
      superposedCurrentTrace ∘ T := by
    funext pair
    exact (superposedCurrentTrace_forceInfiniteCurrentEdgePositive_fst
      e pair.1 pair.2).symm
  change Measure.map (setOpen e)
      (Measure.map superposedCurrentTrace (mu.prod nu : Measure _)) ≪
    Measure.map superposedCurrentTrace (mu.prod nu : Measure _)
  rw [Measure.map_map (StatMech.FK.measurable_setOpen e)
      continuous_superposedCurrentTrace.measurable,
    hsemiconj,
    ← Measure.map_map continuous_superposedCurrentTrace.measurable hTmeas]
  exact htrace

theorem freeFreeSuperposedTraceLaw_setOpen_absolutelyContinuous
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet) :
    (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _).map
          (setOpen e) ≪
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _) :=
  independentSuperposedTraceLaw_setOpen_absolutelyContinuous_of_fst
    (infiniteFreeCurrentMeasure d beta hbeta.le)
    (infiniteFreeCurrentMeasure d beta hbeta.le) e
    (infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous
      d beta hbeta e he)

theorem freePlusSuperposedTraceLaw_setOpen_absolutelyContinuous
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet) :
    (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _).map
          (setOpen e) ≪
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _) :=
  independentSuperposedTraceLaw_setOpen_absolutelyContinuous_of_fst
    (infiniteFreeCurrentMeasure d beta hbeta.le)
    (infinitePlusCurrentMeasure d beta hbeta.le) e
    (infiniteFreeCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous
      d beta hbeta e he)

theorem plusPlusSuperposedTraceLaw_setOpen_absolutelyContinuous
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : Sym2 (Site d)) (he : e ∈ (hypercubicLattice d).edgeSet) :
    (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _).map
          (setOpen e) ≪
      (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _) :=
  independentSuperposedTraceLaw_setOpen_absolutelyContinuous_of_fst
    (infinitePlusCurrentMeasure d beta hbeta.le)
    (infinitePlusCurrentMeasure d beta hbeta.le) e
    (infinitePlusCurrentMeasure_forceInfiniteCurrentEdgePositive_absolutelyContinuous
      d beta hbeta e he)






def HasLatticeFiniteEnergyMerge
    {d : ℕ} (mu : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∀ F : Finset (Sym2 (Site d)),
    (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet →
      mu.map (fun omega => StatMech.Percolation.forceOpenFinset F omega) ≪ mu



theorem hasLatticeFiniteEnergyMerge_of_singleOpen
    {d : ℕ} (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (hone : ∀ e : Sym2 (Site d), e ∈ (hypercubicLattice d).edgeSet →
      mu.map (setOpen e) ≪ mu) :
    HasLatticeFiniteEnergyMerge mu := by
  intro F hF
  induction F using Finset.induction with
  | empty =>
      have hempty : StatMech.Percolation.forceOpenFinset
          (∅ : Finset (Sym2 (Site d))) = id := by
        funext omega x
        simp [StatMech.Percolation.forceOpenFinset]
      rw [hempty, Measure.map_id]
  | @insert e F he ih =>
      have heL : e ∈ (hypercubicLattice d).edgeSet := hF (by simp)
      have hFL : (↑F : Set (Sym2 (Site d))) ⊆
          (hypercubicLattice d).edgeSet := by
        intro f hf
        exact hF (by simp [hf])
      have hmap := (ih hFL).map (StatMech.FK.measurable_setOpen e)
      have htrans := hmap.trans (hone e heL)
      rw [Measure.map_map (StatMech.FK.measurable_setOpen e)
        (StatMech.Percolation.measurable_forceOpenFinset F)] at htrans
      rwa [← StatMech.FK.forceOpenFinset_insert e F] at htrans

theorem freeFreeSuperposedTraceLaw_hasLatticeFiniteEnergyMerge
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    HasLatticeFiniteEnergyMerge (d := d)
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _) :=
  hasLatticeFiniteEnergyMerge_of_singleOpen (d := d) _
    (freeFreeSuperposedTraceLaw_setOpen_absolutelyContinuous d beta hbeta)

theorem freePlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    HasLatticeFiniteEnergyMerge (d := d)
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _) :=
  hasLatticeFiniteEnergyMerge_of_singleOpen (d := d) _
    (freePlusSuperposedTraceLaw_setOpen_absolutelyContinuous d beta hbeta)

theorem plusPlusSuperposedTraceLaw_hasLatticeFiniteEnergyMerge
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    HasLatticeFiniteEnergyMerge (d := d)
      (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) : Measure _) :=
  hasLatticeFiniteEnergyMerge_of_singleOpen (d := d) _
    (plusPlusSuperposedTraceLaw_setOpen_absolutelyContinuous d beta hbeta)

end StatMech.FrontierB
