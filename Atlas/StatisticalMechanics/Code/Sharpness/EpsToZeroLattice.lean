/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Sharpness.CToOneLattice
import Code.Sharpness.EpsToZero
import Code.Ising.GHSInhomogeneous
import Code.Lattice.PathVisitsRow
import Code.Lattice.PlanarTopology

open scoped BigOperators
open Filter Topology Finset SimpleGraph

namespace StatMech
namespace Sharpness

open Ising Lattice


noncomputable def sctBoxCovariance (d : ℕ) (beta h : ℝ) (n : ℕ)
    (x : sctBox d n) : ℝ :=
  isingExpectation (sctBoxGraph d n) beta h
      (fun s => spin s (sctBoxOrigin d n) * spin s x) -
    sctOriginMag d beta h n * sctBoxMag d beta h n x




noncomputable def sctExteriorNeighbours (d n : ℕ) (x : Site d) : Finset (Site d) :=
  ((hypercubicLattice d).neighborFinset x).filter (fun y => y ∉ box d n)








noncomputable def sctBoundaryCovarianceError (d : ℕ) (beta h : ℝ) (n : ℕ) : ℝ :=
  ∑ x : sctBox d n,
    ((sctExteriorNeighbours d n x.1).card : ℝ) * sctBoxCovariance d beta h n x


noncomputable def sctOuterCovarianceSum (d : ℕ) (beta h : ℝ) (n : ℕ) : ℝ :=
  ∑ x : sctBox d n,
    if x.1 ∈ box d (n - 1) then 0 else sctBoxCovariance d beta h n x


def sctInnerField (d : ℕ) (beta h : ℝ) (n : ℕ) (x : sctBox d n) : ℝ :=
  if x.1 ∈ box d (n - 1) then beta * h else 0


def sctOuterDirection (d n : ℕ) (x : sctBox d n) : ℝ :=
  if x.1 ∈ box d (n - 1) then 0 else 1


noncomputable def sctInnerFieldMag (d : ℕ) (beta h : ℝ) (n : ℕ) : ℝ :=
  expJ (sctBoxGraph d n).edgeFinset (fun _ => beta)
    (sctInnerField d beta h n) (fun s => spin s (sctBoxOrigin d n))



theorem sct_expJ_const_eq_isingExpectation (d n : ℕ) (beta h : ℝ)
    (f : ConfigSpace (sctBox d n) → ℝ) :
    expJ (sctBoxGraph d n).edgeFinset (fun _ => beta) (fun _ => beta * h) f =
      isingExpectation (sctBoxGraph d n) beta h f := by
  unfold expJ isingExpectation isingProb
  rw [ZJ_edgeFinset_const_eq_isingZ]
  simp_rw [wJ_edgeFinset_const_eq_isingWeight]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem sct_fieldLine_inner_outer_eq_const (d : ℕ) (beta h : ℝ) (n : ℕ) :
    ghsiFieldLine (sctInnerField d beta h n) (sctOuterDirection d n) (beta * h) =
      (fun _ => beta * h) := by
  funext x
  unfold ghsiFieldLine sctInnerField sctOuterDirection
  by_cases hx : x.1 ∈ box d (n - 1) <;> simp [hx]

theorem sct_fieldLine_inner_outer_zero (d : ℕ) (beta h : ℝ) (n : ℕ) :
    ghsiFieldLine (sctInnerField d beta h n) (sctOuterDirection d n) 0 =
      sctInnerField d beta h n := by
  funext x
  simp [ghsiFieldLine]

theorem sctOuterDirection_origin (d n : ℕ) :
    sctOuterDirection d n (sctBoxOrigin d n) = 0 := by
  unfold sctOuterDirection
  simp [sctBoxOrigin, mem_box]

theorem sctOuterDirection_nonneg (d n : ℕ) :
    ∀ x, 0 ≤ sctOuterDirection d n x := by
  intro x
  unfold sctOuterDirection
  split <;> norm_num

theorem sctInnerField_nonneg (d : ℕ) (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (n : ℕ) :
    ∀ x, 0 ≤ sctInnerField d beta h n x := by
  intro x
  unfold sctInnerField
  split
  · exact mul_nonneg hbeta hh
  · exact le_rfl

theorem sct_ghsiCovariance_const_eq (d : ℕ) (beta h : ℝ) (n : ℕ)
    (x : sctBox d n) :
    ghsiCovariance (sctBoxGraph d n) (fun _ => beta) (fun _ => beta * h)
        (sctBoxOrigin d n) x = sctBoxCovariance d beta h n x := by
  unfold ghsiCovariance sctBoxCovariance sctOriginMag sctBoxMag
  rw [sct_expJ_const_eq_isingExpectation,
    sct_expJ_const_eq_isingExpectation, sct_expJ_const_eq_isingExpectation]



theorem sct_directionalCovariance_eq_outer (d : ℕ) (beta h : ℝ) (n : ℕ) :
    ghsiDirectionalCovariance (sctBoxGraph d n) (fun _ => beta)
        (fun _ => beta * h) (sctOuterDirection d n)
        (fun s => spin s (sctBoxOrigin d n)) =
      sctOuterCovarianceSum d beta h n := by
  rw [ghsi_directionalCovariance_eq_sum_covariance]
  unfold sctOuterCovarianceSum
  apply Finset.sum_congr rfl
  intro x _
  unfold sctOuterDirection
  split_ifs with hx
  · simp
  · rw [one_mul, sct_ghsiCovariance_const_eq]


theorem sctOuterCovarianceSum_le_secant (d : ℕ) (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) (n : ℕ) :
    sctOuterCovarianceSum d beta h n ≤
      (sctOriginMag d beta h n - sctInnerFieldMag d beta h n) / (beta * h) := by
  have hs := ghsi_directionalCovariance_le_secant (sctBoxGraph d n)
    (fun _ => beta) (sctInnerField d beta h n) (sctOuterDirection d n)
    (fun _ => hbeta.le) (sctInnerField_nonneg d beta h hbeta.le hh.le n)
    (sctOuterDirection_nonneg d n) (sctBoxOrigin d n)
    (sctOuterDirection_origin d n) (mul_pos hbeta hh)
  rw [sct_fieldLine_inner_outer_eq_const,
    sct_fieldLine_inner_outer_zero] at hs
  rw [sct_directionalCovariance_eq_outer] at hs
  unfold sctInnerFieldMag
  rw [sct_expJ_const_eq_isingExpectation] at hs
  exact hs




theorem sctOriginMag_pred_le_innerFieldMag (d : ℕ) (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (n : ℕ) :
    sctOriginMag d beta h (n - 1) ≤ sctInnerFieldMag d beta h n := by
  let K := sctBoxGraph d n
  let P : sctBox d n → Prop := sctBoxInLarger d (n - 1) n
  let L : SimpleGraph {x : sctBox d n // P x} := FK.agl_left K P
  let I : SimpleGraph {x : sctBox d n // ¬ P x} := ⊥
  let S : SimpleGraph ({x : sctBox d n // P x} ⊕ {x : sctBox d n // ¬ P x}) := L ⊕g I
  let T : SimpleGraph ({x : sctBox d n // P x} ⊕ {x : sctBox d n // ¬ P x}) :=
    FK.agl_glueGraph K P
  let R : SimpleGraph {x : sctBox d n // ¬ P x} := FK.agl_right K P
  let e : ({x : sctBox d n // P x} ⊕ {x : sctBox d n // ¬ P x}) ≃ sctBox d n :=
    FK.agl_sumEquiv P
  let oi : {x : sctBox d n // P x} :=
    ⟨sctBoxOrigin d n, by
      intro i
      simp [P, sctBoxInLarger, sctBoxOrigin]⟩
  let einc := sctBoxInclusionEquiv d (Nat.sub_le n 1)
  have heinc_origin : einc (sctBoxOrigin d (n - 1)) = oi := by
    ext i
    rfl
  have hsmall : sctOriginMag d beta h (n - 1) =
      expJ L.edgeFinset (fun _ => beta) (fun _ => beta * h)
        (fun s => spin s oi) := by
    unfold sctOriginMag sctBoxMag
    have hr := isingExpectation_spin_relabel (sctBoxGraph d (n - 1)) L einc
      (sctBoxInclusionEquiv_adj d (Nat.sub_le n 1)) beta h
      (sctBoxOrigin d (n - 1))
    rw [heinc_origin] at hr
    rw [hr, isingExpectation_spin_eq_expJ]
    rw [spinProd_singleton]
  let hfSum : ({x : sctBox d n // P x} ⊕ {x : sctBox d n // ¬ P x}) → ℝ :=
    Sum.elim (fun _ => beta * h) (fun _ => 0)
  have hsum : expJ L.edgeFinset (fun _ => beta) (fun _ => beta * h)
      (fun s => spin s oi) =
      expJ S.edgeFinset (fun _ => beta) hfSum (fun s => spin s (Sum.inl oi)) := by
    symm
    exact ghsi_expJ_spin_sum_inl L I beta (fun _ => beta * h) (fun _ => 0) oi
  have hSI : S ≤ L ⊕g R := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · simpa [S, L, I, R, SimpleGraph.sum_adj] using hab
    · simpa [S, L, I, R, SimpleGraph.sum_adj] using hab
    · simpa [S, L, I, R, SimpleGraph.sum_adj] using hab
    · simpa [S, L, I, R, SimpleGraph.sum_adj] using hab
  have hST : S ≤ T :=
    le_trans hSI (show L ⊕g R ≤ T from (FK.agl_partitionCrossInterface K P).le)
  have hmono : expJ S.edgeFinset (fun _ => beta) hfSum
      (fun s => spin s (Sum.inl oi)) ≤
      expJ T.edgeFinset (fun _ => beta) hfSum
        (fun s => spin s (Sum.inl oi)) := by
    rw [← spinProd_singleton]
    apply griffiths_mono_spin
    · exact SimpleGraph.edgeFinset_mono hST
    · exact fun _ _ => hbeta
    · intro z
      rcases z with z | z
      · exact mul_nonneg hbeta hh
      · exact le_rfl
    · intro edge hedge _
      exact SimpleGraph.not_isDiag_of_mem_edgeFinset hedge
  have hfield : ∀ z, hfSum z = sctInnerField d beta h n (e z) := by
    intro z
    rcases z with z | z
    · have hz : z.1.1 ∈ box d (n - 1) := by
        simpa [P, sctBoxInLarger] using z.2
      simp [hfSum, e, sctInnerField, hz]
    · have hz : z.1.1 ∉ box d (n - 1) := by
        simpa [P, sctBoxInLarger] using z.2
      simp [hfSum, e, sctInnerField, hz]
  have hrelabel : expJ T.edgeFinset (fun _ => beta) hfSum
      (fun s => spin s (Sum.inl oi)) = sctInnerFieldMag d beta h n := by
    unfold sctInnerFieldMag
    have hr := ghsi_expJ_spin_const_relabel T K e
      (fun u v => FK.agl_glueGraph_adj K P u v) beta hfSum
      (sctInnerField d beta h n) hfield (Sum.inl oi)
    have heo : e (Sum.inl oi) = sctBoxOrigin d n := by
      rfl
    rwa [heo] at hr
  calc
    sctOriginMag d beta h (n - 1) =
        expJ L.edgeFinset (fun _ => beta) (fun _ => beta * h)
          (fun s => spin s oi) := hsmall
    _ = expJ S.edgeFinset (fun _ => beta) hfSum
          (fun s => spin s (Sum.inl oi)) := hsum
    _ ≤ expJ T.edgeFinset (fun _ => beta) hfSum
          (fun s => spin s (Sum.inl oi)) := hmono
    _ = sctInnerFieldMag d beta h n := hrelabel


theorem sctOuterCovarianceSum_le_magDiff (d : ℕ) (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) (n : ℕ) :
    sctOuterCovarianceSum d beta h n ≤
      (sctOriginMag d beta h n - sctOriginMag d beta h (n - 1)) / (beta * h) := by
  have hs := sctOuterCovarianceSum_le_secant d beta h hbeta hh n
  have hm := sctOriginMag_pred_le_innerFieldMag d beta h hbeta.le hh.le n
  have hden : 0 < beta * h := mul_pos hbeta hh
  apply hs.trans
  exact div_le_div_of_nonneg_right (sub_le_sub_left hm _) hden.le


theorem sctBoxCovariance_nonneg (d : ℕ) (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (n : ℕ) (x : sctBox d n) :
    0 ≤ sctBoxCovariance d beta h n x := by
  by_cases hxo : x = sctBoxOrigin d n
  · subst x
    unfold sctBoxCovariance sctOriginMag sctBoxMag
    have hsq :
        (fun s => spin s (sctBoxOrigin d n) * spin s (sctBoxOrigin d n)) =
          (fun _ : ConfigSpace (sctBox d n) => (1 : ℝ)) := by
      funext s
      exact spin_sq s (sctBoxOrigin d n)
    rw [hsq]
    have hone :
        isingExpectation (sctBoxGraph d n) beta h
            (fun _ : ConfigSpace (sctBox d n) => (1 : ℝ)) = 1 := by
      unfold isingExpectation
      simp [isingProb_sum_eq_one (sctBoxGraph d n) beta h]
    rw [hone]
    have hb := expectation_spin_bounds (sctBoxGraph d n) beta h hbeta hh
      (sctBoxOrigin d n)
    nlinarith [hb.1, hb.2]
  · unfold sctBoxCovariance sctOriginMag sctBoxMag
    have hc := cov_nonneg (sctBoxGraph d n) beta h hbeta hh
      (sctBoxOrigin d n) x (Ne.symm hxo)
    linarith


theorem sctBoundaryCovarianceError_nonneg (d : ℕ) (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (n : ℕ) :
    0 ≤ sctBoundaryCovarianceError d beta h n := by
  unfold sctBoundaryCovarianceError
  exact Finset.sum_nonneg (fun x _ =>
    mul_nonneg (Nat.cast_nonneg _) (sctBoxCovariance_nonneg d beta h hbeta hh n x))


theorem sctExteriorNeighbours_card_le (d n : ℕ) (x : Site d) :
    (sctExteriorNeighbours d n x).card ≤ 2 * d := by
  unfold sctExteriorNeighbours
  calc
    (((hypercubicLattice d).neighborFinset x).filter (fun y => y ∉ box d n)).card
        ≤ ((hypercubicLattice d).neighborFinset x).card := Finset.card_filter_le _ _
    _ = (hypercubicLattice d).degree x :=
      SimpleGraph.card_neighborFinset_eq_degree _ _
    _ = 2 * d := degree_eq d x


theorem sct_adj_mem_box_of_mem_box_pred {d n : ℕ} (hn : 1 ≤ n)
    {x y : Site d} (hx : x ∈ box d (n - 1))
    (hxy : (hypercubicLattice d).Adj x y) : y ∈ box d n := by
  rw [mem_box] at hx ⊢
  intro i
  have hstep := pvr_adj_coord_diff_le_one hxy i
  have htri : (y i).natAbs ≤ (x i).natAbs + (x i - y i).natAbs := by
    have := Int.natAbs_add_le (x i) (y i - x i)
    rw [show x i + (y i - x i) = y i by ring] at this
    rw [show (y i - x i).natAbs = (x i - y i).natAbs by
      rw [← Int.natAbs_neg]; congr 1; ring] at this
    exact this
  calc
    (y i).natAbs ≤ (x i).natAbs + (x i - y i).natAbs := htri
    _ ≤ (n - 1) + 1 := Nat.add_le_add (hx i) hstep
    _ = n := Nat.sub_add_cancel hn


theorem sctExteriorNeighbours_eq_empty_of_mem_pred {d n : ℕ} (hn : 1 ≤ n)
    {x : Site d} (hx : x ∈ box d (n - 1)) :
    sctExteriorNeighbours d n x = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  rw [sctExteriorNeighbours, Finset.mem_filter,
    SimpleGraph.mem_neighborFinset] at hy
  exact hy.2 (sct_adj_mem_box_of_mem_box_pred hn hx hy.1)



theorem sctBoundaryCovarianceError_outerLayer (d : ℕ) (beta h : ℝ)
    (n : ℕ) (hn : 1 ≤ n) :
    sctBoundaryCovarianceError d beta h n =
      ∑ x : sctBox d n,
        if x.1 ∈ box d (n - 1) then 0
        else ((sctExteriorNeighbours d n x.1).card : ℝ) *
          sctBoxCovariance d beta h n x := by
  unfold sctBoundaryCovarianceError
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hx
  · rw [sctExteriorNeighbours_eq_empty_of_mem_pred hn hx]
    simp
  · rfl





theorem sctBoundaryCovarianceError_le_outer (d : ℕ) (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (n : ℕ) (hn : 1 ≤ n) :
    sctBoundaryCovarianceError d beta h n ≤
      (2 * d : ℝ) * sctOuterCovarianceSum d beta h n := by
  rw [sctBoundaryCovarianceError_outerLayer d beta h n hn]
  unfold sctOuterCovarianceSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hx
  · simp
  · have hcov := sctBoxCovariance_nonneg d beta h hbeta hh n x
    have hcard : ((sctExteriorNeighbours d n x.1).card : ℝ) ≤ (2 * d : ℝ) := by
      exact_mod_cast sctExteriorNeighbours_card_le d n x.1
    exact mul_le_mul_of_nonneg_right hcard hcov



theorem sctOriginMag_tendsto_iSup (d : ℕ) (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    Tendsto (sctOriginMag d beta h) atTop
      (nhds (⨆ n : ℕ, sctOriginMag d beta h n)) := by
  apply tendsto_atTop_ciSup (sctOriginMag_monotone d beta h hbeta hh)
  refine ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact sctOriginMag_le_one d beta h n


theorem sctOuterCovarianceSum_tendsto_zero (d : ℕ) (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (sctOuterCovarianceSum d beta h) atTop (nhds 0) := by
  let M : ℕ → ℝ := sctOriginMag d beta h
  have hM : Tendsto M atTop (nhds (⨆ n : ℕ, M n)) := by
    exact sctOriginMag_tendsto_iSup d beta h hbeta.le hh.le
  have hdiff : Tendsto
      (fun n : ℕ => (M n - M (n - 1)) / (beta * h)) atTop (nhds 0) := by
    have ht := (set_annularDiff_tendsto_zero M hM 1).div_const (beta * h)
    simpa using ht
  apply squeeze_zero
  · intro n
    unfold sctOuterCovarianceSum
    exact Finset.sum_nonneg (fun x _ => by
      split_ifs
      · exact le_rfl
      · exact sctBoxCovariance_nonneg d beta h hbeta.le hh.le n x)
  · intro n
    exact sctOuterCovarianceSum_le_magDiff d beta h hbeta hh n
  · exact hdiff




theorem sctBoundaryCovarianceError_tendsto_zero (d : ℕ) (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (sctBoundaryCovarianceError d beta h) atTop (nhds 0) := by
  have houter := sctOuterCovarianceSum_tendsto_zero d beta h hbeta hh
  have hscaled : Tendsto
      (fun n : ℕ => (2 * d : ℝ) * sctOuterCovarianceSum d beta h n)
      atTop (nhds 0) := by
    simpa using houter.const_mul (2 * d : ℝ)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall
      (sctBoundaryCovarianceError_nonneg d beta h hbeta.le hh.le)
  · rw [Filter.eventually_atTop]
    exact ⟨1, fun n hn =>
      sctBoundaryCovarianceError_le_outer d beta h hbeta.le hh.le n hn⟩
  · exact hscaled

end Sharpness
end StatMech
