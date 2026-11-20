/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionCriticalReduction
import Code.FrontierA.IsingSurfaceTensionUnconditionalBounds
import Code.FrontierA.IsingSurfaceTensionPrismGinibre
import Code.FrontierB.CurrentContinuityVaryingTemperature
import Code.Ising.IsingMinusTIFromPlacement
import Code.Ising.GHSInhomogeneous
import Code.Sharpness.Simon










open Filter MeasureTheory Topology

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Lattice StatMech.ConfigSpace StatMech.FK
  StatMech.Sharpness

noncomputable section

variable {d : Nat}




theorem varyingFiniteGibbs_tendsto_of_unique
    (beta : Real) (muLim : ProbabilityMeasure (ConfigSpace (Site d)))
    (hunique : forall (mu : Measure (ConfigSpace (Site d)))
      [IsProbabilityMeasure mu],
      IsDLRState d beta 0 mu -> mu = (muLim : Measure _))
    (eta : Nat -> ConfigSpace (Site d)) (radius : Nat -> Nat)
    (hradius : Tendsto radius atTop atTop) :
    WeakConvergesTo
      (fun k => fvProbabilityMeasure (eta k) (radius k)
        (bondFinsetTouch d (radius k)) beta 0)
      muLim := by
  let mu : Nat -> ProbabilityMeasure (ConfigSpace (Site d)) := fun k =>
    fvProbabilityMeasure (eta k) (radius k)
      (bondFinsetTouch d (radius k)) beta 0
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨nu, phi, hphi, hweak⟩ := prokhorov_seq_compact (mu ∘ ns)
  have hcofinal : Tendsto (ns ∘ phi) atTop atTop :=
    hns.comp hphi.tendsto_atTop
  have hdlr : IsDLRState d beta 0
      (nu : Measure (ConfigSpace (Site d))) := by
    apply StatMech.FrontierB.varyingFiniteGibbsWeakLimit_isDLR
      (eta := eta ∘ ns ∘ phi) (radius := radius ∘ ns ∘ phi)
      (betaSeq := fun _ => beta) (beta := beta) (h := 0)
    · exact hradius.comp hcofinal
    · exact tendsto_const_nhds
    · simpa only [mu, Function.comp_assoc] using hweak
  have hnuMeasure : (nu : Measure (ConfigSpace (Site d))) =
      (muLim : Measure (ConfigSpace (Site d))) := hunique _ hdlr
  have hnu : nu = muLim := by
    apply ProbabilityMeasure.toMeasure_injective
    exact hnuMeasure
  refine ⟨phi, ?_⟩
  simpa only [mu, Function.comp_assoc, hnu] using hweak



theorem isingCritical_varyingFiniteGibbs_tendsto
    (eta : Nat -> ConfigSpace (Site 3)) (radius : Nat -> Nat)
    (hradius : Tendsto radius atTop atTop) :
    WeakConvergesTo
      (fun k => fvProbabilityMeasure (eta k) (radius k)
        (bondFinsetTouch 3 (radius k)) (Ising.betaC 3) 0)
      (minusState 3 (Ising.betaC 3) 0) := by
  have hbetaC : 0 < Ising.betaC 3 := isingBetaC_three_pos
  have hphase :
      (plusState 3 (Ising.betaC 3) 0 : Measure (ConfigSpace (Site 3))) =
        (minusState 3 (Ising.betaC 3) 0 : Measure (ConfigSpace (Site 3))) :=
    StatMech.FrontierB.plusState_eq_minusState_of_magnetization_eq_zero
      (Ising.betaC 3) hbetaC.le magnetization_three_isingBetaC_eq_zero
  apply varyingFiniteGibbs_tendsto_of_unique (Ising.betaC 3)
    (minusState 3 (Ising.betaC 3) 0) _ eta radius hradius
  intro mu hprob hmu
  exact gsi_gibbs_unique_of_phases_eq
    (Ising.betaC 3) 0 hbetaC.le (by norm_num) mu hmu hphase




theorem isingCritical_varyingFiniteGibbs_localExpectation_sub_tendsto_zero
    (eta zeta : Nat -> ConfigSpace (Site 3))
    (radius rho : Nat -> Nat)
    (hradius : Tendsto radius atTop atTop)
    (hrho : Tendsto rho atTop atTop)
    (f : BoundedContinuousFunction (ConfigSpace (Site 3)) Real) :
    Tendsto (fun k =>
      (∫ omega, f omega
        ∂fvMeasure (eta k) (radius k) (bondFinsetTouch 3 (radius k))
          (Ising.betaC 3) 0) -
      ∫ omega, f omega
        ∂fvMeasure (zeta k) (rho k) (bondFinsetTouch 3 (rho k))
          (Ising.betaC 3) 0) atTop (nhds 0) := by
  have heta :=
    (isingCritical_varyingFiniteGibbs_tendsto eta radius hradius).tendsto_integral f
  have hzeta :=
    (isingCritical_varyingFiniteGibbs_tendsto zeta rho hrho).tendsto_integral f
  simpa using heta.sub hzeta


theorem isingCritical_varyingFiniteGibbs_spin_sub_tendsto_zero
    (eta zeta : Nat -> ConfigSpace (Site 3))
    (radius rho : Nat -> Nat)
    (hradius : Tendsto radius atTop atTop)
    (hrho : Tendsto rho atTop atTop) (x : Site 3) :
    Tendsto (fun k =>
      (∫ omega, spin omega x
        ∂fvMeasure (eta k) (radius k) (bondFinsetTouch 3 (radius k))
          (Ising.betaC 3) 0) -
      ∫ omega, spin omega x
        ∂fvMeasure (zeta k) (rho k) (bondFinsetTouch 3 (rho k))
          (Ising.betaC 3) 0) atTop (nhds 0) := by
  simpa only [spinBCF_apply] using
    isingCritical_varyingFiniteGibbs_localExpectation_sub_tendsto_zero
      eta zeta radius rho hradius hrho (spinBCF x)







theorem gvMeasure_real_sub_abs_le_inner_extremal_gap
    {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    {beta : Real} (hbeta : 0 ≤ beta) {h : Real} (hh : 0 ≤ h)
    (eta zeta : ConfigSpace (Site d))
    {A : Set (ConfigSpace (Site d))}
    (hAmeas : MeasurableSet A) (hAinc : IsIncreasing A) :
    |(gvMeasure eta Sout beta h).real A -
        (gvMeasure zeta Sout beta h).real A| ≤
      (gvPlusMeasure Sin beta h).real A -
        (gvMinusMeasure Sin beta h).real A := by
  have hl_eta : (gvMinusMeasure Sin beta h).real A ≤
      (gvMeasure eta Sout beta h).real A :=
    (iptm_gv_crossbox_dom hsub hbeta hh hAmeas hAinc).trans
      (gvMeasure_minusField_le Sout hbeta hh eta hAmeas hAinc)
  have hl_zeta : (gvMinusMeasure Sin beta h).real A ≤
      (gvMeasure zeta Sout beta h).real A :=
    (iptm_gv_crossbox_dom hsub hbeta hh hAmeas hAinc).trans
      (gvMeasure_minusField_le Sout hbeta hh zeta hAmeas hAinc)
  have hu_eta : (gvMeasure eta Sout beta h).real A ≤
      (gvPlusMeasure Sin beta h).real A :=
    (gvMeasure_le_plusField Sout hbeta hh eta hAmeas hAinc).trans
      (iptp_gv_crossbox_dom hsub hbeta hh hAmeas hAinc)
  have hu_zeta : (gvMeasure zeta Sout beta h).real A ≤
      (gvPlusMeasure Sin beta h).real A :=
    (gvMeasure_le_plusField Sout hbeta hh zeta hAmeas hAinc).trans
      (iptp_gv_crossbox_dom hsub hbeta hh hAmeas hAinc)
  rw [abs_le]
  constructor <;> linarith


theorem isingCritical_centeredBox_spinUp_extremalGap_tendsto_zero
    (x : Site 3) :
    Tendsto (fun n =>
      (gvPlusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real
          {omega | omega x = true} -
        (gvMinusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real
          {omega | omega x = true}) atTop (nhds 0) := by
  let radius : Nat -> Nat := fun n => n
  have hradius : Tendsto radius atTop atTop := tendsto_id
  have hplus :=
    (isingCritical_varyingFiniteGibbs_tendsto
      (fun _ => plusField 3) radius hradius).tendsto_integral
        (pstc_coordBcf x)
  have hminus :=
    (isingCritical_varyingFiniteGibbs_tendsto
      (fun _ => minusField 3) radius hradius).tendsto_integral
        (pstc_coordBcf x)
  have hsub := hplus.sub hminus
  change Tendsto (fun n =>
      (∫ omega, pstc_coordBcf x omega
        ∂fvMeasure (plusField 3) n (bondFinsetTouch 3 n)
          (Ising.betaC 3) 0) -
      ∫ omega, pstc_coordBcf x omega
        ∂fvMeasure (minusField 3) n (bondFinsetTouch 3 n)
          (Ising.betaC 3) 0) atTop
    (nhds ((∫ omega, pstc_coordBcf x omega
        ∂(minusState 3 (Ising.betaC 3) 0 :
          Measure (ConfigSpace (Site 3)))) -
      ∫ omega, pstc_coordBcf x omega
        ∂(minusState 3 (Ising.betaC 3) 0 :
          Measure (ConfigSpace (Site 3))))) at hsub
  have heq : (fun n =>
      (∫ omega, pstc_coordBcf x omega
        ∂fvMeasure (plusField 3) n (bondFinsetTouch 3 n)
          (Ising.betaC 3) 0) -
      ∫ omega, pstc_coordBcf x omega
        ∂fvMeasure (minusField 3) n (bondFinsetTouch 3 n)
          (Ising.betaC 3) 0) =
      (fun n =>
        (gvPlusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real
            {omega | omega x = true} -
          (gvMinusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real
            {omega | omega x = true}) := by
    funext n
    rw [ibs_integral_coordBcf, ibs_integral_coordBcf,
      iptp_gvPlusMeasure_eq_plusMeasure,
      iptm_gvMinusMeasure_eq_minusMeasure]
    rfl
  rw [heq] at hsub
  simpa only [sub_self] using hsub




theorem gvMeasure_spinUp_sub_abs_le_critical_centeredGap
    (Sout : Finset (Site 3)) (eta zeta : ConfigSpace (Site 3))
    (x : Site 3) (n : Nat)
    (hcontain :
      (boxFinset 3 n).image
        (fun y => Multiplicative.ofAdd x • y) ⊆ Sout) :
    |(gvMeasure eta Sout (Ising.betaC 3) 0).real
          {omega | omega x = true} -
        (gvMeasure zeta Sout (Ising.betaC 3) 0).real
          {omega | omega x = true}| ≤
      (gvPlusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real
          {omega | omega (origin 3) = true} -
        (gvMinusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real
          {omega | omega (origin 3) = true} := by
  let Sin : Finset (Site 3) :=
    (boxFinset 3 n).image (fun y => Multiplicative.ofAdd x • y)
  have hraw := gvMeasure_real_sub_abs_le_inner_extremal_gap
    (Sin := Sin) (Sout := Sout) hcontain
    (le_of_lt isingBetaC_three_pos) (by norm_num : (0 : Real) ≤ 0)
    eta zeta (ibs_measurableSet_spinUp x)
    (by
      intro omega omega' homega hx
      have hxle := homega x
      cases hval : omega' x with
      | false =>
          have hx' : omega x = true := hx
          rw [hx'] at hxle
          simp [hval] at hxle
          have hfalse : false = true := hxle rfl
          exact Bool.noConfusion hfalse
      | true => exact hval)
  have hplus := iptp_gvPlus_real_shift (Multiplicative.ofAdd x)
    (boxFinset 3 n)
    (Ising.betaC 3) 0 ({x} : Finset (Site 3))
  have hminus := iptm_gvMinus_real_shift (Multiplicative.ofAdd x)
    (boxFinset 3 n)
    (Ising.betaC 3) 0 ({x} : Finset (Site 3))
  have hgorigin : (Multiplicative.ofAdd x)⁻¹ • x = origin 3 := by
    ext i
    change -x i + x i = 0
    simp
  have hset : fmu_multiOpen ({x} : Finset (Site 3)) =
      {omega | omega x = true} := by
    ext omega
    simp [fmu_multiOpen]
  have hset0 : fmu_multiOpen ({origin 3} : Finset (Site 3)) =
      {omega | omega (origin 3) = true} := by
    ext omega
    simp [fmu_multiOpen]
  have himage : ({x} : Finset (Site 3)).image
      (fun y => (Multiplicative.ofAdd x)⁻¹ • y) =
      {origin 3} := by
    simp [hgorigin]
  rw [hset, himage, hset0] at hplus hminus
  change
    (gvPlusMeasure ((boxFinset 3 n).image (fun y => x + y))
        (Ising.betaC 3) 0).real {omega | omega x = true} = _ at hplus
  change
    (gvMinusMeasure ((boxFinset 3 n).image (fun y => x + y))
        (Ising.betaC 3) 0).real {omega | omega x = true} = _ at hminus
  dsimp [Sin] at hraw
  rw [hplus, hminus] at hraw
  exact hraw



theorem isingCritical_gvBoundary_spinUp_sub_abs_tendsto_zero
    (Sout : Nat -> Finset (Site 3))
    (eta zeta : Nat -> ConfigSpace (Site 3)) (x : Site 3)
    (hcontain : forall n,
      (boxFinset 3 n).image
        (fun y => Multiplicative.ofAdd x • y) ⊆ Sout n) :
    Tendsto (fun n =>
      |(gvMeasure (eta n) (Sout n) (Ising.betaC 3) 0).real
            {omega | omega x = true} -
        (gvMeasure (zeta n) (Sout n) (Ising.betaC 3) 0).real
            {omega | omega x = true}|) atTop (nhds 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    (Filter.Eventually.of_forall fun n =>
      gvMeasure_spinUp_sub_abs_le_critical_centeredGap
        (Sout n) (eta n) (zeta n) x n (hcontain n))
  exact isingCritical_centeredBox_spinUp_extremalGap_tendsto_zero
    (origin 3)




set_option maxHeartbeats 800000 in








theorem expJ_spin_induce_le_inhomogeneous
    {U : Type*} [Fintype U] [DecidableEq U]
    (K : SimpleGraph U) [DecidableRel K.Adj]
    (P : U -> Prop) [DecidablePred P]
    (beta : Real) (hbeta : 0 <= beta)
    (hf : U -> Real) (hhf : forall u, 0 <= hf u)
    (x : {u // P u}) :
    expJ (K.comap (Subtype.val : {u // P u} -> U)).edgeFinset
        (fun _ => beta) (fun u => hf u.1) (fun s => spin s x) <=
      expJ K.edgeFinset (fun _ => beta) hf (fun s => spin s x.1) := by
  let L : SimpleGraph {u // P u} := FK.agl_left K P
  let R : SimpleGraph {u // ¬ P u} := FK.agl_right K P
  let I : SimpleGraph {u // ¬ P u} := ⊥
  let S : SimpleGraph ({u // P u} ⊕ {u // ¬ P u}) := L ⊕g I
  let T : SimpleGraph ({u // P u} ⊕ {u // ¬ P u}) :=
    FK.agl_glueGraph K P
  let e : ({u // P u} ⊕ {u // ¬ P u}) ≃ U := FK.agl_sumEquiv P
  let hfSum : ({u // P u} ⊕ {u // ¬ P u}) -> Real :=
    Sum.elim (fun u => hf u.1) (fun u => hf u.1)
  have hleft :
      expJ (K.comap (Subtype.val : {u // P u} -> U)).edgeFinset
          (fun _ => beta) (fun u => hf u.1) (fun s => spin s x) =
        expJ S.edgeFinset (fun _ => beta) hfSum
          (fun s => spin s (Sum.inl x)) := by
    symm
    exact ghsi_expJ_spin_sum_inl L I beta
      (fun u => hf u.1) (fun u => hf u.1) x
  have hSI : S <= L ⊕g R := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    all_goals simpa [S, L, I, R, SimpleGraph.sum_adj] using hab
  have hST : S <= T :=
    le_trans hSI
      (show L ⊕g R <= T from (FK.agl_partitionCrossInterface K P).le)
  have hmono :
      expJ S.edgeFinset (fun _ => beta) hfSum
          (fun s => spin s (Sum.inl x)) <=
        expJ T.edgeFinset (fun _ => beta) hfSum
          (fun s => spin s (Sum.inl x)) := by
    rw [<- spinProd_singleton]
    apply StatMech.Sharpness.griffiths_mono_spin
    · exact SimpleGraph.edgeFinset_mono hST
    · exact fun _ _ => hbeta
    · intro u
      rcases u with u | u <;> exact hhf u.1
    · intro edge hedge _
      exact SimpleGraph.not_isDiag_of_mem_edgeFinset hedge
  have hfield : forall u, hfSum u = hf (e u) := by
    intro u
    rcases u with u | u <;> rfl
  have hrelabel :
      expJ T.edgeFinset (fun _ => beta) hfSum
          (fun s => spin s (Sum.inl x)) =
        expJ K.edgeFinset (fun _ => beta) hf
          (fun s => spin s x.1) := by
    have h := ghsi_expJ_spin_const_relabel T K e
      (fun u v => FK.agl_glueGraph_adj K P u v) beta hfSum hf hfield
      (Sum.inl x)
    simpa [e] using h
  rw [hleft]
  exact hmono.trans_eq hrelabel



theorem plusMeasure_spin_eq_spinUp_sub_minus
    (d n : Nat) (beta : Real) (x : Site d) :
    (∫ omega, spin omega x
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) =
      (plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real
          {omega | omega x = true} -
        (minusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real
          {omega | omega x = true} := by
  let muMinus : Measure (ConfigSpace (Site d)) :=
    (minusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))
  let muPlus : Measure (ConfigSpace (Site d)) :=
    (plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))
  have hmap : Measure.map flipConfig muMinus = muPlus := by
    simpa [muMinus, muPlus] using
      (map_minusMeasure_eq_plusMeasure (d := d) n beta)
  have hflip :
      (∫ omega, spin omega x ∂muPlus) =
        -∫ omega, spin omega x ∂muMinus := by
    rw [<- hmap]
    rw [MeasureTheory.integral_map measurable_flipConfig.aemeasurable
      (continuous_spin_apply x).aestronglyMeasurable]
    rw [<- MeasureTheory.integral_neg]
    apply integral_congr_ae
    filter_upwards with omega
    rw [spin_flipConfig]
  have hplus := integral_spin_eq_two_mul_real_spinUp_sub_one
    (plusMeasure d n beta 0) x
  have hminus := integral_spin_eq_two_mul_real_spinUp_sub_one
    (minusMeasure d n beta 0) x
  change (∫ omega, spin omega x ∂muPlus) = _
  change (∫ omega, spin omega x ∂muPlus) =
    muPlus.real {omega | omega x = true} -
      muMinus.real {omega | omega x = true}
  change (∫ omega, spin omega x ∂muPlus) = _ at hplus hflip
  change (∫ omega, spin omega x ∂muMinus) = _ at hminus
  linarith



theorem isingCritical_oddPrismPlusSpinMean_le_centeredGap
    (n r : Nat)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n)
    (hcontain :
      (boxFinset 3 r).image (fun y =>
        Multiplicative.ofAdd
          (rectangularPrismSiteEquivSctBoxDobrushin n v).1 • y) ⊆
        boxFinset 3 n) :
    oddPrismPlusSpinMean (Ising.betaC 3) n v <=
      (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
          {omega | omega (origin 3) = true} -
        (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
          {omega | omega (origin 3) = true} := by
  let x := (rectangularPrismSiteEquivSctBoxDobrushin n v).1
  have hmono :
      (minusMeasure 3 n (Ising.betaC 3) 0 :
          Measure (ConfigSpace (Site 3))).real {omega | omega x = true} <=
        (plusMeasure 3 n (Ising.betaC 3) 0 :
          Measure (ConfigSpace (Site 3))).real {omega | omega x = true} := by
    have h := gvMeasure_minusField_le (boxFinset 3 n)
      isingBetaC_three_pos.le (by norm_num : (0 : Real) <= 0)
      (plusField 3) (ibs_measurableSet_spinUp x)
      (sct_isIncreasing_spinUp x)
    change (gvMinusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real
        {omega | omega x = true} <=
      (gvPlusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real
        {omega | omega x = true} at h
    rw [iptm_gvMinusMeasure_eq_minusMeasure,
      iptp_gvPlusMeasure_eq_plusMeasure] at h
    exact h
  have hbound := gvMeasure_spinUp_sub_abs_le_critical_centeredGap
    (boxFinset 3 n) (plusField 3) (minusField 3) x r hcontain
  change |(gvPlusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real
        {omega | omega x = true} -
      (gvMinusMeasure (boxFinset 3 n) (Ising.betaC 3) 0).real
        {omega | omega x = true}| <= _ at hbound
  rw [iptp_gvPlusMeasure_eq_plusMeasure,
    iptm_gvMinusMeasure_eq_minusMeasure] at hbound
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)] at hbound
  rw [iptp_gvPlusMeasure_eq_plusMeasure,
    iptm_gvMinusMeasure_eq_minusMeasure]
  rw [oddPrismPlusSpinMean_eq_plusMeasure_integral,
    plusMeasure_spin_eq_spinUp_sub_minus]
  simpa [x, iptp_gvPlusMeasure_eq_plusMeasure,
    iptm_gvMinusMeasure_eq_minusMeasure] using hbound



def oddPrismInternalGraph (n : Nat) :
    SimpleGraph (RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :=
  SimpleGraph.fromEdgeSet (oddPrismInternalEdges n : Set _)

theorem oddPrismInternalEdge_not_isDiag
    (n : Nat) (q : OddPrismInternalIndex n) :
    ¬ (oddPrismInternalEdge n q).IsDiag := by
  rcases q with q | q
  · simp [oddPrismInternalEdge, Sym2.mk_isDiag_iff,
      RectangularPrismSite.mk.injEq]
  · rcases q with q | q <;>
      simp [oddPrismInternalEdge, Sym2.mk_isDiag_iff,
        RectangularPrismSite.mk.injEq]

@[simp] theorem oddPrismInternalGraph_edgeFinset (n : Nat)
    [Fintype (oddPrismInternalGraph n).edgeSet] :
    (oddPrismInternalGraph n).edgeFinset = oddPrismInternalEdges n := by
  ext e
  constructor
  · intro he
    have he' := SimpleGraph.mem_edgeFinset.mp he
    simp only [oddPrismInternalGraph,
      SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff] at he'
    exact he'.1
  · intro he
    apply SimpleGraph.mem_edgeFinset.mpr
    rw [oddPrismInternalGraph, SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨he, ?_⟩
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he
    exact oddPrismInternalEdge_not_isDiag n q



def oddPrismLowerHalfCenter (n : Nat) :
    {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n // v.z.val <= n} :=
  ⟨⟨⟨n, by omega⟩, ⟨n, by omega⟩, ⟨n, by omega⟩⟩, le_rfl⟩


def oddPrismLowerHalfSurfaceSite (n : Nat)
    (i j : Fin (2 * n + 1)) :
    {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n // v.z.val <= n} :=
  ⟨⟨i, j, ⟨n, by omega⟩⟩, le_rfl⟩



def oddPrismLowerHalfSurfaceSpinMean (beta : Real) (n : Nat) : Real :=
  let K := oddPrismInternalGraph n
  let P : RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Prop :=
    fun v => v.z.val <= n
  expJ (K.comap (Subtype.val : {v // P v} -> _)).edgeFinset
    (fun _ => beta)
    (fun v => beta * oddPrismPlusField n v.1)
    (fun sigma => spin sigma (oddPrismLowerHalfCenter n))

def oddPrismLowerHalfSurfaceSpinMeanAt (beta : Real) (n : Nat)
    (i j : Fin (2 * n + 1)) : Real :=
  let K := oddPrismInternalGraph n
  let P : RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Prop :=
    fun v => v.z.val <= n
  expJ (K.comap (Subtype.val : {v // P v} -> _)).edgeFinset
    (fun _ => beta)
    (fun v => beta * oddPrismPlusField n v.1)
    (fun sigma => spin sigma (oddPrismLowerHalfSurfaceSite n i j))


theorem oddPrismLowerHalfSurfaceSpinMeanAt_le_plus
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (i j : Fin (2 * n + 1)) :
    oddPrismLowerHalfSurfaceSpinMeanAt beta n i j <=
      oddPrismPlusSpinMean beta n (oddPrismLowerHalfSurfaceSite n i j).1 := by
  letI : DecidableRel (oddPrismInternalGraph n).Adj := Classical.decRel _
  let P : RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Prop :=
    fun v => v.z.val <= n
  have hfield : forall v, 0 <= beta * oddPrismPlusField n v := by
    intro v
    exact mul_nonneg hbeta (Nat.cast_nonneg _)
  have h := expJ_spin_induce_le_inhomogeneous (oddPrismInternalGraph n) P
    beta hbeta (fun v => beta * oddPrismPlusField n v) hfield
    (oddPrismLowerHalfSurfaceSite n i j)
  simpa [oddPrismLowerHalfSurfaceSpinMeanAt, oddPrismPlusSpinMean, P,
    oddPrismInternalGraph_edgeFinset] using h



theorem oddPrismLowerHalfSurfaceSpinMean_le_plus
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) :
    oddPrismLowerHalfSurfaceSpinMean beta n <=
      oddPrismPlusSpinMean beta n (oddPrismLowerHalfCenter n).1 := by
  letI : DecidableRel (oddPrismInternalGraph n).Adj := Classical.decRel _
  let P : RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Prop :=
    fun v => v.z.val <= n
  have hfield : forall v,
      0 <= beta * oddPrismPlusField n v := by
    intro v
    exact mul_nonneg hbeta (Nat.cast_nonneg _)
  have h := expJ_spin_induce_le_inhomogeneous (oddPrismInternalGraph n) P
    beta hbeta
    (fun v => beta * oddPrismPlusField n v) hfield
    (oddPrismLowerHalfCenter n)
  simpa [oddPrismLowerHalfSurfaceSpinMean, oddPrismPlusSpinMean, P,
    oddPrismInternalGraph_edgeFinset] using h

@[simp] theorem oddPrismLowerHalfCenter_to_origin (n : Nat) :
    (rectangularPrismSiteEquivSctBoxDobrushin n
      (oddPrismLowerHalfCenter n).1).1 = origin 3 := by
  funext i
  fin_cases i <;> simp [oddPrismLowerHalfCenter, origin]



theorem isingCritical_oddPrismPlusCenter_tendsto_zero :
    Tendsto (fun n => oddPrismPlusSpinMean (Ising.betaC 3) n
        (oddPrismLowerHalfCenter n).1) atTop (nhds 0) := by
  have h := plusMeasure_spin_full_tendsto_magnetization
    (d := 3) (Ising.betaC 3) isingBetaC_three_pos.le (origin 3)
  rw [magnetization_three_isingBetaC_eq_zero] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun n => by
    dsimp only
    simpa using (oddPrismPlusSpinMean_eq_plusMeasure_integral
      (Ising.betaC 3) n (oddPrismLowerHalfCenter n).1).symm

theorem oddPrismLowerHalfSurfaceSpinMean_nonneg
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) :
    0 <= oddPrismLowerHalfSurfaceSpinMean beta n := by
  dsimp only [oddPrismLowerHalfSurfaceSpinMean]
  rw [<- spinProd_singleton]
  apply ghsvp_expJ_nonneg
  · exact fun _ _ => hbeta
  · intro v
    exact mul_nonneg hbeta (Nat.cast_nonneg _)



theorem isingCritical_oddPrismLowerHalfSurfaceSpinMean_tendsto_zero :
    Tendsto (oddPrismLowerHalfSurfaceSpinMean (Ising.betaC 3))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n =>
      oddPrismLowerHalfSurfaceSpinMean_nonneg
        (Ising.betaC 3) isingBetaC_three_pos.le n
  · exact Filter.Eventually.of_forall fun n =>
      oddPrismLowerHalfSurfaceSpinMean_le_plus
        (Ising.betaC 3) isingBetaC_three_pos.le n
  · exact isingCritical_oddPrismPlusCenter_tendsto_zero





noncomputable def criticalCenteredSlab (L H : Nat) : Finset (Site 3) :=
  (boxFinset 3 (max L H)).filter fun x =>
    (x 0).natAbs ≤ L ∧ (x 1).natAbs ≤ L ∧ (x 2).natAbs ≤ H

theorem mem_criticalCenteredSlab_iff
    {L H : Nat} {x : Site 3} :
    x ∈ criticalCenteredSlab L H ↔
      (x 0).natAbs ≤ L ∧ (x 1).natAbs ≤ L ∧
        (x 2).natAbs ≤ H := by
  rw [criticalCenteredSlab, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨mem_boxFinset.mpr (fun i => ?_), h⟩
    fin_cases i
    · exact h.1.trans (Nat.le_max_left _ _)
    · exact h.2.1.trans (Nat.le_max_left _ _)
    · exact h.2.2.trans (Nat.le_max_right _ _)



theorem translatedBox_subset_criticalCenteredSlab
    (L H r : Nat) (x : Site 3)
    (hx0 : (x 0).natAbs + r ≤ L)
    (hx1 : (x 1).natAbs + r ≤ L)
    (hx2 : (x 2).natAbs + r ≤ H) :
    (boxFinset 3 r).image (fun y => Multiplicative.ofAdd x • y) ⊆
      criticalCenteredSlab L H := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rw [mem_criticalCenteredSlab_iff]
  have hz' := mem_boxFinset.mp hz
  have hcoord (i : Fin 3) :
      ((Multiplicative.ofAdd x • z) i).natAbs ≤
        (x i).natAbs + r := by
    change (x i + z i).natAbs ≤ (x i).natAbs + r
    exact (Int.natAbs_add_le _ _).trans
      (Nat.add_le_add_left (hz' i) _)
  exact ⟨(hcoord 0).trans hx0, (hcoord 1).trans hx1,
    (hcoord 2).trans hx2⟩


theorem criticalCenteredSlab_spinUp_sub_abs_le_centeredGap
    (L H r : Nat) (x : Site 3)
    (hx0 : (x 0).natAbs + r ≤ L)
    (hx1 : (x 1).natAbs + r ≤ L)
    (hx2 : (x 2).natAbs + r ≤ H)
    (eta zeta : ConfigSpace (Site 3)) :
    |(gvMeasure eta (criticalCenteredSlab L H) (Ising.betaC 3) 0).real
          {omega | omega x = true} -
        (gvMeasure zeta (criticalCenteredSlab L H) (Ising.betaC 3) 0).real
          {omega | omega x = true}| ≤
      (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
          {omega | omega (origin 3) = true} -
        (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
          {omega | omega (origin 3) = true} :=
  gvMeasure_spinUp_sub_abs_le_critical_centeredGap
    (criticalCenteredSlab L H) eta zeta x r
    (translatedBox_subset_criticalCenteredSlab L H r x hx0 hx1 hx2)



theorem isingCritical_centeredSlab_origin_boundaryInfluence_tendsto_zero
    (L H : Nat -> Nat) (eta zeta : Nat -> ConfigSpace (Site 3))
    (hsize : Tendsto (fun n => min (L n) (H n)) atTop atTop) :
    Tendsto (fun n =>
      |(gvMeasure (eta n) (criticalCenteredSlab (L n) (H n))
            (Ising.betaC 3) 0).real
            {omega | omega (origin 3) = true} -
        (gvMeasure (zeta n) (criticalCenteredSlab (L n) (H n))
            (Ising.betaC 3) 0).real
            {omega | omega (origin 3) = true}|) atTop (nhds 0) := by
  let gap : Nat -> Real := fun r =>
    (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
        {omega | omega (origin 3) = true} -
      (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
        {omega | omega (origin 3) = true}
  have hgap : Tendsto gap atTop (nhds 0) := by
    exact isingCritical_centeredBox_spinUp_extremalGap_tendsto_zero
      (origin 3)
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    (Filter.Eventually.of_forall fun n => by
      apply criticalCenteredSlab_spinUp_sub_abs_le_centeredGap
        (L n) (H n) (min (L n) (H n)) (origin 3)
      · simp [origin]
      · simp [origin]
      · simp [origin])
  exact hgap.comp hsize

end

end StatMech.FrontierA
