/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCriticalDualQuasiInvariant



namespace StatMech.FrontierD

noncomputable section



theorem fkRectOpenEdgeCount_add_dual
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenEdgeCount R omega +
        fkRectOpenEdgeCount R (fkRectDualConfigurationEquiv R omega) =
      Fintype.card R.EdgeIndex := by
  classical
  let e := fkRectEdgeDualEquiv R
  have hdual : fkRectOpenEdgeCount R
        (fkRectDualConfigurationEquiv R omega) =
      (Finset.univ.filter fun a : R.EdgeIndex => omega a = false).card := by
    unfold fkRectOpenEdgeCount
    have hfilter : (Finset.univ.filter fun a : R.EdgeIndex =>
          fkRectDualConfigurationEquiv R omega a = true) =
        Finset.image e
          (Finset.univ.filter fun a : R.EdgeIndex => omega a = false) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]
      constructor
      · intro ha
        refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
        rw [fkRectDualConfigurationEquiv_apply] at ha
        simpa [e] using ha
      · rintro ⟨b, hb, rfl⟩
        change fkRectDualConfigurationEquiv R omega
          (fkRectEdgeToDualEdge R b) = true
        rw [fkRectDualConfigurationEquiv_apply_edgeToDualEdge, hb]
        rfl
    rw [hfilter]
    rw [Finset.card_image_of_injective _ e.injective]
  rw [hdual]
  unfold fkRectOpenEdgeCount
  have hpartition :
      (Finset.univ.filter fun a : R.EdgeIndex => omega a = true) ∪
          (Finset.univ.filter fun a : R.EdgeIndex => omega a = false) =
        Finset.univ := by
    ext a
    cases omega a <;> simp
  have hdisjoint : Disjoint
      (Finset.univ.filter fun a : R.EdgeIndex => omega a = true)
      (Finset.univ.filter fun a : R.EdgeIndex => omega a = false) := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    simp_all
  rw [← Finset.card_union_of_disjoint hdisjoint, hpartition,
    Finset.card_univ]




theorem fkRectMedialLoopCount_add_netIndicators_eq_clusterCounts
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectMedialLoopCount R omega +
        fkRectNetIndicator R omega +
        fkRectNetIndicator R (fkRectDualConfigurationEquiv R omega) =
      fkRectNumClusters R omega +
        fkRectNumClusters R (fkRectDualConfigurationEquiv R omega) := by
  have hp :=
    fkRectEulerHomologyDefect_eq_two_mul_netIndicator_configuration R omega
  have hd :=
    fkRectEulerHomologyDefect_eq_two_mul_netIndicator_configuration R
      (fkRectDualConfigurationEquiv R omega)
  have hedges := fkRectOpenEdgeCount_add_dual R omega
  unfold fkRectEulerHomologyDefect at hp hd
  change 2 * (fkRectNumClusters R
        (fkRectDualConfigurationEquiv R omega) : Int) +
      (fkRectOpenEdgeCount R
        (fkRectDualConfigurationEquiv R omega) : Int) -
      (fkRectMedialLoopCount R
        (fkRectDualConfigurationEquiv R omega) : Int) -
      (R.width * R.height : Nat) =
        2 * (fkRectNetIndicator R
          (fkRectDualConfigurationEquiv R omega) : Int) at hd
  rw [fkRectMedialLoopCount_dual R omega] at hd
  have hedgesInt :
      (fkRectOpenEdgeCount R omega : Int) +
          (fkRectOpenEdgeCount R
            (fkRectDualConfigurationEquiv R omega) : Int) =
        2 * (R.width * R.height : Nat) := by
    rw [show Fintype.card R.EdgeIndex = 2 * R.width * R.height from
      card_fkRectEdgeIndex R] at hedges
    simp only [mul_assoc] at hedges
    exact_mod_cast hedges
  have htwice :
      2 * ((fkRectMedialLoopCount R omega : Int) +
          (fkRectNetIndicator R omega : Int) +
          (fkRectNetIndicator R
            (fkRectDualConfigurationEquiv R omega) : Int)) =
        2 * ((fkRectNumClusters R omega : Int) +
          (fkRectNumClusters R
            (fkRectDualConfigurationEquiv R omega) : Int)) := by
    omega
  exact_mod_cast (Int.eq_of_mul_eq_mul_left (by norm_num : (2 : Int) ≠ 0)
    htwice)



theorem fkRectMedialLoopCount_eq_clusterCounts_or_pred_of_not_hasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (hnoNet : ¬ FKRectHasNet R omega) :
    fkRectMedialLoopCount R omega =
        fkRectNumClusters R omega +
          fkRectNumClusters R (fkRectDualConfigurationEquiv R omega) ∨
      fkRectMedialLoopCount R omega + 1 =
        fkRectNumClusters R omega +
          fkRectNumClusters R (fkRectDualConfigurationEquiv R omega) := by
  have hp : fkRectNetIndicator R omega = 0 :=
    (fkRectNetIndicator_eq_zero_iff R omega).2 hnoNet
  have hdle := fkRectNetIndicator_le_one R
    (fkRectDualConfigurationEquiv R omega)
  have hcount :=
    fkRectMedialLoopCount_add_netIndicators_eq_clusterCounts R omega
  rw [hp, add_zero] at hcount
  interval_cases hdual : fkRectNetIndicator R
      (fkRectDualConfigurationEquiv R omega) <;> omega

end

end StatMech.FrontierD
