/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamPinnedFieldAdapter
import Code.FrontierA.GrahamMarkedSiteCorollary










open Finset
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.ConfigSpace StatMech.Ising StatMech.Sharpness
open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem vbg_exp_grahamZeroProb_mul_spin_eq_zero_of_flipInvariant
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V)
    (F : ConfigSpace V -> Real)
    (hF : forall s, F (FieldGhostDict.flipV s) = F s) :
    vbg_exp (grahamZeroProb E J)
      (fun s => F s * spin s m) = 0 := by
  let S := vbg_exp (grahamZeroProb E J) (fun s => F s * spin s m)
  have hweight : forall s : ConfigSpace V,
      grahamZeroProb E J (FieldGhostDict.flipV s) =
        grahamZeroProb E J s := by
    intro s
    unfold grahamZeroProb
    rw [show wJ E J (fun _ => 0) (FieldGhostDict.flipV s) =
        wJ E J (fun _ => 0) s by
      simpa only [Pi.neg_apply, neg_zero] using
        ghsvp_wJ_negField_flip E J (fun _ => 0) s]
  have hneg : S = -S := by
    have hS : S = ∑ s : ConfigSpace V,
        grahamZeroProb E J (FieldGhostDict.flipV s) *
          (F (FieldGhostDict.flipV s) *
            spin (FieldGhostDict.flipV s) m) :=
      (Equiv.sum_comp
        (FieldGhostDict.flipV_involutive (V := V)).toPerm
        (fun s : ConfigSpace V =>
          grahamZeroProb E J s * (F s * spin s m))).symm
    simp_rw [hweight, hF, FieldGhostDict.spin_flipV] at hS
    rw [show (∑ s : ConfigSpace V,
        grahamZeroProb E J s * (F s * -spin s m)) = -S by
      unfold S vbg_exp
      calc
        (∑ s : ConfigSpace V,
            grahamZeroProb E J s * (F s * -spin s m)) =
            ∑ s : ConfigSpace V,
              -(grahamZeroProb E J s * (F s * spin s m)) := by
                apply sum_congr rfl
                intro s _
                ring
        _ = -(∑ s : ConfigSpace V,
              grahamZeroProb E J s * (F s * spin s m)) := by
                simpa using sum_neg_distrib
        _ = _ := rfl] at hS
    exact hS
  dsimp only [S] at hneg
  linarith



theorem vbg_exp_grahamPinnedProb_eq_of_flipInvariant
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V)
    (F : ConfigSpace V -> Real)
    (hF : forall s, F (FieldGhostDict.flipV s) = F s) :
    vbg_exp (grahamPinnedProb E J m) F =
      expJ E J (fun _ => 0) F := by
  rw [vbg_exp_grahamPinnedProb,
    vbg_exp_grahamZeroProb_mul_spin_eq_zero_of_flipInvariant E J m F hF,
    add_zero, vbg_exp_grahamZeroProb_eq_expJ]



theorem grahamAnchor_expJ_eq_zero_of_invariant
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (m : V)
    (F : ConfigSpace V -> Real)
    (hanchor : forall t, F (grahamPinConfig m t) = F t)
    (hflip : forall t, F (FieldGhostDict.flipV t) = F t) :
    expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) F =
      expJ E J (fun _ => 0) F := by
  rw [grahamAnchor_expJ_eq_pinned E J hdiag m F hanchor,
    vbg_exp_grahamPinnedProb_eq_of_flipInvariant E J m F hflip]


theorem grahamAnchor_fourPoint_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m i j k l : V}
    (him : i ≠ m) (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m) :
    expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m)
        (fun t => (spin t i * spin t j) * (spin t k * spin t l)) =
      grahamFourPoint E J i j k l := by
  rw [grahamAnchor_expJ_eq_zero_of_invariant E J hdiag m]
  · exact (grahamFourPoint_eq_expJ E J i j k l).symm
  · intro t
    rw [spin_grahamPinConfig_of_ne m t him,
      spin_grahamPinConfig_of_ne m t hjm,
      spin_grahamPinConfig_of_ne m t hkm,
      spin_grahamPinConfig_of_ne m t hlm]
  · intro t
    simp only [FieldGhostDict.spin_flipV]
    ring


noncomputable def grahamFieldFourPointLHS
    (E : Finset (Sym2 V)) (K : Sym2 V -> Real) (h : V -> Real)
    (i j k l : V) : Real :=
  expJ E K h (fun t => (spin t i * spin t j) * (spin t k * spin t l)) -
    expJ E K h (fun t => spin t i * spin t j) *
      expJ E K h (fun t => spin t k * spin t l) -
    expJ E K h (fun t => spin t i * spin t k) *
      expJ E K h (fun t => spin t j * spin t l) -
    expJ E K h (fun t => spin t i * spin t l) *
      expJ E K h (fun t => spin t j * spin t k)


noncomputable def grahamFieldCovariance
    (E : Finset (Sym2 V)) (K : Sym2 V -> Real) (h : V -> Real)
    (x y : V) : Real :=
  expJ E K h (fun t => spin t x * spin t y) -
    expJ E K h (fun t => spin t x) *
      expJ E K h (fun t => spin t y)


noncomputable def grahamFieldFourPointRHS
    (E : Finset (Sym2 V)) (K : Sym2 V -> Real) (h : V -> Real)
    (i j k l : V) : Real :=
  -2 * expJ E K h (fun t => spin t i) *
      expJ E K h (fun t => spin t j) *
      expJ E K h (fun t => spin t k) *
      expJ E K h (fun t => spin t l) -
    2 * grahamFieldCovariance E K h i k *
      grahamFieldCovariance E K h j k *
      expJ E K h (fun t => spin t k * spin t l) -
    2 * expJ E K h (fun t => spin t i) *
      expJ E K h (fun t => spin t j) *
      grahamFieldCovariance E K h i k *
      grahamFieldCovariance E K h i l



theorem grahamFieldFourPointLHS_anchor_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m i j k l : V}
    (him : i ≠ m) (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m) :
    grahamFieldFourPointLHS E (grahamAnchorCoupling J m)
        (grahamAnchorField E J m) i j k l =
      grahamUrsell4 E J i j k l := by
  unfold grahamFieldFourPointLHS grahamUrsell4
  rw [grahamAnchor_fourPoint_eq E J hdiag him hjm hkm hlm,
    grahamAnchor_twoPoint_eq E J hdiag him hjm,
    grahamAnchor_twoPoint_eq E J hdiag hkm hlm,
    grahamAnchor_twoPoint_eq E J hdiag him hkm,
    grahamAnchor_twoPoint_eq E J hdiag hjm hlm,
    grahamAnchor_twoPoint_eq E J hdiag him hlm,
    grahamAnchor_twoPoint_eq E J hdiag hjm hkm]



theorem grahamFieldFourPointRHS_anchor_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m i j k l : V}
    (him : i ≠ m) (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m) :
    grahamFieldFourPointRHS E (grahamAnchorCoupling J m)
        (grahamAnchorField E J m) i j k l =
      grahamCorrectedRHS E J i j k l m := by
  unfold grahamFieldFourPointRHS grahamFieldCovariance
  rw [grahamAnchor_onePoint_eq E J hdiag him,
    grahamAnchor_onePoint_eq E J hdiag hjm,
    grahamAnchor_onePoint_eq E J hdiag hkm,
    grahamAnchor_onePoint_eq E J hdiag hlm,
    grahamAnchor_twoPoint_eq E J hdiag him hkm,
    grahamAnchor_twoPoint_eq E J hdiag hjm hkm,
    grahamAnchor_twoPoint_eq E J hdiag him hlm,
    grahamAnchor_twoPoint_eq E J hdiag hkm hlm]
  unfold grahamCorrectedRHS grahamLeadingTerm grahamKCorrection
    grahamICorrection grahamBridgeGap
  rw [grahamTwoPoint_comm E J m k, grahamTwoPoint_comm E J m l]
  ring



theorem grahamCorrectedBound_iff_anchorField
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) {m i j k l : V}
    (him : i ≠ m) (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m) :
    grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l m ↔
      grahamFieldFourPointLHS E (grahamAnchorCoupling J m)
          (grahamAnchorField E J m) i j k l <=
        grahamFieldFourPointRHS E (grahamAnchorCoupling J m)
          (grahamAnchorField E J m) i j k l := by
  rw [grahamFieldFourPointLHS_anchor_eq E J hdiag him hjm hkm hlm,
    grahamFieldFourPointRHS_anchor_eq E J hdiag him hjm hkm hlm]



theorem grahamUrsell4_pair_rotate
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (i j k l : V) :
    grahamUrsell4 E J i j k l = grahamUrsell4 E J k l i j := by
  have hfour : grahamFourPoint E J i j k l =
      grahamFourPoint E J k l i j := by
    unfold grahamFourPoint grahamFourSupport
    rw [symmDiff_comm]
  unfold grahamUrsell4
  rw [hfour, grahamTwoPoint_comm E J i j,
    grahamTwoPoint_comm E J k l,
    grahamTwoPoint_comm E J k i,
    grahamTwoPoint_comm E J l j,
    grahamTwoPoint_comm E J k j,
    grahamTwoPoint_comm E J l i]
  ring

theorem grahamUrsell4_swap_last
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (i j k l : V) :
    grahamUrsell4 E J i j k l = grahamUrsell4 E J i j l k := by
  have hfour : grahamFourPoint E J i j k l =
      grahamFourPoint E J i j l k := by
    unfold grahamFourPoint grahamFourSupport grahamPairSupport
    rw [symmDiff_comm ({k} : Finset V) {l}]
  unfold grahamUrsell4
  rw [hfour, grahamTwoPoint_comm E J k l,
    grahamTwoPoint_comm E J i k, grahamTwoPoint_comm E J i l,
    grahamTwoPoint_comm E J j k, grahamTwoPoint_comm E J j l]
  ring

theorem grahamUrsell4_cycle
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (i j k l : V) :
    grahamUrsell4 E J i j k l = grahamUrsell4 E J j k l i := by
  have hfour : grahamFourPoint E J i j k l =
      grahamFourPoint E J j k l i := by
    rw [grahamFourPoint_eq_expJ, grahamFourPoint_eq_expJ]
    congr 1
    funext s
    ring
  unfold grahamUrsell4
  rw [hfour, grahamTwoPoint_comm E J i j,
    grahamTwoPoint_comm E J i k, grahamTwoPoint_comm E J i l,
    grahamTwoPoint_comm E J j k, grahamTwoPoint_comm E J j l,
    grahamTwoPoint_comm E J k l]
  ring



theorem grahamCorrectedBound_aux_eq_first
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : ∀ e, 0 <= J e)
    (i j k l : V) :
    grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l i := by
  have hmarked := grahamMarkedSite_four_point_edgeFinset
    E J hdiag hJ j k l i
  have hsign := grahamCorrectedRHS_le_leading E J
    (fun e he => hJ e) j k l i i
  have hU : grahamUrsell4 E J i j k l =
      grahamUrsell4 E J j k l i := grahamUrsell4_cycle E J i j k l
  have htarget : grahamCorrectedRHS E J i j k l i =
      grahamLeadingTerm E J j k l i i := by
    unfold grahamCorrectedRHS grahamLeadingTerm grahamKCorrection
      grahamICorrection grahamBridgeGap
    simp [grahamTwoPoint_comm E J]
  rw [hU, htarget]
  exact hmarked.trans hsign




theorem grahamCorrectedBound_aux_eq_second
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : ∀ e, 0 <= J e)
    (i j k l : V) :
    grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l j := by
  have hmarked := grahamMarkedSite_four_point_edgeFinset
    E J hdiag hJ k l i j
  rw [← grahamUrsell4_pair_rotate E J i j k l] at hmarked
  have hrhs : grahamCorrectedRHS E J k l i j j =
      grahamCorrectedRHS E J i j k l j := by
    unfold grahamCorrectedRHS grahamLeadingTerm grahamKCorrection
      grahamICorrection grahamBridgeGap
    simp [grahamTwoPoint_comm E J]
    ring
  rwa [hrhs] at hmarked



theorem grahamCorrectedBound_aux_eq_third
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : ∀ e, 0 <= J e)
    (i j k l : V) :
    grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l k := by
  have hmarked := grahamMarkedSite_four_point_edgeFinset
    E J hdiag hJ i j l k
  have hsign := grahamCorrectedRHS_le_leading E J
    (fun e he => hJ e) i j l k k
  have hU : grahamUrsell4 E J i j k l =
      grahamUrsell4 E J i j l k := grahamUrsell4_swap_last E J i j k l
  have htarget : grahamCorrectedRHS E J i j k l k =
      grahamLeadingTerm E J i j l k k := by
    unfold grahamCorrectedRHS grahamLeadingTerm grahamKCorrection
      grahamICorrection grahamBridgeGap
    simp [grahamTwoPoint_comm E J]
  rw [hU, htarget]
  exact hmarked.trans hsign



theorem grahamCorrectedBound_of_aux_mem_marks
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : ∀ e, 0 <= J e)
    (i j k l m : V) (hm : m = i ∨ m = j ∨ m = k ∨ m = l) :
    grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l m := by
  rcases hm with hmi | hmj | hmk | hml
  · subst m
    exact grahamCorrectedBound_aux_eq_first E J hdiag hJ i j k l
  · subst m
    exact grahamCorrectedBound_aux_eq_second E J hdiag hJ i j k l
  · subst m
    exact grahamCorrectedBound_aux_eq_third E J hdiag hJ i j k l
  · subst m
    exact grahamMarkedSite_four_point_edgeFinset E J hdiag hJ i j k l

end StatMech.FrontierA
