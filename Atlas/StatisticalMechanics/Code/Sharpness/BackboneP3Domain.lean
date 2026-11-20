/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Sharpness.BackboneSelectorCompatible

open SimpleGraph Finset

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]









def shb_P3DomainResummation
    (H G : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (β : ℝ) (J : Sym2 V → ℝ) {x y : V}
    (p : H.Path x y) : Prop :=
  shb_backboneNumSupport G β J x y (shb_pathMapLe hHG p) *
      currentSum H β J ∅ ≤
    shb_backboneNumSupport H β J x y p * currentSum G β J ∅



theorem shb_P3_support_of_domainResummation
    (H G : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (β : ℝ) (J : Sym2 V → ℝ) {x y : V}
    (p : H.Path x y)
    (hresum : shb_P3DomainResummation H G hHG β J p) :
    shb_rhoSupport G β J x y (shb_pathMapLe hHG p) ≤
      shb_rhoSupport H β J x y p := by
  have hZH : 0 < currentSum H β J ∅ :=
    StatMech.Ising.acr_currentSum_empty_pos H β J
  have hZG : 0 < currentSum G β J ∅ :=
    StatMech.Ising.acr_currentSum_empty_pos G β J
  unfold shb_P3DomainResummation at hresum
  unfold shb_rhoSupport
  exact (div_le_div_iff₀ hZG hZH).2 hresum



theorem shb_P3DomainResummation_of_support
    (H G : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (β : ℝ) (J : Sym2 V → ℝ) {x y : V}
    (p : H.Path x y)
    (hP3 : shb_rhoSupport G β J x y (shb_pathMapLe hHG p) ≤
      shb_rhoSupport H β J x y p) :
    shb_P3DomainResummation H G hHG β J p := by
  have hZH : 0 < currentSum H β J ∅ :=
    StatMech.Ising.acr_currentSum_empty_pos H β J
  have hZG : 0 < currentSum G β J ∅ :=
    StatMech.Ising.acr_currentSum_empty_pos G β J
  unfold shb_rhoSupport at hP3
  unfold shb_P3DomainResummation
  exact (div_le_div_iff₀ hZG hZH).1 hP3




theorem shb_P3_support_iff_domainResummation
    (H G : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (β : ℝ) (J : Sym2 V → ℝ) {x y : V}
    (p : H.Path x y) :
    shb_rhoSupport G β J x y (shb_pathMapLe hHG p) ≤
        shb_rhoSupport H β J x y p ↔
      shb_P3DomainResummation H G hHG β J p := by
  constructor
  · exact shb_P3DomainResummation_of_support H G hHG β J p
  · exact shb_P3_support_of_domainResummation H G hHG β J p










theorem shb_backboneNumSupport_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (x y : V) (p : G.Path x y) :
    0 ≤ shb_backboneNumSupport G β J x y p := by
  unfold shb_backboneNumSupport
  refine tsum_nonneg (fun m => ?_)
  split
  · exact shb_weight_nonneg G β J hβ hJ _
  · exact le_rfl







theorem shb_P3_support_of_fiber_partition_bounds
    (H G : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) {x y : V}
    (p : H.Path x y) (c : ℝ)
    (hfiber : shb_backboneNumSupport G β J x y (shb_pathMapLe hHG p) ≤
      c * shb_backboneNumSupport H β J x y p)
    (hpartition : c * currentSum H β J ∅ ≤ currentSum G β J ∅) :
    shb_rhoSupport G β J x y (shb_pathMapLe hHG p) ≤
      shb_rhoSupport H β J x y p := by
  apply shb_P3_support_of_domainResummation H G hHG β J p
  unfold shb_P3DomainResummation
  have hZH : 0 ≤ currentSum H β J ∅ :=
    le_of_lt (StatMech.Ising.acr_currentSum_empty_pos H β J)
  have hnumH : 0 ≤ shb_backboneNumSupport H β J x y p :=
    shb_backboneNumSupport_nonneg H β J hβ hJ x y p
  calc
    shb_backboneNumSupport G β J x y (shb_pathMapLe hHG p) *
          currentSum H β J ∅
        ≤ (c * shb_backboneNumSupport H β J x y p) *
            currentSum H β J ∅ :=
      mul_le_mul_of_nonneg_right hfiber hZH
    _ = shb_backboneNumSupport H β J x y p *
          (c * currentSum H β J ∅) := by ring
    _ ≤ shb_backboneNumSupport H β J x y p * currentSum G β J ∅ :=
      mul_le_mul_of_nonneg_left hpartition hnumH

end StatMech.Sharpness
