/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Sharpness.BackboneP2Quantitative
import Code.Ising.CorrelationRatio

open SimpleGraph Finset

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]



@[reducible] noncomputable def shb_supportPathOrder (G : SimpleGraph V) (x y : V) :
    LinearOrder (G.Path x y) :=
  LinearOrder.lift' (fun p => p.1.support) (by
    intro p q h
    apply Subtype.ext
    exact SimpleGraph.Walk.support_injective h)



noncomputable def shb_backboneSelectSupport
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : Current V) (x y : V) : Option (G.Path x y) := by
  letI := shb_supportPathOrder G x y
  exact if h : (shb_backboneSet G n x y).Nonempty then
    some ((shb_backboneSet G n x y).min' h) else none



theorem shb_supportPathOrder_mapLe_iff
    {H G : SimpleGraph V} (hHG : H ≤ G) {x y : V}
    (p q : H.Path x y) :
    (p.1.mapLe hHG).support < (q.1.mapLe hHG).support ↔
      p.1.support < q.1.support := by
  simp only [SimpleGraph.Walk.support_mapLe_eq_support]


def shb_pathMapLe {H G : SimpleGraph V} (hHG : H ≤ G) {x y : V} :
    H.Path x y → G.Path x y := fun p =>
  ⟨p.1.mapLe hHG, p.2.mapLe hHG⟩

theorem shb_pathMapLe_injective {H G : SimpleGraph V} (hHG : H ≤ G)
    {x y : V} : Function.Injective (shb_pathMapLe hHG : H.Path x y → G.Path x y) := by
  intro p q hpq
  apply Subtype.ext
  apply SimpleGraph.Walk.support_injective
  have hs := congrArg (fun r : G.Path x y => r.1.support) hpq
  simpa only [shb_pathMapLe, SimpleGraph.Walk.support_mapLe_eq_support] using hs



def shb_CurrentSupportedOn (H : SimpleGraph V) (n : Current V) : Prop :=
  ∀ e, n e ≠ 0 → e ∈ H.edgeSet



noncomputable def shb_restrictBackbonePath
    {H G : SimpleGraph V} [DecidableRel G.Adj]
    (hHG : H ≤ G) (n : Current V) (hSupp : shb_CurrentSupportedOn H n)
    {x y : V} (p : G.Path x y) (hp : shb_IsBackboneOf G n x y p) :
    H.Path x y := by
  have he : ∀ e ∈ p.1.edges, e ∈ H.edgeSet := by
    intro e he
    exact hSupp e (Nat.ne_of_gt (hp e he).pos)
  exact ⟨p.1.transfer H he, p.2.transfer he⟩


theorem shb_mapLe_restrictBackbonePath
    {H G : SimpleGraph V} [DecidableRel G.Adj]
    (hHG : H ≤ G) (n : Current V) (hSupp : shb_CurrentSupportedOn H n)
    {x y : V} (p : G.Path x y) (hp : shb_IsBackboneOf G n x y p) :
    (⟨(shb_restrictBackbonePath hHG n hSupp p hp).1.mapLe hHG,
        (shb_restrictBackbonePath hHG n hSupp p hp).2.mapLe hHG⟩ :
      G.Path x y) = p := by
  apply Subtype.ext
  apply SimpleGraph.Walk.support_injective
  rw [SimpleGraph.Walk.support_mapLe_eq_support]
  exact SimpleGraph.Walk.support_transfer _ _


theorem shb_restrictBackbonePath_isBackbone
    {H G : SimpleGraph V} [DecidableRel G.Adj]
    (hHG : H ≤ G) (n : Current V) (hSupp : shb_CurrentSupportedOn H n)
    {x y : V} (p : G.Path x y) (hp : shb_IsBackboneOf G n x y p) :
    shb_IsBackboneOf H n x y (shb_restrictBackbonePath hHG n hSupp p hp) := by
  intro e he
  apply hp e
  simpa [shb_restrictBackbonePath, SimpleGraph.Walk.edges_transfer] using he



theorem shb_mapLe_isBackboneOf
    {H G : SimpleGraph V} (hHG : H ≤ G) (n : Current V) {x y : V}
    (p : H.Path x y) (hp : shb_IsBackboneOf H n x y p) :
    shb_IsBackboneOf G n x y
      ⟨p.1.mapLe hHG, p.2.mapLe hHG⟩ := by
  intro e he
  apply hp e
  simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he



theorem shb_backboneSet_nonempty_iff_of_supported
    {H G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (n : Current V) (hSupp : shb_CurrentSupportedOn H n)
    (x y : V) :
    (shb_backboneSet H n x y).Nonempty ↔
      (shb_backboneSet G n x y).Nonempty := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨shb_pathMapLe hHG p, ?_⟩
    rw [shb_mem_backboneSet] at hp ⊢
    exact shb_mapLe_isBackboneOf hHG n p hp
  · rintro ⟨p, hp⟩
    rw [shb_mem_backboneSet] at hp
    refine ⟨shb_restrictBackbonePath hHG n hSupp p hp, ?_⟩
    rw [shb_mem_backboneSet]
    exact shb_restrictBackbonePath_isBackbone hHG n hSupp p hp




theorem shb_backboneSelectSupport_mapLe
    {H G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (n : Current V) (hSupp : shb_CurrentSupportedOn H n)
    (x y : V) :
    Option.map (shb_pathMapLe hHG) (shb_backboneSelectSupport H n x y) =
      shb_backboneSelectSupport G n x y := by
  letI : LinearOrder (H.Path x y) := shb_supportPathOrder H x y
  letI : LinearOrder (G.Path x y) := shb_supportPathOrder G x y
  have hne := shb_backboneSet_nonempty_iff_of_supported hHG n hSupp x y
  unfold shb_backboneSelectSupport
  by_cases hH : (shb_backboneSet H n x y).Nonempty
  · have hG : (shb_backboneSet G n x y).Nonempty := hne.mp hH
    rw [dif_pos hH, dif_pos hG, Option.map_some]
    apply congrArg some
    let pH := (shb_backboneSet H n x y).min' hH
    let pG := (shb_backboneSet G n x y).min' hG
    have hpH : pH ∈ shb_backboneSet H n x y := Finset.min'_mem _ _
    have hpG : pG ∈ shb_backboneSet G n x y := Finset.min'_mem _ _
    have hmapH : shb_pathMapLe hHG pH ∈ shb_backboneSet G n x y := by
      rw [shb_mem_backboneSet] at hpH ⊢
      exact shb_mapLe_isBackboneOf hHG n pH hpH
    have hpGback : shb_IsBackboneOf G n x y pG :=
      (shb_mem_backboneSet G n x y pG).mp hpG
    let qH := shb_restrictBackbonePath hHG n hSupp pG hpGback
    have hqH : qH ∈ shb_backboneSet H n x y := by
      rw [shb_mem_backboneSet]
      exact shb_restrictBackbonePath_isBackbone hHG n hSupp pG hpGback
    have hminG : pG ≤ shb_pathMapLe hHG pH :=
      Finset.min'_le _ _ hmapH
    have hminH : pH ≤ qH := Finset.min'_le _ _ hqH
    have hmapq : shb_pathMapLe hHG qH = pG := by
      exact shb_mapLe_restrictBackbonePath hHG n hSupp pG hpGback
    have hmapMinH : shb_pathMapLe hHG pH ≤ shb_pathMapLe hHG qH := by
      change (pH.1.mapLe hHG).support ≤ (qH.1.mapLe hHG).support
      simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hminH
    exact le_antisymm (hmapMinH.trans_eq hmapq) hminG
  · have hG : ¬ (shb_backboneSet G n x y).Nonempty :=
      fun hg => hH (hne.mpr hg)
    rw [dif_neg hH, dif_neg hG, Option.map_none]



theorem shb_ofEdgeFun_supportedOn
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (m : H.edgeFinset → ℕ) :
    shb_CurrentSupportedOn H (ofEdgeFun H m) := by
  intro e he
  unfold ofEdgeFun at he
  split at he
  · rename_i hmem
    simpa [SimpleGraph.edgeFinset] using hmem
  · simp at he



theorem shb_backboneSelectSupport_ofEdgeFun_mapLe
    {H G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (m : H.edgeFinset → ℕ) (x y : V) :
    Option.map (shb_pathMapLe hHG)
        (shb_backboneSelectSupport H (ofEdgeFun H m) x y) =
      shb_backboneSelectSupport G (ofEdgeFun H m) x y :=
  shb_backboneSelectSupport_mapLe hHG (ofEdgeFun H m)
    (shb_ofEdgeFun_supportedOn H m) x y



theorem shb_backboneSelectSupport_ofEdgeFun_eq_some_mapLe_iff
    {H G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (m : H.edgeFinset → ℕ) {x y : V}
    (p : H.Path x y) :
    shb_backboneSelectSupport G (ofEdgeFun H m) x y =
        some (shb_pathMapLe hHG p) ↔
      shb_backboneSelectSupport H (ofEdgeFun H m) x y = some p := by
  have hcompat := shb_backboneSelectSupport_ofEdgeFun_mapLe hHG m x y
  rw [← hcompat]
  constructor
  · intro h
    obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp h
    have : q = p := shb_pathMapLe_injective hHG heq
    simpa [this] using hq
  · intro h
    simp [h]




noncomputable def shb_backboneNumSupport
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (x y : V) (p : G.Path x y) : ℝ :=
  ∑' m : G.edgeFinset → ℕ,
    if sources G (ofEdgeFun G m) = {x, y} ∧
        shb_backboneSelectSupport G (ofEdgeFun G m) x y = some p then
      weight G β J (ofEdgeFun G m) else 0


noncomputable def shb_rhoSupport
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (x y : V) (p : G.Path x y) : ℝ :=
  shb_backboneNumSupport G β J x y p / currentSum G β J ∅


theorem shb_support_indicator_eq_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {x y : V} (hxy : x ≠ y)
    (m : G.edgeFinset → ℕ) :
    (if sources G (ofEdgeFun G m) = {x, y} then
        weight G β J (ofEdgeFun G m) else 0) =
      ∑ p : G.Path x y,
        if sources G (ofEdgeFun G m) = {x, y} ∧
            shb_backboneSelectSupport G (ofEdgeFun G m) x y = some p then
          weight G β J (ofEdgeFun G m) else 0 := by
  let n := ofEdgeFun G m
  by_cases hs : sources G n = {x, y}
  · rw [if_pos hs]
    have hne : (shb_backboneSet G n x y).Nonempty :=
      shb_backboneSet_nonempty_of_sources G n hxy hs
    have hsel : shb_backboneSelectSupport G n x y =
        some ((@Finset.min' _ (shb_supportPathOrder G x y)
          (shb_backboneSet G n x y) hne)) := by
      unfold shb_backboneSelectSupport
      rw [dif_pos hne]
    letI : LinearOrder (G.Path x y) := shb_supportPathOrder G x y
    let p := (shb_backboneSet G n x y).min' hne
    rw [Finset.sum_eq_single p]
    · rw [if_pos ⟨hs, by simpa [p] using hsel⟩]
    · intro q _ hqp
      rw [if_neg]
      rintro ⟨_, hq⟩
      have : q = p := by
        apply Option.some.inj
        exact hq.symm.trans (by simpa [p] using hsel)
      exact hqp this
    · intro hp
      exact absurd (Finset.mem_univ p) hp
  · rw [if_neg hs]
    symm
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg]
    exact fun h => hs h.1


theorem shb_currentSum_eq_sum_backboneNumSupport
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) {x y : V} (hxy : x ≠ y) :
    currentSum G β J {x, y} =
      ∑ p : G.Path x y, shb_backboneNumSupport G β J x y p := by
  unfold currentSum shb_backboneNumSupport
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset (G.Path x y)))
    (f := fun p (m : G.edgeFinset → ℕ) =>
      if sources G (ofEdgeFun G m) = {x, y} ∧
          shb_backboneSelectSupport G (ofEdgeFun G m) x y = some p then
        weight G β J (ofEdgeFun G m) else 0)
    (fun p _ => shb_summable_indicator G β J hβ hJ _)]
  exact tsum_congr (fun m => shb_support_indicator_eq_sum G β J hxy m)


theorem shb_P1_support
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) {x y : V} (hxy : x ≠ y) :
    expectationJ G β J {x, y} =
      ∑ p : G.Path x y, shb_rhoSupport G β J x y p := by
  rw [current_representation,
    shb_currentSum_eq_sum_backboneNumSupport G β J hβ hJ hxy]
  unfold shb_rhoSupport
  rw [Finset.sum_div]






def shb_P2ComplementResummation
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {x z u : V}
    (p₁₂ : G.Path x z) (p₁ : G.Path x u) (p₂ : H.Path u z) : Prop :=
  shb_backboneNumSupport G β J x z p₁₂ * currentSum H β J ∅ =
    shb_backboneNumSupport G β J x u p₁ *
      shb_backboneNumSupport H β J u z p₂



theorem shb_P2_support_of_complementResummation
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {x z u : V}
    (p₁₂ : G.Path x z) (p₁ : G.Path x u) (p₂ : H.Path u z)
    (hresum : shb_P2ComplementResummation G H β J p₁₂ p₁ p₂) :
    shb_rhoSupport G β J x z p₁₂ =
      shb_rhoSupport G β J x u p₁ * shb_rhoSupport H β J u z p₂ := by
  have hZG : currentSum G β J ∅ ≠ 0 :=
    ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos G β J)
  have hZH : currentSum H β J ∅ ≠ 0 :=
    ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos H β J)
  unfold shb_P2ComplementResummation at hresum
  unfold shb_rhoSupport
  field_simp [hZG, hZH]
  exact hresum

end StatMech.Sharpness
