/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Sharpness.DeltaBound
import Code.Sharpness.FieldGhostDict
import Code.Sharpness.GhostCurrentRep
import Code.Sharpness.WeightedFieldGhost
import Code.Ising.FiniteVolumeDomain

open Finset SimpleGraph
open scoped BigOperators symmDiff

namespace StatMech
namespace Sharpness

open FluxEdgeCopy
open FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



noncomputable def isingCutMass (beta : ℝ) (J : Sym2 V → ℝ)
    (g : V) (S : Finset V) : ℝ :=
  (currentSum G beta J ∅)⁻¹ ^ 2 *
    gatedSourcePairSum G beta J ∅ ∅
      (fun m => notConnComp G m g = S)



theorem sum_cutMassNumerator_eq_sourcePairDisconn (beta : ℝ)
    (J : Sym2 V → ℝ) (o g : V) :
    (∑ S : Finset V,
      if o ∈ S then
        gatedSourcePairSum G beta J ∅ ∅
          (fun m => notConnComp G m g = S)
      else 0) =
      sourcePairDisconnSum G beta J ∅ ∅ o g := by
  classical
  let P : Current V → Prop := fun m => ¬ CurrentConnected G m o g
  let f : Current V → Finset V := fun m => notConnComp G m g
  have hterm (S : Finset V) :
      (if o ∈ S then gatedSourcePairSum G beta J ∅ ∅ (fun m => f m = S) else 0) =
        gatedSourcePairSum G beta J ∅ ∅ (fun m => f m = S ∧ P m) := by
    by_cases hoS : o ∈ S
    · rw [if_pos hoS]
      apply gatedSourcePairSum_congr_sources
      intro p q _ _
      let m := ofEdgeFun G (fun e => p e + q e)
      constructor
      · intro hm
        refine ⟨hm, ?_⟩
        have hmem : o ∈ f m := by rw [hm]; exact hoS
        have hnot : ¬ CurrentConnected G m g o :=
          (mem_notConnComp G).mp hmem
        exact fun hconn => hnot hconn.symm
      · exact fun hm => hm.1
    · rw [if_neg hoS]
      have hc := gatedSourcePairSum_congr_sources G beta J ∅ ∅
        (fun m => f m = S ∧ P m) (fun _ => False) (fun p q _ _ => by
          let m := ofEdgeFun G (fun e => p e + q e)
          constructor
          · rintro ⟨hm, hP⟩
            have hnot : ¬ CurrentConnected G m g o :=
              fun hconn => hP hconn.symm
            have hmem : o ∈ f m := (mem_notConnComp G).mpr hnot
            apply hoS
            rw [← hm]
            exact hmem
          · simp)
      rw [hc]
      simp [gatedSourcePairSum]
  calc
    (∑ S : Finset V,
        if o ∈ S then
          gatedSourcePairSum G beta J ∅ ∅
            (fun m => notConnComp G m g = S)
        else 0) =
        ∑ S : Finset V,
          gatedSourcePairSum G beta J ∅ ∅
            (fun m => f m = S ∧ P m) := by
      apply Finset.sum_congr rfl
      intro S _
      simpa [f] using hterm S
    _ = gatedSourcePairSum G beta J ∅ ∅ P :=
      (gatedSourcePairSum_partition G beta J ∅ ∅ P f).symm
    _ = sourcePairDisconnSum G beta J ∅ ∅ o g := by
      unfold gatedSourcePairSum sourcePairDisconnSum P
      apply tsum_congr
      rintro ⟨p, q⟩
      rfl





theorem sum_isingCutMass_eq_one_sub_sq (beta : ℝ) (J : Sym2 V → ℝ)
    {o g : V} (hog : o ≠ g) :
    (∑ S : Finset V, if o ∈ S then isingCutMass G beta J g S else 0) =
      1 - (expectationJ G beta J {o, g}) ^ 2 := by
  classical
  let Z := currentSum G beta J ∅
  let C := currentSum G beta J {o, g}
  have hZ : Z ≠ 0 := ne_of_gt (Ising.acr_currentSum_empty_pos G beta J)
  have hnum := sum_cutMassNumerator_eq_sourcePairDisconn G beta J o g
  have hgap := GhostCurrentRep.gcr_currentSum_ghostRep G beta J ∅ hog
  have hsd : (∅ : Finset V) ∆ {o, g} = {o, g} := by simp
  rw [hsd] at hgap
  rw [current_representation]
  unfold isingCutMass
  have hfactor :
      (∑ S : Finset V,
        if o ∈ S then
          (currentSum G beta J ∅)⁻¹ ^ 2 *
            gatedSourcePairSum G beta J ∅ ∅
              (fun m => notConnComp G m g = S)
        else 0) =
        (currentSum G beta J ∅)⁻¹ ^ 2 *
          ∑ S : Finset V,
            if o ∈ S then
              gatedSourcePairSum G beta J ∅ ∅
                (fun m => notConnComp G m g = S)
            else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    split <;> simp_all
  rw [hfactor]
  rw [hnum, ← hgap]
  dsimp [Z, C] at hZ ⊢
  field_simp



theorem isingCutMass_eq_zero_of_mem_root (beta : ℝ) (J : Sym2 V → ℝ)
    (g : V) (S : Finset V) (hg : g ∈ S) :
    isingCutMass G beta J g S = 0 := by
  unfold isingCutMass
  apply mul_eq_zero_of_right
  unfold gatedSourcePairSum
  refine (tsum_congr (fun pq => ?_)).trans tsum_zero
  rcases pq with ⟨p, q⟩
  let m := ofEdgeFun G (fun e => p e + q e)
  have hne : notConnComp G m g ≠ S := by
    intro heq
    have hmem : g ∈ notConnComp G m g := by rw [heq]; exact hg
    exact (mem_notConnComp G).mp hmem (CurrentConnected.refl G m g)
  simp [m, hne]


theorem isingCutMass_nonneg (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (g : V) (S : Finset V) :
    0 ≤ isingCutMass G beta J g S := by
  unfold isingCutMass
  apply mul_nonneg (sq_nonneg _)
  unfold gatedSourcePairSum
  apply tsum_nonneg
  rintro ⟨p, q⟩
  by_cases hp : sources G (ofEdgeFun G p) = ∅ <;>
    by_cases hq : sources G (ofEdgeFun G q) = ∅ <;>
    by_cases hS : notConnComp G (ofEdgeFun G (fun e => p e + q e)) g = S <;>
    simp [hp, hq, hS]
  exact mul_nonneg
    (Ising.acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G p))
    (Ising.acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G q))




theorem sum_localCorr_mul_cutMassNumerator_eq_sourcePairDisconn
    (beta : ℝ) (J : Sym2 V → ℝ) {o x g : V}
    (hox : o ≠ x) :
    (∑ S : Finset V,
      if o ∈ S ∧ x ∈ S ∧ g ∉ S then
        expectationJ G beta (couplingIn J S) {o, x} *
          gatedSourcePairSum G beta J ∅ ∅
            (fun m => notConnComp G m g = S)
      else 0) =
      sourcePairDisconnSum G beta J {o, x} ∅ o g := by
  classical
  let P : Current V → Prop := fun m => ¬ CurrentConnected G m o g
  let f : Current V → Finset V := fun m => notConnComp G m g
  have hterm (S : Finset V) :
      (if o ∈ S ∧ x ∈ S ∧ g ∉ S then
          expectationJ G beta (couplingIn J S) {o, x} *
            gatedSourcePairSum G beta J ∅ ∅ (fun m => f m = S)
        else 0) =
        gatedSourcePairSum G beta J {o, x} ∅ (fun m => f m = S ∧ P m) := by
    by_cases hgood : o ∈ S ∧ x ∈ S ∧ g ∉ S
    · rw [if_pos hgood]
      change
        expectationJ G beta (couplingIn J S) {o, x} *
            gatedSourcePairSum G beta J ∅ ∅
              (fun m => notConnComp G m g = S) = _
      rw [← claim2_ising_gated G beta J S g o x hgood.2.2 hgood.1 hgood.2.1]
      apply gatedSourcePairSum_congr_sources
      intro p q hp hq
      let m := ofEdgeFun G (fun e => p e + q e)
      constructor
      · intro hm
        refine ⟨hm, ?_⟩
        have hmem : o ∈ f m := by
          change o ∈ notConnComp G m g
          change notConnComp G m g = S at hm
          rw [hm]
          exact hgood.1
        have hnot : ¬ CurrentConnected G m g o :=
          (mem_notConnComp G).mp hmem
        exact fun hconn => hnot hconn.symm
      · exact fun hm => hm.1
    · rw [if_neg hgood]
      have hc := gatedSourcePairSum_congr_sources G beta J {o, x} ∅
        (fun m => f m = S ∧ P m) (fun _ => False) (fun p q hp hq => by
          let m := ofEdgeFun G (fun e => p e + q e)
          have hsrc : sources G m = {o, x} := by
            dsimp [m]
            rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
            simp
          have hconnOX : CurrentConnected G m o x :=
            currentConnected_of_sources_pair G (fun e => p e + q e) hox hsrc
          constructor
          · rintro ⟨hm, hP⟩
            have hnotO : ¬ CurrentConnected G m g o :=
              fun hconn => hP hconn.symm
            have ho : o ∈ f m := (mem_notConnComp G).mpr hnotO
            have hnotX : ¬ CurrentConnected G m g x := fun hgx =>
              hnotO (CurrentConnected.trans G hgx hconnOX.symm)
            have hx : x ∈ f m := (mem_notConnComp G).mpr hnotX
            have hg : g ∉ f m := fun hgmem =>
              (mem_notConnComp G).mp hgmem (CurrentConnected.refl G m g)
            apply hgood
            constructor
            · rw [← hm]; exact ho
            constructor
            · rw [← hm]; exact hx
            · rw [← hm]; exact hg
          · simp)
      rw [hc]
      simp [gatedSourcePairSum]
  calc
    (∑ S : Finset V,
        if o ∈ S ∧ x ∈ S ∧ g ∉ S then
          expectationJ G beta (couplingIn J S) {o, x} *
            gatedSourcePairSum G beta J ∅ ∅
              (fun m => notConnComp G m g = S)
        else 0) =
        ∑ S : Finset V,
          gatedSourcePairSum G beta J {o, x} ∅
            (fun m => f m = S ∧ P m) := by
      apply Finset.sum_congr rfl
      intro S _
      simpa [f] using hterm S
    _ = gatedSourcePairSum G beta J {o, x} ∅ P :=
      (gatedSourcePairSum_partition G beta J {o, x} ∅ P f).symm
    _ = sourcePairDisconnSum G beta J {o, x} ∅ o g := by
      unfold gatedSourcePairSum sourcePairDisconnSum P
      apply tsum_congr
      rintro ⟨p, q⟩
      rfl





theorem sum_localCorr_mul_isingCutMass_eq_covariance
    (beta : ℝ) (J : Sym2 V → ℝ) {o x g : V}
    (hox : o ≠ x) (hog : o ≠ g) (hxg : x ≠ g) :
    (∑ S : Finset V,
      if o ∈ S ∧ x ∈ S ∧ g ∉ S then
        expectationJ G beta (couplingIn J S) {o, x} *
          isingCutMass G beta J g S
      else 0) =
      expectationJ G beta J {o, x} -
        expectationJ G beta J {o, g} * expectationJ G beta J {x, g} := by
  classical
  let Z := currentSum G beta J ∅
  have hZ : Z ≠ 0 := ne_of_gt (Ising.acr_currentSum_empty_pos G beta J)
  have hnum :=
    sum_localCorr_mul_cutMassNumerator_eq_sourcePairDisconn G beta J
      (g := g) hox
  have hgap := GhostCurrentRep.gcr_currentSum_ghostRep G beta J {o, x} hog
  have hsd : ({o, x} : Finset V) ∆ {o, g} = {x, g} := by
    ext z
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [hsd] at hgap
  unfold isingCutMass
  have hfactor :
      (∑ S : Finset V,
        if o ∈ S ∧ x ∈ S ∧ g ∉ S then
          expectationJ G beta (couplingIn J S) {o, x} *
            ((currentSum G beta J ∅)⁻¹ ^ 2 *
              gatedSourcePairSum G beta J ∅ ∅
                (fun m => notConnComp G m g = S))
        else 0) =
        (currentSum G beta J ∅)⁻¹ ^ 2 *
          ∑ S : Finset V,
            if o ∈ S ∧ x ∈ S ∧ g ∉ S then
              expectationJ G beta (couplingIn J S) {o, x} *
                gatedSourcePairSum G beta J ∅ ∅
                  (fun m => notConnComp G m g = S)
            else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    split
    · ring
    · simp_all
  rw [hfactor, hnum, ← hgap]
  simp_rw [current_representation]
  dsimp [Z] at hZ ⊢
  field_simp





theorem sum_localCorr_mul_fieldGhostCutMass_eq_covariance
    (beta h : ℝ) {o x : V} (hox : o ≠ x) :
    (∑ S : Finset (Option V),
      if some o ∈ S ∧ some x ∈ S ∧ none ∉ S then
        expectationJ (withGhost G) beta
            (couplingIn (ghostCoupling h beta (fun _ => 1)) S)
            {some o, some x} *
          isingCutMass (withGhost G) beta
            (ghostCoupling h beta (fun _ => 1)) none S
      else 0) =
      Ising.isingExpectation G beta h (Ising.spinProd {o, x}) -
        Ising.isingExpectation G beta h (Ising.spinProd {o}) *
          Ising.isingExpectation G beta h (Ising.spinProd {x}) := by
  classical
  have hmain := sum_localCorr_mul_isingCutMass_eq_covariance
    (withGhost G) beta (ghostCoupling h beta (fun _ => 1))
    (o := some o) (x := some x) (g := none)
    (by simpa using hox) (by simp) (by simp)
  have heven : Even (({o, x} : Finset V).card) := by
    rw [Finset.card_insert_of_notMem (by simp [hox]), Finset.card_singleton]
    decide
  have hoddO : Odd (({o} : Finset V).card) := by simp
  have hoddX : Odd (({x} : Finset V).card) := by simp
  have hpair := fgd_expectationJ_ghost_eq G beta h ({o, x} : Finset V) heven
  have hone := fgd_expectationJ_ghost_eq_odd G beta h ({o} : Finset V) hoddO
  have hxone := fgd_expectationJ_ghost_eq_odd G beta h ({x} : Finset V) hoddX
  have hmapPair : ({o, x} : Finset V).map someEmb = {some o, some x} := by simp
  have hmapO : insert none (({o} : Finset V).map someEmb) = {some o, none} := by
    ext z
    simp [someEmb]
    tauto
  have hmapX : insert none (({x} : Finset V).map someEmb) = {some x, none} := by
    ext z
    simp [someEmb]
    tauto
  rw [hmapPair] at hpair
  rw [hmapO] at hone
  rw [hmapX] at hxone
  rw [hpair, hone, hxone] at hmain
  simpa [Finset.pair_comm] using hmain



theorem weightedExpectation_zero_eq_expectationJ
    (beta : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    WeightedFieldGhost.weightedExpectation G beta J 0 (Ising.spinProd A) =
      expectationJ G beta J A := by
  unfold WeightedFieldGhost.weightedExpectation WeightedFieldGhost.weightedZ
    WeightedFieldGhost.weightedWeight WeightedFieldGhost.weightedEnergy
    expectationJ partitionJ boltzmannJ
  simp only [zero_mul, add_zero]



theorem couplingIn_ghostCoupling_map_some (beta h : ℝ)
    (T : Finset V) :
    couplingIn (ghostCoupling h beta (fun _ => 1)) (T.map someEmb) =
      ghostCoupling 0 beta (couplingIn (fun _ => 1) T) := by
  funext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      cases a <;> cases b <;>
        simp [couplingIn, edgeInside, ghostCoupling, someEmb]




theorem localCorr_fieldGhost_map_some (beta h : ℝ) (T : Finset V)
    {o x : V} (hox : o ≠ x) :
    expectationJ (withGhost G) beta
        (couplingIn (ghostCoupling h beta (fun _ => 1)) (T.map someEmb))
        {some o, some x} =
      expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} := by
  classical
  rw [couplingIn_ghostCoupling_map_some beta h T]
  have heven : Even (({o, x} : Finset V).card) := by
    rw [Finset.card_insert_of_notMem (by simp [hox]), Finset.card_singleton]
    decide
  have hratio := WeightedFieldGhost.weightedExpectation_eq_currentRatio_even
    G beta 0 (couplingIn (fun _ => 1) T) ({o, x} : Finset V) heven
  have hmap : ({o, x} : Finset V).map someEmb = {some o, some x} := by simp
  rw [hmap] at hratio
  rw [current_representation, ← hratio,
    weightedExpectation_zero_eq_expectationJ G beta]



noncomputable def ghostFreeFinsetEquiv :
    Finset V ≃ {S : Finset (Option V) // none ∉ S} :=
  Equiv.ofBijective
    (fun T => (⟨T.map someEmb, by simp⟩ :
      {S : Finset (Option V) // none ∉ S}))
    ⟨by
      intro T U h
      apply Finset.map_injective someEmb
      exact Subtype.ext_iff.mp h,
    by
      intro S
      let T := S.1.preimage some (Set.injOn_of_injective someEmb.injective)
      refine ⟨T, Subtype.ext ?_⟩
      ext z
      cases z with
      | none => simp [S.2]
      | some z => simp [T]⟩



theorem sum_baseCutMass_eq_one_sub_mag_sq (beta h : ℝ) (o : V) :
    (∑ T : Finset V, if o ∈ T then
      isingCutMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
      else 0) =
      1 - (Ising.isingExpectation G beta h (Ising.spinProd {o})) ^ 2 := by
  classical
  have hghost := sum_isingCutMass_eq_one_sub_sq
    (withGhost G) beta (ghostCoupling h beta (fun _ => 1))
    (o := some o) (g := none) (by simp)
  let F : Finset (Option V) → ℝ := fun S =>
    if some o ∈ S then
      isingCutMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) none S
    else 0
  have hrestrict :
      (∑ S : Finset (Option V), F S) =
        ∑ S : Finset (Option V), if none ∉ S then F S else 0 := by
    apply Finset.sum_congr rfl
    intro S _
    by_cases hg : none ∉ S
    · rw [if_pos hg]
    · rw [if_neg hg]
      have hgmem : none ∈ S := not_not.mp hg
      by_cases ho : some o ∈ S
      · simp [F, ho, isingCutMass_eq_zero_of_mem_root
          (withGhost G) beta (ghostCoupling h beta (fun _ => 1)) none S hgmem]
      · simp [F, ho]
  have hsubtype :
      (∑ S : Finset (Option V), if none ∉ S then F S else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro S
    simp
  have hreindex :
      (∑ T : Finset V, if o ∈ T then
        isingCutMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
        else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    apply Fintype.sum_equiv ghostFreeFinsetEquiv
    intro T
    simp only [ghostFreeFinsetEquiv, Equiv.ofBijective_apply]
    change
      (if o ∈ T then
        isingCutMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
      else 0) = F (T.map someEmb)
    by_cases ho : o ∈ T <;> simp [F, ho]
  have hdict := fgd_expectationJ_ghost_eq_odd G beta h ({o} : Finset V) (by simp)
  have hsource : insert none (({o} : Finset V).map someEmb) =
      ({some o, none} : Finset (Option V)) := by
    ext z
    cases z <;> simp [someEmb]
  rw [hsource] at hdict
  change (∑ S : Finset (Option V), F S) = _ at hghost
  rw [hreindex, ← hsubtype, ← hrestrict, hghost, hdict]




theorem sum_localCorr_baseCutMass_eq_fieldCovariance
    (beta h : ℝ) {o x : V} (hox : o ≠ x) :
    (∑ T : Finset V,
      if o ∈ T ∧ x ∈ T then
        expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} *
          isingCutMass (withGhost G) beta
            (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
      else 0) =
      Ising.isingExpectation G beta h (Ising.spinProd {o, x}) -
        Ising.isingExpectation G beta h (Ising.spinProd {o}) *
          Ising.isingExpectation G beta h (Ising.spinProd {x}) := by
  classical
  have hghost := sum_localCorr_mul_fieldGhostCutMass_eq_covariance G beta h hox
  let F : Finset (Option V) → ℝ := fun S =>
    if some o ∈ S ∧ some x ∈ S then
      expectationJ (withGhost G) beta
          (couplingIn (ghostCoupling h beta (fun _ => 1)) S)
          {some o, some x} *
        isingCutMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) none S
    else 0
  have hsplit :
      (∑ S : Finset (Option V),
        if some o ∈ S ∧ some x ∈ S ∧ none ∉ S then
          expectationJ (withGhost G) beta
              (couplingIn (ghostCoupling h beta (fun _ => 1)) S)
              {some o, some x} *
            isingCutMass (withGhost G) beta
              (ghostCoupling h beta (fun _ => 1)) none S
        else 0) =
        ∑ S : Finset (Option V), if none ∉ S then F S else 0 := by
    apply Finset.sum_congr rfl
    intro S _
    by_cases hg : none ∉ S <;>
      by_cases ho : some o ∈ S <;>
      by_cases hx : some x ∈ S <;> simp [F, hg, ho, hx]
  have hsubtype :
      (∑ S : Finset (Option V), if none ∉ S then F S else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro S
    simp
  have hreindex :
      (∑ T : Finset V,
        if o ∈ T ∧ x ∈ T then
          expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} *
            isingCutMass (withGhost G) beta
              (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
        else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    apply Fintype.sum_equiv ghostFreeFinsetEquiv
    intro T
    simp only [ghostFreeFinsetEquiv, Equiv.ofBijective_apply]
    change
      (if o ∈ T ∧ x ∈ T then
        expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} *
          isingCutMass (withGhost G) beta
            (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
      else 0) = F (T.map someEmb)
    by_cases ho : o ∈ T <;> by_cases hx : x ∈ T
    · simp [F, ho, hx, localCorr_fieldGhost_map_some G beta h T hox]
    · simp [F, ho, hx]
    · simp [F, ho, hx]
    · simp [F, ho, hx]
  rw [hreindex, ← hsubtype, ← hsplit]
  exact hghost



theorem normalizedDeltaLowerMass_fieldGhost (beta h : ℝ)
    {o x y : V} (hox : o ≠ x) :
    (currentSum (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      isingDeltaLowerMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none =
      ∑ T : Finset V,
        if o ∈ T ∧ x ∈ T ∧ y ∉ T then
          expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} *
            isingCutMass (withGhost G) beta
              (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
        else 0 := by
  classical
  let Z := currentSum (withGhost G) beta
    (ghostCoupling h beta (fun _ => 1)) ∅
  let F : Finset (Option V) → ℝ := fun S =>
    if some o ∈ S ∧ some x ∈ S ∧ some y ∉ S then
      expectationJ (withGhost G) beta
          (couplingIn (ghostCoupling h beta (fun _ => 1)) S)
          {some o, some x} *
        isingCutMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) none S
    else 0
  have hscaled :
      Z⁻¹ ^ 2 * isingDeltaLowerMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none =
        ∑ S : Finset (Option V), if none ∉ S then F S else 0 := by
    unfold isingDeltaLowerMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hoS : some o ∈ S <;> by_cases hxS : some x ∈ S <;>
      by_cases hyS : some y ∉ S <;> by_cases hgS : none ∉ S <;>
      simp [F, isingCutMass, Z, hoS, hxS, hyS, hgS] <;> ring
  have hsubtype :
      (∑ S : Finset (Option V), if none ∉ S then F S else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro S
    simp
  have hreindex :
      (∑ T : Finset V,
        if o ∈ T ∧ x ∈ T ∧ y ∉ T then
          expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} *
            isingCutMass (withGhost G) beta
              (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
        else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    apply Fintype.sum_equiv ghostFreeFinsetEquiv
    intro T
    simp only [ghostFreeFinsetEquiv, Equiv.ofBijective_apply]
    change
      (if o ∈ T ∧ x ∈ T ∧ y ∉ T then
        expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} *
          isingCutMass (withGhost G) beta
            (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
      else 0) = F (T.map someEmb)
    by_cases ho : o ∈ T <;> by_cases hx : x ∈ T <;> by_cases hy : y ∉ T
    · simp [F, ho, hx, hy, localCorr_fieldGhost_map_some G beta h T hox]
    · simp [F, ho, hx, hy]
    · simp [F, ho, hx, hy]
    · simp [F, ho, hx, hy]
    · simp [F, ho, hx, hy]
    · simp [F, ho, hx, hy]
    · simp [F, ho, hx, hy]
    · simp [F, ho, hx, hy]
  rw [hscaled, hsubtype, ← hreindex]



theorem normalizedDeltaSelfLowerMass_fieldGhost (beta h : ℝ) (o y : V) :
    (currentSum (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      isingDeltaSelfLowerMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) (some o) (some y) none =
      ∑ T : Finset V,
        if o ∈ T ∧ y ∉ T then
          isingCutMass (withGhost G) beta
            (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
        else 0 := by
  classical
  let Z := currentSum (withGhost G) beta
    (ghostCoupling h beta (fun _ => 1)) ∅
  let F : Finset (Option V) → ℝ := fun S =>
    if some o ∈ S ∧ some y ∉ S then
      isingCutMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) none S
    else 0
  have hscaled :
      Z⁻¹ ^ 2 * isingDeltaSelfLowerMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) (some o) (some y) none =
        ∑ S : Finset (Option V), if none ∉ S then F S else 0 := by
    unfold isingDeltaSelfLowerMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hoS : some o ∈ S <;> by_cases hyS : some y ∉ S <;>
      by_cases hgS : none ∉ S <;>
      simp [F, isingCutMass, Z, hoS, hyS, hgS] <;> ring
  have hsubtype :
      (∑ S : Finset (Option V), if none ∉ S then F S else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro S
    simp
  have hreindex :
      (∑ T : Finset V,
        if o ∈ T ∧ y ∉ T then
          isingCutMass (withGhost G) beta
            (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
        else 0) =
        ∑ S : {S : Finset (Option V) // none ∉ S}, F S.1 := by
    apply Fintype.sum_equiv ghostFreeFinsetEquiv
    intro T
    simp only [ghostFreeFinsetEquiv, Equiv.ofBijective_apply]
    change
      (if o ∈ T ∧ y ∉ T then
        isingCutMass (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) none (T.map someEmb)
      else 0) = F (T.map someEmb)
    by_cases ho : o ∈ T <;> by_cases hy : y ∉ T <;> simp [F, ho, hy]
  rw [hscaled, hsubtype, ← hreindex]





def localizedGraph (T : Finset V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (↑(edgesIn G T) : Set (Sym2 V))


theorem localizedGraph_edgeFinset (T : Finset V)
    [DecidableRel (localizedGraph G T).Adj] :
    (localizedGraph G T).edgeFinset = edgesIn G T := by
  classical
  apply Finset.coe_injective
  rw [SimpleGraph.coe_edgeFinset]
  unfold localizedGraph
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_diff, Finset.mem_coe, Sym2.mem_diagSet]
  constructor
  · exact fun h => h.1
  · intro he
    exact ⟨he, G.not_isDiag_of_mem_edgeFinset (Finset.mem_filter.mp he).1⟩

set_option maxHeartbeats 1000000 in




theorem expectationJ_couplingIn_one_eq_induced (beta : ℝ) (T : Finset V)
    {o x : V} (ho : o ∈ T) (hx : x ∈ T) :
    expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} =
      Ising.isingExpectation
        (G.comap (Subtype.val : {v // v ∈ T} → V)) beta 0
        (Ising.spinProd {⟨o, ho⟩, ⟨x, hx⟩}) := by
  classical
  let P : V → Prop := fun v => v ∈ T
  let L : SimpleGraph {v // P v} := FK.agl_left G P
  let I : SimpleGraph {v // ¬ P v} := ⊥
  let S : SimpleGraph ({v // P v} ⊕ {v // ¬ P v}) := L ⊕g I
  let K : SimpleGraph V := localizedGraph G T
  let A : Finset {v // P v} := {⟨o, ho⟩, ⟨x, hx⟩}
  let σ : ({v // P v} ⊕ {v // ¬ P v}) ≃ V := FK.agl_sumEquiv P
  letI : DecidableRel L.Adj := Classical.decRel _
  letI : DecidableRel I.Adj := Classical.decRel _
  letI : DecidableRel K.Adj := Classical.decRel _
  have hσ : ∀ a b, S.Adj a b ↔ K.Adj (σ a) (σ b) := by
    intro a b
    rcases a with a | a <;> rcases b with b | b
    · simp [S, L, I, K, localizedGraph, σ, P, FK.agl_sumEquiv,
        SimpleGraph.fromEdgeSet_adj, edgesIn, edgeInside]
      intro hab heq
      exact G.ne_of_adj hab (congrArg Subtype.val heq)
    · simp [S, L, I, K, localizedGraph, σ, P, FK.agl_sumEquiv,
        SimpleGraph.fromEdgeSet_adj, edgesIn, edgeInside]
      exact fun _ hb => (b.property hb).elim
    · simp [S, L, I, K, localizedGraph, σ, P, FK.agl_sumEquiv,
        SimpleGraph.fromEdgeSet_adj, edgesIn, edgeInside]
      exact fun _ ha => (a.property ha).elim
    · simp [S, L, I, K, localizedGraph, σ, P, FK.agl_sumEquiv,
        SimpleGraph.fromEdgeSet_adj, edgesIn, edgeInside]
      exact fun _ ha _ => (a.property ha).elim
  have hmap :
      (A.map ⟨Sum.inl, Sum.inl_injective⟩).map σ.toEmbedding =
        ({o, x} : Finset V) := by
    ext z
    simp [A, σ, P, FK.agl_sumEquiv]
  have hK : K.edgeFinset = edgesIn G T := by
    simpa [K] using localizedGraph_edgeFinset G T
  calc
    expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} =
        expJ (edgesIn G T) (fun _ => beta) (fun _ => 0)
          (Ising.spinProd {o, x}) := by
      simpa using expectationJ_couplingIn_eq_expJ G beta (fun _ => 1) T {o, x}
    _ = Ising.isingExpectation K beta 0 (Ising.spinProd {o, x}) := by
      rw [← hK]
      simpa using (Ising.isingExpectation_spinProd_eq_expJ K beta 0 {o, x}).symm
    _ = Ising.isingExpectation S beta 0
          (Ising.spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩)) := by
      rw [Ising.isingExpectation_spinProd_relabel S K σ hσ beta 0,
        hmap]
    _ = Ising.isingExpectation L beta 0 (Ising.spinProd A) :=
      by simpa [S] using Ising.isingExpectation_spinProd_sum_inl L I beta 0 A
    _ = Ising.isingExpectation
          (G.comap (Subtype.val : {v // v ∈ T} → V)) beta 0
          (Ising.spinProd {⟨o, ho⟩, ⟨x, hx⟩}) := by
      rfl





theorem hcaBondDelta_incident_eq (beta h : ℝ) (o y : V) (hoy : o ≠ y) :
    HcovAssembly.hcaBondDelta G beta h o s(o, y) =
      sourcePairDisconnSum (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) {some y, none} ∅ (some o) none := by
  unfold HcovAssembly.hcaBondDelta HcovAssembly.hcaBondSource
  congr 2
  ext z
  cases z <;> simp [Finset.mem_symmDiff, someEmb, hoy, eq_comm] <;> aesop


theorem hcaBondDelta_incident_bound (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (o y : V) (hoy : o ≠ y) :
    Ising.isingExpectation G beta h (Ising.spinProd {y}) *
        HcovAssembly.hcaBondDelta G beta h o s(o, y) ≥
      isingDeltaSelfLowerMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) (some o) (some y) none := by
  have hJ : ∀ e : Sym2 (Option V),
      0 ≤ ghostCoupling h beta (fun _ => 1) e := by
    intro e
    induction e using Sym2.inductionOn with
    | _ a b => cases a <;> cases b <;> simp [ghostCoupling, hh]
  have hdict := fgd_expectationJ_ghost_eq_odd G beta h ({y} : Finset V) (by simp)
  have hsource : insert none (({y} : Finset V).map someEmb) =
      ({some y, none} : Finset (Option V)) := by
    ext z
    cases z <;> simp [someEmb]
  rw [hsource] at hdict
  rw [hcaBondDelta_incident_eq G beta h o y hoy, ← hdict]
  exact ising_delta_bound_cleared_self (withGhost G) beta
    (ghostCoupling h beta (fun _ => 1)) hbeta hJ (by simp)



theorem hcaBondDelta_nonincident_eq_deltaPair_add (beta h : ℝ)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    HcovAssembly.hcaBondDelta G beta h o s(x, y) =
      isingDeltaPairSum (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none +
        isingDeltaPairSum (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) (some o) (some y) (some x) none := by
  have hsource : HcovAssembly.hcaBondSource o s(x, y) =
      ({some o, some x, some y, none} : Finset (Option V)) := by
    rw [HcovAssembly.hcaBondSource_mk]
    ext z
    cases z <;> simp [Finset.mem_symmDiff, someEmb, hox, hoy, hxy, eq_comm] <;> aesop
  rw [HcovAssembly.hcaBondDelta, hsource]
  exact sourcePairDisconn_eq_deltaPair_add (withGhost G) beta
    (ghostCoupling h beta (fun _ => 1))
    (by simpa using hox) (by simpa using hoy) (by simp)
    (by simpa using hxy) (by simp) (by simp)



theorem isingDeltaPair_field_bound (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    Ising.isingExpectation G beta h (Ising.spinProd {y}) *
        isingDeltaPairSum (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none ≥
      isingDeltaLowerMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none := by
  have hJ : ∀ e : Sym2 (Option V),
      0 ≤ ghostCoupling h beta (fun _ => 1) e := by
    intro e
    induction e using Sym2.inductionOn with
    | _ a b => cases a <;> cases b <;> simp [ghostCoupling, hh]
  have hdict := fgd_expectationJ_ghost_eq_odd G beta h ({y} : Finset V) (by simp)
  have hsource : insert none (({y} : Finset V).map someEmb) =
      ({some y, none} : Finset (Option V)) := by
    ext z
    cases z <;> simp [someEmb]
  rw [hsource] at hdict
  rw [← hdict]
  exact ising_delta_bound_cleared (withGhost G) beta
    (ghostCoupling h beta (fun _ => 1)) hbeta hJ
    (by simpa using hox) (by simpa using hoy) (by simp)
    (by simpa using hxy) (by simp) (by simp)

end Sharpness
end StatMech
