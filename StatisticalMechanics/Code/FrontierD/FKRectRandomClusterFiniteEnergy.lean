/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRandomClusterFKG
import Code.FK.CircuitLowerBound
import Code.FK.FinitePatternEnergy









open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

open StatMech

local instance fkRectFiniteEnergyDecidableRel (R : FKRectTorus) :
    DecidableRel (fkRectTorusGraph R).Adj := Classical.decRel _

@[simp] theorem fkRectGraphConfigurationExtend_setOpen
    (R : FKRectTorus) (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) :
    fkRectGraphConfigurationExtend R (setOpen e eta) =
      setOpen e.1 (fkRectGraphConfigurationExtend R eta) := by
  funext x
  by_cases hx : x = e.1
  · subst x
    simp [fkRectGraphConfigurationExtend, e.2]
  · by_cases hxe : x ∈ (fkRectTorusGraph R).edgeSet
    · have hsub : (⟨x, hxe⟩ : {x // x ∈ (fkRectTorusGraph R).edgeSet}) ≠ e :=
        fun h => hx (congrArg Subtype.val h)
      simp [fkRectGraphConfigurationExtend, hxe,
        setOpen_of_ne hsub, setOpen_of_ne hx]
    · simp [fkRectGraphConfigurationExtend, hxe,
        setOpen_of_ne hx]

@[simp] theorem fkRectGraphConfigurationExtend_setClosed
    (R : FKRectTorus) (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) :
    fkRectGraphConfigurationExtend R (setClosed e eta) =
      setClosed e.1 (fkRectGraphConfigurationExtend R eta) := by
  funext x
  by_cases hx : x = e.1
  · subst x
    simp [fkRectGraphConfigurationExtend, e.2]
  · by_cases hxe : x ∈ (fkRectTorusGraph R).edgeSet
    · have hsub : (⟨x, hxe⟩ : {x // x ∈ (fkRectTorusGraph R).edgeSet}) ≠ e :=
        fun h => hx (congrArg Subtype.val h)
      simp [fkRectGraphConfigurationExtend, hxe,
        setClosed_of_ne hsub, setClosed_of_ne hx]
    · simp [fkRectGraphConfigurationExtend, hxe,
        setClosed_of_ne hx]



theorem fkRectGraphCriticalProb_setClosed_ge
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) :
    FK.cFE (fkRectCriticalP q) q *
        (fkRectGraphCriticalRandomClusterProb R q
            (setOpen e eta) +
          fkRectGraphCriticalRandomClusterProb R q
            (setClosed e eta)) ≤
      fkRectGraphCriticalRandomClusterProb R q
        (setClosed e eta) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp : 0 < fkRectCriticalP q := fkRectCriticalP_pos hq0
  have hp1 : fkRectCriticalP q < 1 := fkRectCriticalP_lt_one hq0
  have hraw := FK.fkWeight_setClosed_ge (fkRectTorusGraph R)
    hp hp1 hq e.1 (fkRectGraphConfigurationExtend R eta)
  rw [← fkRectGraphConfigurationExtend_setOpen,
    ← fkRectGraphConfigurationExtend_setClosed] at hraw
  simp_rw [fkWeight_configurationExtend_critical R hq0] at hraw
  have hfactor : 0 < fkRectCriticalEdgeFactor R q :=
    fkRectCriticalEdgeFactor_pos R hq0
  have hreduced :
      FK.cFE (fkRectCriticalP q) q *
          (fkRectGraphCriticalReducedWeight R q
              (setOpen e eta) +
            fkRectGraphCriticalReducedWeight R q
              (setClosed e eta)) ≤
        fkRectGraphCriticalReducedWeight R q
          (setClosed e eta) := by
    nlinarith
  have hZ : 0 < fkRectGraphCriticalReducedZ R q :=
    fkRectGraphCriticalReducedZ_pos R hq0
  unfold fkRectGraphCriticalRandomClusterProb
  rw [← add_div]
  rw [show FK.cFE (fkRectCriticalP q) q *
      ((fkRectGraphCriticalReducedWeight R q
            (setOpen e eta) +
          fkRectGraphCriticalReducedWeight R q
            (setClosed e eta)) /
        fkRectGraphCriticalReducedZ R q) =
      (FK.cFE (fkRectCriticalP q) q *
        (fkRectGraphCriticalReducedWeight R q
            (setOpen e eta) +
          fkRectGraphCriticalReducedWeight R q
            (setClosed e eta))) /
        fkRectGraphCriticalReducedZ R q by ring]
  exact (div_le_div_iff_of_pos_right hZ).2 hreduced



theorem fkRectGraphCriticalProb_setOpen_ge
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) :
    FK.cFE (fkRectCriticalP q) q *
        (fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) +
          fkRectGraphCriticalRandomClusterProb R q (setClosed e eta)) ≤
      fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp : 0 < fkRectCriticalP q := fkRectCriticalP_pos hq0
  have hp1 : fkRectCriticalP q < 1 := fkRectCriticalP_lt_one hq0
  have hraw := FK.fkWeight_setOpen_ge (fkRectTorusGraph R)
    hp hp1 hq e.1 (fkRectGraphConfigurationExtend R eta)
  rw [← fkRectGraphConfigurationExtend_setOpen,
    ← fkRectGraphConfigurationExtend_setClosed] at hraw
  simp_rw [fkWeight_configurationExtend_critical R hq0] at hraw
  have hfactor : 0 < fkRectCriticalEdgeFactor R q :=
    fkRectCriticalEdgeFactor_pos R hq0
  have hreduced :
      FK.cFE (fkRectCriticalP q) q *
          (fkRectGraphCriticalReducedWeight R q (setOpen e eta) +
            fkRectGraphCriticalReducedWeight R q (setClosed e eta)) ≤
        fkRectGraphCriticalReducedWeight R q (setOpen e eta) := by
    nlinarith
  have hZ : 0 < fkRectGraphCriticalReducedZ R q :=
    fkRectGraphCriticalReducedZ_pos R hq0
  unfold fkRectGraphCriticalRandomClusterProb
  rw [← add_div]
  rw [show FK.cFE (fkRectCriticalP q) q *
      ((fkRectGraphCriticalReducedWeight R q (setOpen e eta) +
          fkRectGraphCriticalReducedWeight R q (setClosed e eta)) /
        fkRectGraphCriticalReducedZ R q) =
      (FK.cFE (fkRectCriticalP q) q *
        (fkRectGraphCriticalReducedWeight R q (setOpen e eta) +
          fkRectGraphCriticalReducedWeight R q (setClosed e eta))) /
        fkRectGraphCriticalReducedZ R q by ring]
  exact (div_le_div_iff_of_pos_right hZ).2 hreduced


noncomputable def fkRectGraphCriticalClosedMass
    (R : FKRectTorus) (q : Real)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) : Real :=
  ∑ eta ∈ Finset.univ.filter
      (fun eta : FKRectGraphConfiguration R => ∀ e ∈ I, eta e = false),
    fkRectGraphCriticalRandomClusterProb R q eta

theorem fkRectGraphCriticalClosedMass_empty
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    fkRectGraphCriticalClosedMass R q ∅ = 1 := by
  classical
  unfold fkRectGraphCriticalClosedMass
  rw [show Finset.univ.filter
      (fun eta : FKRectGraphConfiguration R =>
        ∀ e ∈ (∅ : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}),
          eta e = false) = Finset.univ by ext eta; simp]
  exact sum_fkRectGraphCriticalRandomClusterProb R hq


noncomputable def fkRectGraphClosedFibre
    (R : FKRectTorus)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    Finset (FKRectGraphConfiguration R) :=
  Finset.univ.filter fun eta =>
    eta e = false ∧ ∀ e' ∈ I, eta e' = false

theorem fkRectGraphCriticalClosedMass_reindex
    (R : FKRectTorus) (q : Real)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
    (he : e ∉ I) :
    fkRectGraphCriticalClosedMass R q I =
      ∑ eta ∈ fkRectGraphClosedFibre R e I,
        (fkRectGraphCriticalRandomClusterProb R q
          (setOpen e eta) +
          fkRectGraphCriticalRandomClusterProb R q
            (setClosed e eta)) := by
  classical
  unfold fkRectGraphCriticalClosedMass fkRectGraphClosedFibre
  rw [Finset.sum_add_distrib]
  have hclosed :
      (∑ eta ∈ Finset.univ.filter
          (fun eta : FKRectGraphConfiguration R =>
            eta e = false ∧ ∀ e' ∈ I, eta e' = false),
        fkRectGraphCriticalRandomClusterProb R q
          (setClosed e eta)) =
      ∑ omega ∈ Finset.univ.filter
          (fun omega : FKRectGraphConfiguration R =>
            (∀ e' ∈ I, omega e' = false) ∧ omega e = false),
        fkRectGraphCriticalRandomClusterProb R q omega := by
    apply Finset.sum_nbij' (fun eta => eta) (fun omega => omega)
    · intro eta heta
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta ⊢
      exact ⟨heta.2, heta.1⟩
    · intro omega homega
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega ⊢
      exact ⟨homega.2, homega.1⟩
    · intro eta _
      rfl
    · intro omega _
      rfl
    · intro eta heta
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
      congr 1
      funext x
      by_cases hx : x = e
      · subst x
        simp [heta.1]
      · rw [setClosed_of_ne hx]
  have hopen :
      (∑ eta ∈ Finset.univ.filter
          (fun eta : FKRectGraphConfiguration R =>
            eta e = false ∧ ∀ e' ∈ I, eta e' = false),
        fkRectGraphCriticalRandomClusterProb R q
          (setOpen e eta)) =
      ∑ omega ∈ Finset.univ.filter
          (fun omega : FKRectGraphConfiguration R =>
            (∀ e' ∈ I, omega e' = false) ∧ omega e = true),
        fkRectGraphCriticalRandomClusterProb R q omega := by
    apply Finset.sum_nbij'
      (fun eta => setOpen e eta)
      (fun omega => setClosed e omega)
    · intro eta heta
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta ⊢
      refine ⟨fun e' he' => ?_, by simp⟩
      have hne : e' ≠ e := fun h => he (h ▸ he')
      rw [setOpen_of_ne hne]
      exact heta.2 e' he'
    · intro omega homega
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega ⊢
      refine ⟨by simp, fun e' he' => ?_⟩
      have hne : e' ≠ e := fun h => he (h ▸ he')
      rw [setClosed_of_ne hne]
      exact homega.1 e' he'
    · intro eta heta
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
      funext x
      by_cases hx : x = e
      · subst x
        simp [heta.1]
      · rw [setClosed_of_ne hx, setOpen_of_ne hx]
    · intro omega homega
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega
      funext x
      by_cases hx : x = e
      · subst x
        simp [homega.2]
      · rw [setOpen_of_ne hx, setClosed_of_ne hx]
    · intro eta _
      rfl
  rw [hopen, hclosed]
  have htrue :
      Finset.univ.filter
          (fun omega : FKRectGraphConfiguration R =>
            (∀ e' ∈ I, omega e' = false) ∧ omega e = true) =
        (Finset.univ.filter fun omega : FKRectGraphConfiguration R =>
          ∀ e' ∈ I, omega e' = false).filter
            (fun omega => ¬ omega e = false) := by
    ext omega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.not_eq_false]
  have hfalse :
      Finset.univ.filter
          (fun omega : FKRectGraphConfiguration R =>
            (∀ e' ∈ I, omega e' = false) ∧ omega e = false) =
        (Finset.univ.filter fun omega : FKRectGraphConfiguration R =>
          ∀ e' ∈ I, omega e' = false).filter
            (fun omega => omega e = false) := by
    ext omega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [htrue, hfalse, add_comm]
  exact (Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun omega : FKRectGraphConfiguration R =>
      ∀ e' ∈ I, omega e' = false)
    (fun omega => omega e = false)
    (fkRectGraphCriticalRandomClusterProb R q)).symm

theorem fkRectGraphCriticalClosedMass_insert_reindex
    (R : FKRectTorus) (q : Real)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    fkRectGraphCriticalClosedMass R q (insert e I) =
      ∑ eta ∈ fkRectGraphClosedFibre R e I,
        fkRectGraphCriticalRandomClusterProb R q
          (setClosed e eta) := by
  classical
  unfold fkRectGraphCriticalClosedMass fkRectGraphClosedFibre
  apply Finset.sum_nbij' (fun omega => omega) (fun eta => eta)
  · intro omega homega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.forall_mem_insert] at homega ⊢
    exact ⟨homega.1, homega.2⟩
  · intro eta heta
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.forall_mem_insert] at heta ⊢
    exact ⟨heta.1, heta.2⟩
  · intro omega _
    rfl
  · intro eta _
    rfl
  · intro omega homega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.forall_mem_insert] at homega
    congr 1
    funext x
    by_cases hx : x = e
    · subst x
      simp [homega.1]
    · rw [setClosed_of_ne hx]

theorem fkRectGraphCritical_cFE_mul_closedMass_le_insert
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
    (he : e ∉ I) :
    FK.cFE (fkRectCriticalP q) q *
        fkRectGraphCriticalClosedMass R q I ≤
      fkRectGraphCriticalClosedMass R q (insert e I) := by
  rw [fkRectGraphCriticalClosedMass_reindex R q e he,
    fkRectGraphCriticalClosedMass_insert_reindex R q e I,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro eta heta
  exact fkRectGraphCriticalProb_setClosed_ge R hq e eta



theorem fkRectGraphCritical_cFE_pow_le_closedMass
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    FK.cFE (fkRectCriticalP q) q ^ I.card ≤
      fkRectGraphCriticalClosedMass R q I := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  classical
  induction I using Finset.induction with
  | empty =>
      rw [Finset.card_empty, pow_zero,
        fkRectGraphCriticalClosedMass_empty R hq0]
  | @insert e I he ih =>
      rw [Finset.card_insert_of_notMem he, pow_succ]
      calc
        FK.cFE (fkRectCriticalP q) q ^ I.card *
              FK.cFE (fkRectCriticalP q) q =
            FK.cFE (fkRectCriticalP q) q *
              FK.cFE (fkRectCriticalP q) q ^ I.card := by ring
        _ ≤ FK.cFE (fkRectCriticalP q) q *
              fkRectGraphCriticalClosedMass R q I :=
          mul_le_mul_of_nonneg_left ih
            (FK.cFE_pos (fkRectCriticalP_pos hq0)
              (fkRectCriticalP_lt_one hq0) hq).le
        _ ≤ fkRectGraphCriticalClosedMass R q (insert e I) :=
          fkRectGraphCritical_cFE_mul_closedMass_le_insert R hq e he



noncomputable def fkRectGraphCriticalOpenMass
    (R : FKRectTorus) (q : Real)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) : Real :=
  ∑ eta ∈ Finset.univ.filter
      (fun eta : FKRectGraphConfiguration R => ∀ e ∈ I, eta e = true),
    fkRectGraphCriticalRandomClusterProb R q eta

def fkRectGraphOpenIndicator
    (R : FKRectTorus)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) : Real :=
  if ∀ e ∈ I, eta e = true then 1 else 0

theorem fkRectGraphCriticalOpenMass_eq_expectation
    (R : FKRectTorus) (q : Real)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    fkRectGraphCriticalOpenMass R q I =
      ∑ eta, fkRectGraphCriticalRandomClusterProb R q eta *
        fkRectGraphOpenIndicator R I eta := by
  classical
  unfold fkRectGraphCriticalOpenMass fkRectGraphOpenIndicator
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro eta heta
  by_cases h : ∀ e ∈ I, eta e = true
  · simp [h]
  · simp [h]

theorem monotone_fkRectGraphOpenIndicator
    (R : FKRectTorus)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    Monotone (fkRectGraphOpenIndicator R I) := by
  intro eta zeta hetaZeta
  unfold fkRectGraphOpenIndicator
  by_cases heta : ∀ e ∈ I, eta e = true
  · have hzeta : ∀ e ∈ I, zeta e = true := by
      intro e he
      have hcoord := hetaZeta e
      rw [heta e he] at hcoord
      exact Bool.eq_true_of_true_le hcoord
    rw [if_pos heta, if_pos hzeta]
  · rw [if_neg heta]
    positivity

theorem fkRectGraphOpenIndicator_insert
    (R : FKRectTorus)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) :
    fkRectGraphOpenIndicator R (insert e I) eta =
      fkRectGraphOpenIndicator R {e} eta *
        fkRectGraphOpenIndicator R I eta := by
  classical
  unfold fkRectGraphOpenIndicator
  by_cases he : eta e = true <;>
    by_cases hI : ∀ a ∈ I, eta a = true <;>
    simp [he, hI]

theorem fkRectGraphCriticalOpenMass_singleton_reindex
    (R : FKRectTorus) (q : Real)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    fkRectGraphCriticalOpenMass R q {e} =
      ∑ eta ∈ fkRectGraphClosedFibre R e ∅,
        fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) := by
  classical
  unfold fkRectGraphCriticalOpenMass fkRectGraphClosedFibre
  apply Finset.sum_nbij'
    (fun omega => setClosed e omega) (fun eta => setOpen e eta)
  · intro omega homega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega ⊢
    simp
  · intro eta heta
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta ⊢
    simp
  · intro omega homega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega
    funext x
    by_cases hx : x = e
    · subst x
      rw [setOpen_self]
      exact (homega e (Finset.mem_singleton_self e)).symm
    · rw [setOpen_of_ne hx, setClosed_of_ne hx]
  · intro eta heta
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta
    funext x
    by_cases hx : x = e
    · subst x
      simp [heta.1]
    · rw [setClosed_of_ne hx, setOpen_of_ne hx]
  · intro omega homega
    congr 1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at homega
    funext x
    by_cases hx : x = e
    · subst x
      rw [setOpen_self]
      exact homega e (Finset.mem_singleton_self e)
    · rw [setOpen_of_ne hx, setClosed_of_ne hx]

theorem fkRectGraphCritical_cFE_le_openMass_singleton
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    FK.cFE (fkRectCriticalP q) q ≤
      fkRectGraphCriticalOpenMass R q {e} := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have htotal := fkRectGraphCriticalClosedMass_reindex
    R q e (I := ∅) (by simp)
  rw [fkRectGraphCriticalClosedMass_empty R hq0] at htotal
  rw [fkRectGraphCriticalOpenMass_singleton_reindex R q e]
  calc
    FK.cFE (fkRectCriticalP q) q =
        FK.cFE (fkRectCriticalP q) q * 1 := by ring
    _ = FK.cFE (fkRectCriticalP q) q *
        ∑ eta ∈ fkRectGraphClosedFibre R e ∅,
          (fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) +
            fkRectGraphCriticalRandomClusterProb R q (setClosed e eta)) := by
      rw [htotal]
    _ = ∑ eta ∈ fkRectGraphClosedFibre R e ∅,
        FK.cFE (fkRectCriticalP q) q *
          (fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) +
            fkRectGraphCriticalRandomClusterProb R q (setClosed e eta)) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ eta ∈ fkRectGraphClosedFibre R e ∅,
        fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) := by
      apply Finset.sum_le_sum
      intro eta heta
      exact fkRectGraphCriticalProb_setOpen_ge R hq e eta

theorem fkRectGraphCriticalOpenMass_nonneg
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    0 ≤ fkRectGraphCriticalOpenMass R q I := by
  unfold fkRectGraphCriticalOpenMass
  exact Finset.sum_nonneg fun eta heta =>
    fkRectGraphCriticalRandomClusterProb_nonneg R hq eta

theorem fkRectGraphCritical_cFE_mul_openMass_le_insert
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    FK.cFE (fkRectCriticalP q) q *
        fkRectGraphCriticalOpenMass R q I ≤
      fkRectGraphCriticalOpenMass R q (insert e I) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hPA := fkRectGraphCritical_positivelyAssociated R hq
    (monotone_fkRectGraphOpenIndicator R {e})
    (monotone_fkRectGraphOpenIndicator R I)
  rw [← fkRectGraphCriticalOpenMass_eq_expectation R q {e},
    ← fkRectGraphCriticalOpenMass_eq_expectation R q I] at hPA
  rw [fkRectGraphCriticalOpenMass_eq_expectation R q (insert e I)]
  simp_rw [fkRectGraphOpenIndicator_insert R e I]
  exact (mul_le_mul_of_nonneg_right
      (fkRectGraphCritical_cFE_le_openMass_singleton R hq e)
      (fkRectGraphCriticalOpenMass_nonneg R hq0 I)).trans hPA



theorem fkRectGraphCritical_cFE_pow_le_openMass
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    FK.cFE (fkRectCriticalP q) q ^ I.card ≤
      fkRectGraphCriticalOpenMass R q I := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  classical
  induction I using Finset.induction with
  | empty =>
      rw [Finset.card_empty, pow_zero]
      unfold fkRectGraphCriticalOpenMass
      rw [show Finset.univ.filter
          (fun eta : FKRectGraphConfiguration R =>
            ∀ e ∈ (∅ : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}),
              eta e = true) = Finset.univ by ext eta; simp]
      exact (sum_fkRectGraphCriticalRandomClusterProb R hq0).ge
  | @insert e I he ih =>
      rw [Finset.card_insert_of_notMem he, pow_succ]
      calc
        FK.cFE (fkRectCriticalP q) q ^ I.card *
              FK.cFE (fkRectCriticalP q) q =
            FK.cFE (fkRectCriticalP q) q *
              FK.cFE (fkRectCriticalP q) q ^ I.card := by ring
        _ ≤ FK.cFE (fkRectCriticalP q) q *
              fkRectGraphCriticalOpenMass R q I :=
          mul_le_mul_of_nonneg_left ih
            (FK.cFE_pos (fkRectCriticalP_pos hq0)
              (fkRectCriticalP_lt_one hq0) hq).le
        _ ≤ fkRectGraphCriticalOpenMass R q (insert e I) :=
          fkRectGraphCritical_cFE_mul_openMass_le_insert R hq e I



noncomputable def fkRectCriticalClosedMass
    (R : FKRectTorus) (q : Real) (I : Finset R.EdgeIndex) : Real :=
  ∑ omega ∈ Finset.univ.filter
      (fun omega : R.Configuration => ∀ a ∈ I, omega a = false),
    fkRectCriticalRandomClusterProb R q omega



theorem fkRectGraphCriticalClosedMass_map_edgeEquiv
    (R : FKRectTorus) (q : Real) (I : Finset R.EdgeIndex) :
    fkRectGraphCriticalClosedMass R q
        (I.map (fkRectEdgeGraphEquiv R).toEmbedding) =
      fkRectCriticalClosedMass R q I := by
  classical
  unfold fkRectGraphCriticalClosedMass fkRectCriticalClosedMass
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (fkRectConfigurationGraphEquiv R)
  intro omega
  have hpred :
      (∀ a ∈ I, omega a = false) ↔
        ∀ e ∈ I.map (fkRectEdgeGraphEquiv R).toEmbedding,
          fkRectConfigurationGraphEquiv R omega e = false := by
    constructor
    · intro h e he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 he
      simpa using h a ha
    · intro h a ha
      have he : fkRectEdgeGraphEquiv R a ∈
          I.map (fkRectEdgeGraphEquiv R).toEmbedding :=
        Finset.mem_map.2 ⟨a, ha, rfl⟩
      simpa using h (fkRectEdgeGraphEquiv R a) he
  by_cases homega : ∀ a ∈ I, omega a = false
  · rw [if_pos homega, if_pos (hpred.1 homega)]
    exact
      (fkRectGraphCriticalRandomClusterProb_configurationGraphEquiv
        R q omega).symm
  · rw [if_neg homega, if_neg (not_congr hpred |>.1 homega)]



theorem fkRectCritical_cFE_pow_le_closedMass
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) :
    FK.cFE (fkRectCriticalP q) q ^ I.card ≤
      fkRectCriticalClosedMass R q I := by
  rw [← fkRectGraphCriticalClosedMass_map_edgeEquiv R q I]
  simpa using fkRectGraphCritical_cFE_pow_le_closedMass R hq
    (I.map (fkRectEdgeGraphEquiv R).toEmbedding)



noncomputable def fkRectCriticalOpenMass
    (R : FKRectTorus) (q : Real) (I : Finset R.EdgeIndex) : Real :=
  ∑ omega ∈ Finset.univ.filter
      (fun omega : R.Configuration => ∀ a ∈ I, omega a = true),
    fkRectCriticalRandomClusterProb R q omega

theorem fkRectGraphCriticalOpenMass_map_edgeEquiv
    (R : FKRectTorus) (q : Real) (I : Finset R.EdgeIndex) :
    fkRectGraphCriticalOpenMass R q
        (I.map (fkRectEdgeGraphEquiv R).toEmbedding) =
      fkRectCriticalOpenMass R q I := by
  classical
  unfold fkRectGraphCriticalOpenMass fkRectCriticalOpenMass
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (fkRectConfigurationGraphEquiv R)
  intro omega
  have hpred :
      (∀ a ∈ I, omega a = true) ↔
        ∀ e ∈ I.map (fkRectEdgeGraphEquiv R).toEmbedding,
          fkRectConfigurationGraphEquiv R omega e = true := by
    constructor
    · intro h e he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 he
      simpa using h a ha
    · intro h a ha
      have he : fkRectEdgeGraphEquiv R a ∈
          I.map (fkRectEdgeGraphEquiv R).toEmbedding :=
        Finset.mem_map.2 ⟨a, ha, rfl⟩
      simpa using h (fkRectEdgeGraphEquiv R a) he
  by_cases homega : ∀ a ∈ I, omega a = true
  · rw [if_pos homega, if_pos (hpred.1 homega)]
    exact
      (fkRectGraphCriticalRandomClusterProb_configurationGraphEquiv
        R q omega).symm
  · rw [if_neg homega, if_neg (not_congr hpred |>.1 homega)]



theorem fkRectCritical_cFE_pow_le_openMass
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) :
    FK.cFE (fkRectCriticalP q) q ^ I.card ≤
      fkRectCriticalOpenMass R q I := by
  rw [← fkRectGraphCriticalOpenMass_map_edgeEquiv R q I]
  simpa using fkRectGraphCritical_cFE_pow_le_openMass R hq
    (I.map (fkRectEdgeGraphEquiv R).toEmbedding)

end

end StatMech.FrontierD
