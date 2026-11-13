/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.OSSS.ActiveBoundaryDifferential
import Code.OSSS.DecisionTreeReindex









open scoped BigOperators Classical
open Finset Set

namespace StatMech.OSSS.FiniteGraphBoundaryDifferential

open RevealmentConstruction LindebergTree DecisionTree
open FrontierFamilyClose FamilyEqzzzResolution
open ActiveEdgeDifferential ActiveBoundaryDifferential
open PrefixCoversClose ReachBoxCrossing

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

def openCrossEvent (endU endV : E → V) (o : V) (B : Set V) :
    Set (ConfigSpace E) :=
  {omega | ConnOpenSet endU endV omega o B}

noncomputable def openIncidentEdges
    (endU endV : E → V) (o : V) : Finset E :=
  Finset.univ.filter (fun e => endU e = o ∨ endV e = o)

noncomputable def reindexedOpenIncidentEdges
    {I O : Type*} [Fintype I] [DecidableEq I] [DecidableEq O]
    (iota : I → O) (endU endV : I → V) (o : V) : Finset O :=
  (openIncidentEdges endU endV o).image iota

theorem openCrossEvent_isIncreasing
    (endU endV : E → V) (o : V) (B : Set V) :
    IsIncreasing (openCrossEvent endU endV o B) := by
  intro omega eta hle hconn
  exact connOpenSet_mono (fun e he => by
    have h := hle e
    cases hη : eta e
    · exact ((by decide : ¬ ((true : Bool) ≤ false)) (by simpa [he, hη] using h)).elim
    · rfl) hconn

theorem closedProd_incident_le_openCross_complement
    (endU endV : E → V) (o : V) (B : Set V) (hoB : o ∉ B)
    (omega : ConfigSpace E) :
    FK.closedProd (openIncidentEdges endU endV o) omega ≤
      1 - (openCrossEvent endU endV o B).indicator
        (fun _ => (1 : Real)) omega := by
  by_cases hc : ConnOpenSet endU endV omega o B
  · have hm : omega ∈ openCrossEvent endU endV o B := hc
    rw [Set.indicator_of_mem hm, sub_self]
    obtain ⟨b, hbB, hr⟩ := hc
    have hbo : b ≠ o := fun h => hoB (h ▸ hbB)
    obtain ⟨e, hopen, heo⟩ := reachOpen_first_incident hr hbo.symm
    have heI : e ∈ openIncidentEdges endU endV o := by
      unfold openIncidentEdges
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact heo
    unfold FK.closedProd
    exact (Finset.prod_eq_zero heI (by simp [hopen])).le
  · have hm : omega ∉ openCrossEvent endU endV o B := hc
    rw [Set.indicator_of_notMem hm, sub_zero]
    unfold FK.closedProd
    exact Finset.prod_le_one (fun e he => by positivity) (fun e he => by
      split <;> norm_num)

theorem closedProd_reindexedIncident_le_openCross_complement
    {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    (iota : I → O) (endU endV : I → V) (o : V)
    (B : Set V) (hoB : o ∉ B) (omega : ConfigSpace O) :
    FK.closedProd (reindexedOpenIncidentEdges iota endU endV o) omega ≤
      1 - (openCrossEvent endU endV o B).indicator
        (fun _ => (1 : Real)) (restrictConfig iota omega) := by
  by_cases hc : ConnOpenSet endU endV (restrictConfig iota omega) o B
  · have hm : restrictConfig iota omega ∈ openCrossEvent endU endV o B := hc
    rw [Set.indicator_of_mem hm, sub_self]
    obtain ⟨b, hbB, hr⟩ := hc
    have hbo : b ≠ o := fun h => hoB (h ▸ hbB)
    obtain ⟨e, hopen, heo⟩ := reachOpen_first_incident hr hbo.symm
    have heI : iota e ∈ reindexedOpenIncidentEdges iota endU endV o := by
      unfold reindexedOpenIncidentEdges openIncidentEdges
      exact Finset.mem_image.mpr ⟨e, by simp [heo], rfl⟩
    unfold FK.closedProd
    exact (Finset.prod_eq_zero heI (by simp [restrictConfig] at hopen ⊢; exact hopen)).le
  · have hm : restrictConfig iota omega ∉ openCrossEvent endU endV o B := hc
    rw [Set.indicator_of_notMem hm, sub_zero]
    unfold FK.closedProd
    exact Finset.prod_le_one (fun e he => by positivity) (fun e he => by
      split <;> norm_num)

theorem activeBC_reindexed_openCross_one_sub_lower
    {I W : Type*} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (J : Sym2 V → Real) (hJ : ∀ e, 0 < J e)
    (q beta beta0 : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hbeta0 : beta ≤ beta0)
    (iota : I → G.edgeSet) (endU endV : I → W)
    (o : W) (B : Set W) (hoB : o ∉ B) :
    (reindexedOpenIncidentEdges iota endU endV o).prod
        (fun e => Real.exp (-(beta0 * J e.1))) ≤
      1 - Lindeberg.mean
        (FK.activeBCProb G C (FK.betaParams J beta) q)
        (fun omega => (openCrossEvent endU endV o B).indicator
          (fun _ => (1 : Real)) (restrictConfig iota omega)) := by
  let Iout := reindexedOpenIncidentEdges iota endU endV o
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0 omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hparam : Iout.prod (fun e => Real.exp (-(beta0 * J e.1))) ≤
      Iout.prod (fun e => 1 - FK.betaParams J beta e.1) := by
    apply Finset.prod_le_prod
    · intro e he
      exact (Real.exp_pos _).le
    · intro e he
      rw [FK.betaParams]
      simp only [sub_sub_cancel]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hbeta0 (hJ e.1).le
      linarith
  have hclosed := FK.activeBC_prod_closed_param_le G C
    (FK.betaParams_pos hJ hbeta) (FK.betaParams_lt_one J beta) hq Iout
  have hpoint : ∀ omega, mu omega * FK.closedProd Iout omega ≤
      mu omega * (1 - (openCrossEvent endU endV o B).indicator
        (fun _ => (1 : Real)) (restrictConfig iota omega)) := by
    intro omega
    exact mul_le_mul_of_nonneg_left
      (closedProd_reindexedIncident_le_openCross_complement
        iota endU endV o B hoB omega) (hmu0 omega)
  calc
    Iout.prod (fun e => Real.exp (-(beta0 * J e.1))) ≤
        Iout.prod (fun e => 1 - FK.betaParams J beta e.1) := hparam
    _ ≤ ∑ omega, mu omega * FK.closedProd Iout omega := hclosed
    _ ≤ ∑ omega, mu omega *
        (1 - (openCrossEvent endU endV o B).indicator
          (fun _ => (1 : Real)) (restrictConfig iota omega)) :=
      Finset.sum_le_sum fun omega _ => hpoint omega
    _ = 1 - Lindeberg.mean mu (fun omega =>
        (openCrossEvent endU endV o B).indicator
          (fun _ => (1 : Real)) (restrictConfig iota omega)) := by
      unfold Lindeberg.mean
      rw [show (fun omega => mu omega *
          (1 - (openCrossEvent endU endV o B).indicator
            (fun _ => (1 : Real)) (restrictConfig iota omega))) =
          (fun omega => mu omega - mu omega *
            (openCrossEvent endU endV o B).indicator
              (fun _ => (1 : Real)) (restrictConfig iota omega)) by
        funext omega
        ring]
      rw [Finset.sum_sub_distrib, hmu1]
      congr 1
      exact Finset.sum_congr rfl fun omega _ => by ring

theorem activeBC_openCross_one_sub_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (J : Sym2 V → Real) (hJ : ∀ e, 0 < J e)
    (q beta beta0 : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hbeta0 : beta ≤ beta0)
    (endU endV : G.edgeSet → V) (o : V) (B : Set V) (hoB : o ∉ B) :
    (openIncidentEdges endU endV o).prod
        (fun e => Real.exp (-(beta0 * J e.1))) ≤
      1 - Lindeberg.mean
        (FK.activeBCProb G C (FK.betaParams J beta) q)
        ((openCrossEvent endU endV o B).indicator fun _ => (1 : Real)) := by
  let I := openIncidentEdges endU endV o
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0 omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hparam : I.prod (fun e => Real.exp (-(beta0 * J e.1))) ≤
      I.prod (fun e => 1 - FK.betaParams J beta e.1) := by
    apply Finset.prod_le_prod
    · intro e he
      exact (Real.exp_pos _).le
    · intro e he
      rw [FK.betaParams]
      simp only [sub_sub_cancel]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hbeta0 (hJ e.1).le
      linarith
  have hclosed := FK.activeBC_prod_closed_param_le G C
    (FK.betaParams_pos hJ hbeta) (FK.betaParams_lt_one J beta) hq I
  have hpoint : ∀ omega, mu omega * FK.closedProd I omega ≤
      mu omega * (1 - (openCrossEvent endU endV o B).indicator
        (fun _ => (1 : Real)) omega) := by
    intro omega
    exact mul_le_mul_of_nonneg_left
      (closedProd_incident_le_openCross_complement endU endV o B hoB omega)
      (hmu0 omega)
  calc
    I.prod (fun e => Real.exp (-(beta0 * J e.1))) ≤
        I.prod (fun e => 1 - FK.betaParams J beta e.1) := hparam
    _ ≤ ∑ omega, mu omega * FK.closedProd I omega := hclosed
    _ ≤ ∑ omega, mu omega *
        (1 - (openCrossEvent endU endV o B).indicator
          (fun _ => (1 : Real)) omega) :=
      Finset.sum_le_sum fun omega _ => hpoint omega
    _ = 1 - Lindeberg.mean mu
        ((openCrossEvent endU endV o B).indicator fun _ => (1 : Real)) := by
      unfold Lindeberg.mean
      rw [show (fun omega => mu omega *
          (1 - (openCrossEvent endU endV o B).indicator
            (fun _ => (1 : Real)) omega)) =
          (fun omega => mu omega - mu omega *
            (openCrossEvent endU endV o B).indicator
              (fun _ => (1 : Real)) omega) by
        funext omega
        ring]
      rw [Finset.sum_sub_distrib, hmu1]
      congr 1
      exact Finset.sum_congr rfl fun omega _ => by ring


theorem hcov_openCross_mass
    (mu : ConfigSpace E → Real) (hpos : ∀ omega, 0 < mu omega)
    (hmu1 : ∑ omega, mu omega = 1) (hFKG : FKGLatticeCondition mu)
    (endU endV : E → V) (o : V) (l : List E) (hl : ∀ e, e ∈ l)
    (shell disc : Nat → Finset V)
    (hdiscSub : ∀ k, ∀ x ∈ disc k, x ∈ shell k)
    (hshellDisc : ∀ k, ∀ x ∈ shell k, x ∈ disc k)
    (hoDisc : ∀ k, o ∉ disc k)
    (hcross : ∀ k n, 1 ≤ k → k ≤ n → ∀ omega,
      ConnOpenSet endU endV omega o (shell n) →
        ConnOpenSet endU endV omega o (shell k))
    (n : Nat) (hn : 1 ≤ n) (D : Real) (hD : 0 < D)
    (hsum : ∀ e : E,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean mu (fun omega =>
          if ConnOpenSet endU endV omega (endU e) (shell k) then (1 : Real)
          else 0) +
        Lindeberg.mean mu (fun omega =>
          if ConnOpenSet endU endV omega (endV e) (shell k) then (1 : Real)
          else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
    let f : ConfigSpace E → Real :=
      (openCrossEvent endU endV o (shell n)).indicator (fun _ => 1)
    Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) / D ≤
      ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
  classical
  let f : ConfigSpace E → Real :=
    (openCrossEvent endU endV o (shell n)).indicator (fun _ => 1)
  let T : ↑(Finset.Icc 1 n) → DecisionTree E := fun k =>
    crossTree endU endV o (shell n) l (disc k)
  let R : ↑(Finset.Icc 1 n) → E → Real := fun k e =>
    Lindeberg.mean mu (fun omega =>
      if ConnOpenSet endU endV omega (endU e) (shell k) then 1 else 0) +
    Lindeberg.mean mu (fun omega =>
      if ConnOpenSet endU endV omega (endV e) (shell k) then 1 else 0)
  have hf : Monotone f :=
    (openCrossEvent_isIncreasing endU endV o (shell n)).indicator_monotone
  have hidem : ∀ omega, f omega * f omega = f omega := by
    intro omega
    unfold f
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  have hT : ∀ k, (T k).evalR = f := by
    intro k
    funext omega
    have hk1 := (Finset.mem_Icc.mp k.2).1
    have hkn := (Finset.mem_Icc.mp k.2).2
    have heval := evalR_crossTree endU endV o (shell k) (shell n) l hl
      (disc k) (hshellDisc k) (hoDisc k)
      (hcross k n hk1 hkn) omega
    rw [show T k = crossTree endU endV o (shell n) l (disc k) by rfl,
      heval]
    by_cases hc : ConnOpenSet endU endV omega o (shell n)
    · rw [if_pos hc]
      simp [f, openCrossEvent, hc]
    · rw [if_neg hc]
      simp [f, openCrossEvent, hc]
  have hreach : ∀ k e, revealmentMu mu (T k) e ≤ R k e := by
    intro k e
    exact frf_mean_reveal_crossTree_le_connOpen
      (fun omega => (hpos omega).le) endU endV o (shell k) (shell n)
      l (disc k) (hdiscSub k) e
  letI : Nonempty (↑(Finset.Icc 1 n)) :=
    ⟨⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩⟩
  have havg : ∀ e,
      (1 / (Fintype.card (↑(Finset.Icc 1 n)) : Real)) *
        ∑ k, revealmentMu mu (T k) e ≤ D := by
    intro e
    have hle : (∑ k, revealmentMu mu (T k) e) ≤ ∑ k, R k e :=
      Finset.sum_le_sum fun k _ => hreach k e
    have hb := hle.trans (hsum e)
    have hcard : 0 < (Fintype.card (↑(Finset.Icc 1 n)) : Real) := by
      exact_mod_cast Fintype.card_pos
    calc
      (1 / (Fintype.card (↑(Finset.Icc 1 n)) : Real)) *
          ∑ k, revealmentMu mu (T k) e ≤
        (1 / (Fintype.card (↑(Finset.Icc 1 n)) : Real)) *
          ((Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) := by gcongr
      _ = D := by field_simp
  have hmain := var_le_avg_adaptive_reveal_mul_sum_cov_unconditional
    hpos hmu1 hFKG T hf hT D havg
  have hvar : Lindeberg.var mu f =
      Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) :=
    RevealmentBoundAssembly.var_eq_theta_one_sub_theta hidem
  rw [hvar] at hmain
  rw [div_le_iff₀ hD]
  simpa [f, mul_comm] using hmain




theorem hcov_reindexed_openCross_mass
    {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    (mu : ConfigSpace O → Real) (hpos : ∀ omega, 0 < mu omega)
    (hmu1 : ∑ omega, mu omega = 1) (hFKG : FKGLatticeCondition mu)
    (iota : I → O) (hiota : Function.Injective iota)
    (endU endV : I → V) (o : V) (l : List I) (hl : ∀ e, e ∈ l)
    (shell disc : Nat → Finset V)
    (hdiscSub : ∀ k, ∀ x ∈ disc k, x ∈ shell k)
    (hshellDisc : ∀ k, ∀ x ∈ shell k, x ∈ disc k)
    (hoDisc : ∀ k, o ∉ disc k)
    (hcross : ∀ k n, 1 ≤ k → k ≤ n → ∀ omega,
      ConnOpenSet endU endV omega o (shell n) →
        ConnOpenSet endU endV omega o (shell k))
    (n : Nat) (hn : 1 ≤ n) (D : Real) (hD : 0 < D)
    (hsum : ∀ e : I,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean mu (fun omega =>
          if ConnOpenSet endU endV (restrictConfig iota omega)
            (endU e) (shell k) then (1 : Real) else 0) +
        Lindeberg.mean mu (fun omega =>
          if ConnOpenSet endU endV (restrictConfig iota omega)
            (endV e) (shell k) then (1 : Real) else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
    let f : ConfigSpace O → Real := fun omega =>
      (openCrossEvent endU endV o (shell n)).indicator (fun _ => 1)
        (restrictConfig iota omega)
    Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) / D ≤
      ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
  classical
  let f : ConfigSpace O → Real := fun omega =>
    (openCrossEvent endU endV o (shell n)).indicator (fun _ => 1)
      (restrictConfig iota omega)
  let Tinner : ↑(Finset.Icc 1 n) → DecisionTree I := fun k =>
    crossTree endU endV o (shell n) l (disc k)
  let T : ↑(Finset.Icc 1 n) → DecisionTree O := fun k =>
    (Tinner k).reindex iota
  have hf : Monotone f := by
    intro omega eta hle
    apply (openCrossEvent_isIncreasing endU endV o (shell n)).indicator_monotone
    intro e
    exact hle (iota e)
  have hidem : ∀ omega, f omega * f omega = f omega := by
    intro omega
    unfold f
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  have hT : ∀ k, (T k).evalR = f := by
    intro k
    funext omega
    have hk1 := (Finset.mem_Icc.mp k.2).1
    have hkn := (Finset.mem_Icc.mp k.2).2
    have heval := evalR_crossTree endU endV o (shell k) (shell n) l hl
      (disc k) (hshellDisc k) (hoDisc k)
      (hcross k n hk1 hkn) (restrictConfig iota omega)
    rw [show T k = (Tinner k).reindex iota by rfl, evalR_reindex, heval]
    by_cases hc : ConnOpenSet endU endV (restrictConfig iota omega) o (shell n)
    · rw [if_pos hc]
      simp [f, openCrossEvent, hc]
    · rw [if_neg hc]
      simp [f, openCrossEvent, hc]
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega => (hpos omega).le
  have hreachImage : ∀ k e,
      revealmentMu mu (T k) (iota e) ≤
        Lindeberg.mean mu (fun omega =>
          if ConnOpenSet endU endV (restrictConfig iota omega)
            (endU e) (shell k) then (1 : Real) else 0) +
        Lindeberg.mean mu (fun omega =>
          if ConnOpenSet endU endV (restrictConfig iota omega)
            (endV e) (shell k) then (1 : Real) else 0) := by
    intro k e
    unfold revealmentMu
    refine (mean_indicator_mono hmu0 _ _ ?_).trans
      (mean_indicator_or_le hmu0 _ _)
    intro omega hquery
    have hqueryInner : e ∈ (Tinner k).queried (restrictConfig iota omega) := by
      apply (DecisionTree.mem_queried_reindex_iff iota hiota
        (Tinner k) omega e).mp
      simpa [T] using hquery
    exact queried_crossTree_imp endU endV o (shell k) (shell n) l
      (disc k) (hdiscSub k) (restrictConfig iota omega) e hqueryInner
  letI : Nonempty (↑(Finset.Icc 1 n)) :=
    ⟨⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩⟩
  have havg : ∀ e,
      (1 / (Fintype.card (↑(Finset.Icc 1 n)) : Real)) *
        ∑ k, revealmentMu mu (T k) e ≤ D := by
    intro e
    by_cases he : e ∈ Set.range iota
    · obtain ⟨i, rfl⟩ := he
      have hs : (∑ k, revealmentMu mu (T k) (iota i)) ≤
          ∑ k : ↑(Finset.Icc 1 n),
            (Lindeberg.mean mu (fun omega =>
              if ConnOpenSet endU endV (restrictConfig iota omega)
                (endU i) (shell k) then (1 : Real) else 0) +
            Lindeberg.mean mu (fun omega =>
              if ConnOpenSet endU endV (restrictConfig iota omega)
                (endV i) (shell k) then (1 : Real) else 0)) :=
        Finset.sum_le_sum fun k _ => hreachImage k i
      have hb := hs.trans (hsum i)
      calc
        (1 / (Fintype.card (↑(Finset.Icc 1 n)) : Real)) *
            ∑ k, revealmentMu mu (T k) (iota i) ≤
          (1 / (Fintype.card (↑(Finset.Icc 1 n)) : Real)) *
            ((Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) := by gcongr
        _ = D := by field_simp
    · have hz : ∀ k, revealmentMu mu (T k) e = 0 := by
        intro k
        unfold revealmentMu Lindeberg.mean
        apply Finset.sum_eq_zero
        intro omega _
        change (if e ∈ (T k).queried omega then (1 : Real) else 0) * mu omega = 0
        rw [if_neg]
        · ring
        · exact DecisionTree.not_mem_queried_reindex_of_not_range
            iota (Tinner k) omega e he
      simp_rw [hz]
      simpa using hD.le
  have hmain := var_le_avg_adaptive_reveal_mul_sum_cov_unconditional
    hpos hmu1 hFKG T hf hT D havg
  have hvar : Lindeberg.var mu f =
      Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) :=
    RevealmentBoundAssembly.var_eq_theta_one_sub_theta hidem
  rw [hvar] at hmain
  exact (div_le_iff₀ hD).2
    (by simpa [mul_assoc, mul_comm, mul_left_comm] using hmain)



theorem activeBC_openCross_differential_inequality
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty G.edgeSet]
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (J : Sym2 V → Real) (hJ : ∀ e, 0 < J e)
    (q beta beta0 : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hbeta0 : beta ≤ beta0)
    (endU endV : G.edgeSet → V) (hcoh : ∀ e, e.1 = s(endU e, endV e))
    (o : V) (l : List G.edgeSet) (hl : ∀ e, e ∈ l)
    (shell disc : Nat → Finset V)
    (hdiscSub : ∀ k, ∀ x ∈ disc k, x ∈ shell k)
    (hshellDisc : ∀ k, ∀ x ∈ shell k, x ∈ disc k)
    (hoDisc : ∀ k, o ∉ disc k)
    (hcross : ∀ k n, 1 ≤ k → k ≤ n → ∀ omega,
      ConnOpenSet endU endV omega o (shell n) →
        ConnOpenSet endU endV omega o (shell k))
    (n : Nat) (hn : 1 ≤ n) (D : Real) (hD : 0 < D)
    (hsum : ∀ e : G.edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean
          (FK.activeBCProb G C (FK.betaParams J beta) q) (fun omega =>
            if ConnOpenSet endU endV omega (endU e) (shell k) then 1 else 0) +
        Lindeberg.mean
          (FK.activeBCProb G C (FK.betaParams J beta) q) (fun omega =>
            if ConnOpenSet endU endV omega (endV e) (shell k) then 1 else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
    ∃ c : Real, 0 < c ∧
      c * (Lindeberg.mean
        (FK.activeBCProb G C (FK.betaParams J beta) q)
        ((openCrossEvent endU endV o (shell n)).indicator (fun _ => 1)) / D) ≤
      deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q
        (openCrossEvent endU endV o (shell n))) beta := by
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  let f := (openCrossEvent endU endV o (shell n)).indicator (fun _ => (1 : Real))
  let theta := Lindeberg.mean mu f
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpos : ∀ omega, 0 < mu omega := fun omega =>
    FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0 omega
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    FK.activeBCProb_FKGLatticeCondition G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq
  have hcov := hcov_openCross_mass mu hpos hmu1 hFKG endU endV o l hl
    shell disc hdiscSub hshellDisc hoDisc hcross n hn D hD hsum
  have htheta : 0 ≤ theta := by
    unfold theta f Lindeberg.mean
    exact Finset.sum_nonneg fun omega _ => mul_nonneg (by
      rw [Set.indicator_apply]
      split_ifs <;> norm_num) (hpos omega).le
  let kappa := (openIncidentEdges endU endV o).prod
    (fun e => Real.exp (-(beta0 * J e.1)))
  have hkappa : 0 < kappa := Finset.prod_pos fun e he => Real.exp_pos _
  have hgap : kappa ≤ 1 - theta := by
    have hoShell : o ∉ (shell n : Set V) := fun ho => hoDisc n (hshellDisc n o ho)
    simpa [kappa, theta, mu, f] using
      (activeBC_openCross_one_sub_lower G C J hJ q beta beta0 hq hbeta
        hbeta0 endU endV o (shell n : Set V) hoShell)
  have hcov0 : ∀ e : G.edgeSet,
      0 ≤ FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e) := by
    intro e
    rw [← cov_activeBC_eq]
    exact cov_coord_nonneg hpos hmu1 hFKG
      ((openCrossEvent_isIncreasing endU endV o (shell n)).indicator_monotone) e
  have hderiv := FK.hasDerivAt_activeBCProbOf_beta_sum G C hJ hbeta hq0
    (openCrossEvent endU endV o (shell n))
  have hderivEq :
      deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q
        (openCrossEvent endU endV o (shell n))) beta =
      ∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(beta * J e.1)))) *
        FK.activeBCCov G C (FK.betaParams J beta) q f (Lindeberg.coord e) := by
    rw [hderiv.deriv]
  obtain ⟨cR, hcR, hRusso⟩ :=
    RussoPrefactor.rp_differential_lower_weighted_beta
      (fun e : G.edgeSet => J e.1)
      (fun e => FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e)) beta _ (fun e => hJ e.1) hbeta hcov0 hderivEq
  refine ⟨cR * kappa, mul_pos hcR hkappa, ?_⟩
  calc
    (cR * kappa) * (theta / D) ≤
        cR * (theta * (1 - theta) / D) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hcR.le
      calc
        kappa * (theta / D) = (theta * kappa) / D := by ring
        _ ≤ (theta * (1 - theta)) / D :=
          (div_le_div_iff_of_pos_right hD).2
            (mul_le_mul_of_nonneg_left hgap htheta)
    _ ≤ cR * ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
      exact mul_le_mul_of_nonneg_left hcov hcR.le
    _ ≤ deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q
        (openCrossEvent endU endV o (shell n))) beta := by
      simpa [mu, f, cov_activeBC_eq] using hRusso

end StatMech.OSSS.FiniteGraphBoundaryDifferential
