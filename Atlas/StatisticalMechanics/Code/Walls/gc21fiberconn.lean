/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Mathlib
import Code.Walls.gc20closure
import Code.Walls.gc19switching
import Code.Walls.gc18core
import Code.Walls.gc16core
import Code.Walls.gc7core
import Code.Walls.gc6_munonneg
import Code.Ising.TwoReplica
import Code.Ising.TwoReplicaWeighted
import Code.Ising.HdomNativeWeight
import Code.Ising.AizenmanSignDominance
import Code.Sharpness.FluxEdgeCopyBridge

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.FieldGhostDict
















private def gc21_E2 : Finset (Sym2 (Fin 2)) := {s(0, 1)}



private noncomputable def gc21_m2 : Ising.Current (Fin 2) := fun e => if e = s(0, 1) then 2 else 0











theorem gc21_oddFibre_not_of_posFull :
    connP (posEdges gc21_E2 gc21_m2) 0 1 ∧ ¬ connP (oddEdges gc21_E2 gc21_m2) 0 1 := by
  refine ⟨?_, ?_⟩
  · 
    refine Relation.ReflTransGen.single ⟨s(0, 1), ?_, by simp, by simp, by decide⟩
    rw [posEdges, Finset.mem_filter]
    refine ⟨by rw [gc21_E2]; simp, ?_⟩
    show 1 ≤ gc21_m2 s(0, 1)
    simp only [gc21_m2]; decide
  · 
    intro h
    have hempty : oddEdges gc21_E2 gc21_m2 = ∅ := by
      rw [oddEdges]
      apply Finset.filter_eq_empty_iff.mpr
      intro e he
      rw [gc21_E2, Finset.mem_singleton] at he
      subst he
      show ¬ Odd (gc21_m2 s(0, 1))
      simp only [gc21_m2]; decide
    rw [hempty] at h
    cases h with
    | tail _ hstep =>
      obtain ⟨e, he, _, _, _⟩ := hstep
      exact absurd he (by simp)










private def gc21_E4 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(2, 3), s(0, 3)}



private noncomputable def gc21_m4 : Ising.Current (Fin 4) :=
  fun e => if e = s(0, 1) then 1 else if e = s(2, 3) then 1 else if e = s(0, 3) then 2 else 0


private noncomputable def gc21_k4 : Ising.Current (Fin 4) := fun e => if e = s(0, 3) then 2 else 0


private noncomputable def gc21_m4k : Ising.Current (Fin 4) := fun e => gc21_m4 e - gc21_k4 e













theorem gc21_posFibre_not_of_posFull_sourceless :
    (∀ e, gc21_k4 e ≤ gc21_m4 e)
      ∧ Ising.sources gc21_E4 gc21_k4 = (∅ : Finset (Fin 4))
      ∧ Ising.sources gc21_E4 gc21_m4 = ({0, 1, 2, 3} : Finset (Fin 4))
      ∧ connP (posEdges gc21_E4 gc21_m4) 0 3
      ∧ ¬ connP (posEdges gc21_E4 gc21_m4k) 0 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e; unfold gc21_k4 gc21_m4; fin_cases e <;> simp_all
  · decide
  · decide
  · 
    refine Relation.ReflTransGen.single ⟨s(0, 3), ?_, by simp, by simp, by decide⟩
    rw [posEdges, Finset.mem_filter]
    refine ⟨by rw [gc21_E4]; simp, ?_⟩
    show 1 ≤ gc21_m4 s(0, 3)
    simp only [gc21_m4]; decide
  · 
    have hpos : posEdges gc21_E4 gc21_m4k = ({s(0, 1), s(2, 3)} : Finset (Sym2 (Fin 4))) := by
      decide
    intro h
    rw [hpos] at h
    have key : ∀ b : Fin 4, connP ({s(0, 1), s(2, 3)} : Finset (Sym2 (Fin 4))) 0 b →
        (b = 0 ∨ b = 1) := by
      intro b hb
      induction hb with
      | refl => left; rfl
      | tail _ hstep ih =>
        obtain ⟨e, he, ha, hbb, hne⟩ := hstep
        rw [Finset.mem_insert, Finset.mem_singleton] at he
        rcases ih with rfl | rfl <;> rcases he with rfl | rfl <;> simp_all
    rcases key 3 h with h3 | h3 <;> exact absurd h3 (by decide)









variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]














theorem gc21_fibre_posTrichotomy (m : ↥(withGhost G).edgeFinset → ℕ)
    (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e})
    (o x y g : Option V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))
        = ({o, x, y, g} : Finset (Option V))) :
    connP (posEdges (withGhost G).edgeFinset
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o g
      ∨ (connP (posEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o x
          ∧ connP (posEdges (withGhost G).edgeFinset
              (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) y g)
      ∨ (connP (posEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o y
          ∧ connP (posEdges (withGhost G).edgeFinset
              (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) x g) := by
  set n : ↥(withGhost G).edgeFinset → ℕ := fun e => m e - K₁.1 e with hn
  have hnle : n ≤ m := fun e => by have := K₁.2 e; simp only [hn]; omega
  set S : Finset (FluxEdgeCopy.Copy (withGhost G) m) :=
    univ.filter (fun i : FluxEdgeCopy.Copy (withGhost G) m => i.2.val < n i.1) with hS
  have hprof : profileFlux (withGhost G) m S = n := profileFlux_surj (withGhost G) m n hnle
  have hconnK : ∀ a b, connK (endsM (withGhost G) m) S a b ↔
      connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) n)) a b := by
    intro a b
    rw [connK_iff, hprof, ← gc20_connP_posEdges_iff_currentConnected]
  have hSsrc : sources (endsM (withGhost G) m) S = ({o, x, y, g} : Finset (Option V)) := by
    rw [sources_eq, hprof]; exact hbdry
  have htri := gc7_core_pathCrossing_trichotomy_edgeCopy (withGhost G) m S o x y g
    hox hoy hog hxy hxg hyg hSsrc
  rcases htri with h | h | h
  · left; exact (hconnK o g).mp h
  · right; left; exact ⟨(hconnK o x).mp h.1, (hconnK y g).mp h.2⟩
  · right; right; exact ⟨(hconnK o y).mp h.1, (hconnK x g).mp h.2⟩














theorem gc21_fibre_oddArc_of_sourcePair (m : ↥(withGhost G).edgeFinset → ℕ)
    (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}) {u v : Option V} (huv : u ≠ v)
    (hsrc : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) = {u, v}) :
    connP (oddEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) u v :=
  connOdd_of_sources (withGhost G).edgeFinset
    (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) (gc20_withGhost_loopless G) huv hsrc




















theorem gc21_oddArc_imp_posArc (n : ↥(withGhost G).edgeFinset → ℕ) {u v : Option V}
    (hodd : connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) n)) u v) :
    connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) n)) u v :=
  connOdd_imp_connPos (withGhost G).edgeFinset (ofEdgeFun (withGhost G) n) hodd


























def gc21_FibreOddArcBridge (m : ↥(withGhost G).edgeFinset → ℕ) : Prop :=
  ∀ (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}) (u v : Option V),
    connP (posEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) u v →
    connP (oddEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) u v






theorem gc21_allConn_oddArcs_of_bridge (m : ↥(withGhost G).edgeFinset → ℕ)
    (hbridge : gc21_FibreOddArcBridge G m)
    (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}) (o x y g : Option V)
    (hposOg : connP (posEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o g)
    (hposOx : connP (posEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o x)
    (hposOy : connP (posEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o y) :
    connP (oddEdges (withGhost G).edgeFinset
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o g
      ∧ connP (oddEdges (withGhost G).edgeFinset
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o x
      ∧ connP (oddEdges (withGhost G).edgeFinset
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o y :=
  ⟨hbridge K₁ o g hposOg, hbridge K₁ o x hposOx, hbridge K₁ o y hposOy⟩















theorem gc21_fibre_starGap_nonpos_of_bridge (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (m : ↥(withGhost G).edgeFinset → ℕ) (hbridge : gc21_FibreOddArcBridge G m)
    (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e})
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))
        = ({some o, some x, some y, none} : Finset (Option V))) :
    hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) ∅
      - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) {some o, none}
      - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) {some o, some x}
      - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) {some o, some y} ≤ 0 := by
  have hog : (some o : Option V) ≠ none := by simp
  have hoxs : (some o : Option V) ≠ some x := by simpa using hox
  have hoys : (some o : Option V) ≠ some y := by simpa using hoy
  have hxys : (some x : Option V) ≠ some y := by simpa using hxy
  have hxgs : (some x : Option V) ≠ none := by simp
  have hygs : (some y : Option V) ≠ none := by simp
  set fib := ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e) with hfib
  set J' := ghostCoupling h β (fun _ : Sym2 V => (1 : ℝ)) with hJ'
  have hJnn : ∀ e, (0 : ℝ) ≤ J' e := gc6_ghostCoupling_nonneg (V := V) β h hh
  have bg : 0 ≤ hnw_mass (withGhost G) β J' fib {some o, none} :=
    hnw_mass_nonneg (withGhost G) β J' hβ hJnn fib _
  have bx : 0 ≤ hnw_mass (withGhost G) β J' fib {some o, some x} :=
    hnw_mass_nonneg (withGhost G) β J' hβ hJnn fib _
  have by' : 0 ≤ hnw_mass (withGhost G) β J' fib {some o, some y} :=
    hnw_mass_nonneg (withGhost G) β J' hβ hJnn fib _
  have b0 : 0 ≤ hnw_mass (withGhost G) β J' fib ∅ :=
    hnw_mass_nonneg (withGhost G) β J' hβ hJnn fib _
  have collapse : ∀ (a : Option V), (some o : Option V) ≠ a →
      connP (oddEdges (withGhost G).edgeFinset fib) (some o) a →
      hnw_mass (withGhost G) β J' fib {some o, a} = hnw_mass (withGhost G) β J' fib ∅ := by
    intro a hoa Harc
    have := hnw_switching (withGhost G) β J' fib hoa Harc ∅
    rwa [show (∅ : Finset (Option V)) ∆ {some o, a} = {some o, a} from by simp] at this
  have htri := gc21_fibre_posTrichotomy G m K₁ (some o) (some x) (some y) none
    hoxs hoys hog hxys hxgs hygs hbdry
  rcases htri with hOg | hp1 | hp2
  · rw [collapse none hog (hbridge K₁ (some o) none hOg)]; linarith
  · rw [collapse (some x) hoxs (hbridge K₁ (some o) (some x) hp1.1)]; linarith
  · rw [collapse (some y) hoys (hbridge K₁ (some o) (some y) hp2.1)]; linarith


















theorem gc21_firstFour_nonpos_of_bridge (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (m : ↥(withGhost G).edgeFinset → ℕ) (hbridge : gc21_FibreOddArcBridge G m)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V))) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} ≤ 0 := by
  have hJnn : ∀ e, (0 : ℝ) ≤ ghostCoupling h β (fun _ => 1) e :=
    gc6_ghostCoupling_nonneg (V := V) β h hh
  rw [gc18_firstFour_reorg G β h o x y m]
  refine Finset.sum_nonpos (fun K₂ _ => ?_)
  by_cases hK₂ : sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅
  · rw [if_pos hK₂]
    have hw : (0 : ℝ) ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (ofEdgeFun (withGhost G) K₂.1) :=
      asd_weight_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1)) hβ hJnn _
    
    have hinner : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
        = ({some o, some x, some y, none} : Finset (Option V)) := by
      have hadd := sources_ofEdgeFun_add (withGhost G) m K₂.1 K₂.2
      rw [hbdry, hK₂] at hadd
      rw [show (∅ : Finset (Option V)) ∆
            sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
          = sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
          from symmDiff_eq_right.mpr rfl] at hadd
      exact hadd.symm
    have hsg := gc21_fibre_starGap_nonpos_of_bridge G β h hβ hh o x y m hbridge K₂
      hox hoy hxy hinner
    exact mul_nonpos_of_nonneg_of_nonpos hw hsg
  · rw [if_neg hK₂, zero_mul]

end StatMech.Walls
