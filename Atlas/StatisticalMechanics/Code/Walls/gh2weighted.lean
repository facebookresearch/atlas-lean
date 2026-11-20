/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Mathlib
import Code.Sharpness.MultiReplica
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc85bthreereplicaswitch
import Code.Walls.gc86brerouteinjection
import Code.Walls.gc87brerouteinjection
import Code.Walls.gc99consolidation
import Code.Walls.ghggrahamclose
import Code.Ising.GKS
import Code.Ising.GKS2

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {W : Type*} [DecidableEq W] [Fintype W]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]




















theorem gh2_weight_uniform_per_superposition (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (m : ↥(withGhost G).edgeFinset → ℕ)
    (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V))) :
    gc15_threeGap G β h o x y m
      = (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ)
        * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) :=
  gc85b_gc15_threeGap_eq_count G β h o x y hox hoy hxy m hm




theorem gh2_weight_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (m : ↥(withGhost G).edgeFinset → ℕ) :
    0 ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) :=
  gc83_weight_nonneg G β h hβ hh _












theorem gh2_weighted_sign_of_count (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (m : ↥(withGhost G).edgeFinset → ℕ)
    (hcount : sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
        gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none ≤ 0) :
    gc15_threeGap G β h o x y m ≤ 0 := by
  by_cases hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
      = ({some o, some x, some y, none} : Finset (Option V))
  · rw [gh2_weight_uniform_per_superposition G β h o x y hox hoy hxy m hm]
    have hc : (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ) ≤ 0 := by
      exact_mod_cast hcount hm
    have hw := gh2_weight_nonneg G β h hβ hh m
    nlinarith [hc, hw]
  · exact le_of_eq (gc15_threeGap_vanish G β h o x y hox hoy hxy m hm)


















theorem gh2_eq21_weighted_sign (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (m : ↥(withGhost G).edgeFinset → ℕ)
    (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V))) :
    
    (gc15_threeGap G β h o x y m
      = (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ)
        * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m))
    
    ∧ (#((({some x, some y, none} : Finset (Option V))).filter
          (fun w => connK (endsM (withGhost G) m) univ (some o) w)) = 1
        ∨ #((({some x, some y, none} : Finset (Option V))).filter
          (fun w => connK (endsM (withGhost G) m) univ (some o) w)) = 3) := by
  refine ⟨gh2_weight_uniform_per_superposition G β h o x y hox hoy hxy m hm, ?_⟩
  
  have hOX : (some o : Option V) ≠ some x := by simp [hox]
  have hOY : (some o : Option V) ≠ some y := by simp [hoy]
  have hOg : (some o : Option V) ≠ none := by simp
  have hXY : (some x : Option V) ≠ some y := by simp [hxy]
  have hXg : (some x : Option V) ≠ none := by simp
  have hYg : (some y : Option V) ≠ none := by simp
  have hnd : ∀ i ∈ (univ : Finset (Copy (withGhost G) m)), ¬ (endsM (withGhost G) m i).IsDiag :=
    fun i _ => endsM_not_isDiag (withGhost G) m i
  have hsrcU : sources (endsM (withGhost G) m) (univ : Finset (Copy (withGhost G) m))
      = ({some o, some x, some y, none} : Finset (Option V)) := by
    rw [sources_eq, profileFlux_univ]; exact hm
  exact ghg_one_or_three (endsM (withGhost G) m) univ hnd hsrcU hOX hOY hOg hXY hXg hYg














theorem gh2_lemma2_weighted (ends : ι → Sym2 W) (m : Finset ι) (A B : Finset W)
    {u v : W} (huv : u ≠ v) (P : Finset ι) (hPm : P ⊆ m) (hPsrc : sources ends P = {u, v}) :
    #((m.powerset ×ˢ m.powerset).filter
        (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P
          ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B ∆ {u, v}))
      = #((m.powerset ×ˢ m.powerset).filter
        (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P
          ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B)) :=
  gc85b_pcount_reroute_eq ends m A B huv P hPm hPsrc





theorem gh2_lemma1_weighted (G' : SimpleGraph V) [DecidableRel G'.Adj] (β h : ℝ) (hβ : 0 ≤ β)
    (i j k : V) :
    StatMech.Ising.cov2 G' β h i j * StatMech.Ising.cov2 G' β h j k
      ≤ StatMech.Walls.VBG.vbg_var (StatMech.Ising.isingProb G' β h)
          (fun s => StatMech.Ising.spin s j) * StatMech.Ising.cov2 G' β h i k :=
  ghg_lemma1_is_vbg G' β h hβ i j k













theorem gh2_gks_ingredient_available (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A B : Finset V) :
    StatMech.Ising.isingExpectation G β h (StatMech.Ising.spinProd A)
        * StatMech.Ising.isingExpectation G β h (StatMech.Ising.spinProd B)
      ≤ StatMech.Ising.isingExpectation G β h (StatMech.Ising.spinProd (A ∆ B)) :=
  StatMech.Ising.gks_second G β h hβ hh A B















theorem gh2_bridge_count_to_weighted (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (m : ↥(withGhost G).edgeFinset → ℕ)
    (hres : sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
        gc87b_CogxgLeT3 (endsM (withGhost G) m) univ (some o) (some x) (some y) none) :
    gc15_threeGap G β h o x y m ≤ 0 := by
  have hOX : (some o : Option V) ≠ some x := by simp [hox]
  have hOY : (some o : Option V) ≠ some y := by simp [hoy]
  have hOg : (some o : Option V) ≠ none := by simp
  refine gh2_weighted_sign_of_count G β h hβ hh o x y hox hoy hxy m ?_
  intro hm
  
  have hnd : ∀ i ∈ (univ : Finset (Copy (withGhost G) m)), ¬ (endsM (withGhost G) m i).IsDiag :=
    fun i _ => endsM_not_isDiag (withGhost G) m i
  have hsrcU : sources (endsM (withGhost G) m) (univ : Finset (Copy (withGhost G) m))
      = ({some o, some x, some y, none} : Finset (Option V)) := by
    rw [sources_eq, profileFlux_univ]; exact hm
  
  have hbij : gc85b_ThreeCurrentBijection (endsM (withGhost G) m) univ (some o) (some x) (some y) none :=
    gc99_minimal_residue (endsM (withGhost G) m) univ hnd hsrcU hOX hOY hOg (hres hm)
  exact gc85b_threeGapCount_nonpos_of_bijection _ _ _ _ _ _ hbij










theorem gh2_graham_cor3_via_count (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
        sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
        gc87b_CogxgLeT3 (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  have hsign : gc82_ThreeGapNonpos G β h o x y := fun m =>
    gh2_bridge_count_to_weighted G β h hβ hh o x y hox hoy hxy m (hres m)
  exact gc82_ursell_nonpos G β h o x y hox hoy hxy hsign hsupp



















theorem gh2_route_A_verdict (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    
    (∀ m : ↥(withGhost G).edgeFinset → ℕ,
        sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
        gc15_threeGap G β h o x y m
          = (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ)
            * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m))
    
    ∧ (∀ m : ↥(withGhost G).edgeFinset → ℕ,
        0 ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m))
    
    ∧ ((∀ m : ↥(withGhost G).edgeFinset → ℕ,
          sources (withGhost G) (ofEdgeFun (withGhost G) m)
            = ({some o, some x, some y, none} : Finset (Option V)) →
          gc87b_CogxgLeT3 (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
        → gc82_ThreeGapAllConnSupported G β h o x y
        → eg_ursell3 G β h o x y ≤ 0) :=
  ⟨fun m hm => gh2_weight_uniform_per_superposition G β h o x y hox hoy hxy m hm,
   fun m => gh2_weight_nonneg G β h hβ hh m,
   fun hres hsupp => gh2_graham_cor3_via_count G β h hβ hh o x y hox hoy hxy hres hsupp⟩
































theorem gh2_status : True := trivial

end StatMech.Walls
