/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Mathlib
import Code.Walls.gc6_core
import Code.Walls.gc7core
import Code.Walls.gc8crossingallconn
import Code.Walls.gc8innereq15
import Code.Walls.gc8reinnerpair
import Code.Walls.gc8Z0pos
import Code.Walls.gc8munonneg
import Code.Walls.gc8fourmarks
import Code.Ising.CorrelationRatio
import Code.Ising.GKS2
import Code.Ising.GKS

open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]






















theorem gc8_core_claim1_lower_bound (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (y g : V) (eΛ : ℝ)
    (hgriff : Sharpness.expectationJ S β J ({y, g} : Finset V) ≤ eΛ) :
    eΛ * Sharpness.currentSum S β J ({y, g} : Finset V)
      ≥ (Sharpness.expectationJ S β J ({y, g} : Finset V)) ^ 2 * Sharpness.currentSum S β J ∅ :=
  gc8_inner_eq15_claim1_step S β J hβ hJ y g eΛ hgriff















theorem gc8_core_claim1_eqclaim_lower_bound (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (y g : V) (eΛ : ℝ)
    (hgriff : Sharpness.expectationJ S β J ({y, g} : Finset V) ≤ eΛ) :
    eΛ * Sharpness.currentSum S β J ({y, g} : Finset V)
      ≥ (Sharpness.currentSum S β J ({y, g} : Finset V)) ^ 2 / Sharpness.currentSum S β J ∅ := by
  have hstep := gc8_core_claim1_lower_bound S β J hβ hJ y g eΛ hgriff
  have hrepair := gc8r_reinner_pair_unconditional S β J ({y, g} : Finset V)
  rw [ge_iff_le, ← hrepair]
  exact hstep





theorem gc8_core_claim1_eqclaim_lower_bound_nonneg (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (y g : V) :
    0 ≤ (Sharpness.currentSum S β J ({y, g} : Finset V)) ^ 2 / Sharpness.currentSum S β J ∅ :=
  div_nonneg (sq_nonneg _) (gc8_inner_eq15_sourceless_pos S β J).le




theorem gc8_core_claim1_lower_bound_nonneg (S : SimpleGraph V) [DecidableRel S.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (y g : V) :
    0 ≤ (Sharpness.expectationJ S β J ({y, g} : Finset V)) ^ 2 * Sharpness.currentSum S β J ∅ :=
  mul_nonneg (sq_nonneg _) (Ising.acr_currentSum_nonneg S β J hβ hJ ∅)
















theorem gc8_core_claim1_normaliser_nonneg (GΛ GS : SimpleGraph V) [DecidableRel GΛ.Adj]
    [DecidableRel GS.Adj] (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y g : V)
    (Jghost : Sym2 (Option V) → ℝ) :
    0 ≤ isingExpectation GΛ β h (spinProd ({o, x, y, g} : Finset V))
        * (isingExpectation GΛ β h (spinProd ({y} : Finset V))) ^ 2
        * isingExpectation GS β h (spinProd ({o, x} : Finset V))
        * (Sharpness.currentSum (withGhost GΛ) β Jghost ∅) ^ 2 := by
  have hμ := gc8_mu_nonneg GΛ β h hβ hh o x y g
  have hox := gc8_twoPoint_nonneg GS β h hβ hh o x
  have hZ0 := (gc8_Z0_pos GΛ β Jghost).le
  positivity








variable {ι : Type*} [DecidableEq ι] [Fintype ι]











theorem gc8_core_delta_supported_allConn (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)
      = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)
        + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) :=
  (gc8_crossingAllConn ends F hox hoy hog hxy hxg hyg hnd hsrcSet).2.2.2






theorem gc8_core_crossing_forces_oneCluster (ends : ι → Sym2 V) (K : Finset ι) {o x y g w : V}
    (hox : connK ends K o x) (hyg : connK ends K y g)
    (hwo : connK ends K w o) (hwy : connK ends K w y) :
    connK ends K o x ∧ connK ends K o y ∧ connK ends K o g :=
  gc7_core_crossing_forces_oneCluster ends K hox hyg hwo hwy




















theorem gc8_core_delta_lower_bound_ghost (β : ℝ) (J : Sym2 (Option V) → ℝ) (A : Finset (Option V))
    (eΛ : ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hgriff : Sharpness.expectationJ (withGhost G) β J A ≤ eΛ) :
    eΛ * Sharpness.currentSum (withGhost G) β J A
        ≥ (Sharpness.expectationJ (withGhost G) β J A) ^ 2 * Sharpness.currentSum (withGhost G) β J ∅
      ∧ 0 ≤ (Sharpness.expectationJ (withGhost G) β J A) ^ 2
          * Sharpness.currentSum (withGhost G) β J ∅ :=
  ⟨gc8_claim1_griffiths_step_ghost G β J A eΛ hβ hJ hgriff,
   mul_nonneg (sq_nonneg _) (gc8_Z0_pos G β J).le⟩






theorem gc8_core_delta_lower_bound_ghost_nonneg (β : ℝ) (J : Sym2 (Option V) → ℝ)
    (A : Finset (Option V)) (eΛ : ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hgriff : Sharpness.expectationJ (withGhost G) β J A ≤ eΛ) :
    0 ≤ eΛ * Sharpness.currentSum (withGhost G) β J A := by
  obtain ⟨hge, hnn⟩ := gc8_core_delta_lower_bound_ghost G β J A eΛ hβ hJ hgriff
  exact le_trans hnn hge
















theorem gc8_core_pairSum_nonneg (ends : ι → Sym2 V) (A : Finset V) (F : Finset ι → ℝ)
    (P : Finset ι → Prop) (hF : ∀ m, 0 ≤ F m) :
    0 ≤ drd_pairSum ends A F P := by
  unfold drd_pairSum
  refine Finset.sum_nonneg (fun m _ => Finset.sum_nonneg (fun K _ => ?_))
  exact mul_nonneg (hF m) (by split <;> norm_num)













theorem gc8_core_delta_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag) (hF : ∀ m, 0 ≤ F m)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) := by
  rw [gc8_core_delta_supported_allConn ends F hox hoy hog hxy hxg hyg hnd hsrcSet]
  exact add_nonneg (gc8_core_pairSum_nonneg ends _ F _ hF) (gc8_core_pairSum_nonneg ends _ F _ hF)





























def gc8_PivotalSignBridge (β h : ℝ) (o : V) : Prop :=
  ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
    ∃ (D Z' : ℝ), (0 ≤ D) ∧ (0 < Z') ∧ eg_ursell3 G β h o x y * Z' = - D











theorem gc8_pivotalBridge_of_eqSwi (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hid : gc6_EqSwiIdentity G β h o) :
    gc8_PivotalSignBridge G β h o := by
  intro x y hox hoy hxy
  obtain ⟨J, μ, M, B, o', x', y', hβ', hJ, hμ, hox', hoy', hxy', hZpos, hident⟩ :=
    hid x y hox hoy hxy
  refine ⟨- (μ * egh_ensembleUrsell G β J M B o' x' y'), tcp_partitionFunction G β J M B,
    ?_, hZpos, ?_⟩
  · 
    rw [egh_ensemble_ursell_eq G β J M B hox' hoy' hxy']
    have hN : 0 ≤ tcp_allConnMass G β J M B o' x' y' :=
      tcp_allConnMass_nonneg G β J hβ' hJ M B o' x' y'
    nlinarith [hμ, hN]
  · rw [hident]; ring













theorem gc8_core_ursell_nonpos_distinct (β h : ℝ) (o : V)
    (hbr : gc8_PivotalSignBridge G β h o) (x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  obtain ⟨D, Z', hD, hZ, hid⟩ := hbr x y hox hoy hxy
  have hu : eg_ursell3 G β h o x y = - D / Z' := by
    rw [eq_div_iff (ne_of_gt hZ)]; linarith [hid]
  rw [hu]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hZ.le





theorem gc8_core_signDominance (β h : ℝ) (o : V)
    (hbr : gc8_PivotalSignBridge G β h o) :
    GHSSignDominance G β h o :=
  fun x y hox hoy hxy => gc8_core_ursell_nonpos_distinct G β h o hbr x y hox hoy hxy





theorem gc8_core_ursell_nonpos (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hbr : gc8_PivotalSignBridge G β h o) (x y : V) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc5_core_ursell_nonpos_of_signDominance G β h hβ hh o
    (gc8_core_signDominance G β h o hbr) x y




theorem gc8_core_ghs_concavity (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hbr : gc8_PivotalSignBridge G β h o) :
    GHSThreePointSym G β h o :=
  gc5_core_ghs_concavity_of_signDominance G β h hβ hh o
    (gc8_core_signDominance G β h o hbr)












theorem gc8_core_sharpness (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (Jc : ℝ)
    (hbr : gc8_PivotalSignBridge G β h o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = Jc * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ Jc * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc5_core_aizenman_barsky_of_signDominance G β h hβ hh o Jc
    (gc8_core_signDominance G β h o hbr) hfactor

















theorem gc8_core_bracket_surjective {μ t : ℝ} (hμ : 0 ≤ μ) (hlo : -2 * μ ≤ t) (hhi : t ≤ 0) :
    ∃ P : ℝ, 0 ≤ P ∧ P ≤ 1 ∧ -2 * μ * P = t :=
  gc6_core_bracket_surjective hμ hlo hhi







theorem gc8_core_pivotalBridge_iff_ursell_nonpos (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (∃ (D Z' : ℝ), (0 ≤ D) ∧ (0 < Z') ∧ eg_ursell3 G β h o x y * Z' = - D)
      ↔ eg_ursell3 G β h o x y ≤ 0 := by
  constructor
  · rintro ⟨D, Z', hD, hZ, hid⟩
    have hu : eg_ursell3 G β h o x y = - D / Z' := by
      rw [eq_div_iff (ne_of_gt hZ)]; linarith [hid]
    rw [hu]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hZ.le
  · intro hle
    exact ⟨- eg_ursell3 G β h o x y, 1, by linarith, one_pos, by ring⟩











theorem gc8_core_eqclaim_lower_bound_nonvacuous :
    0 ≤ (Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) 1 (fun _ => 1) ({1, 2} : Finset (Fin 4))) ^ 2
        / Sharpness.currentSum (⊥ : SimpleGraph (Fin 4)) 1 (fun _ => 1) ∅ :=
  gc8_core_claim1_eqclaim_lower_bound_nonneg (⊥ : SimpleGraph (Fin 4)) 1 (fun _ => 1) 1 2




theorem gc8_core_normaliser_nonneg_nonvacuous :
    0 ≤ isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1, 2, 0} : Finset (Fin 3)))
        * (isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({2} : Finset (Fin 3)))) ^ 2
        * isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1} : Finset (Fin 3)))
        * (Sharpness.currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1
            (ghostCoupling 1 1 (fun _ => 1)) ∅) ^ 2 :=
  gc8_core_claim1_normaliser_nonneg (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 3)) 1 1
    (by norm_num) (by norm_num) 0 1 2 0 (ghostCoupling 1 1 (fun _ => 1))






theorem gc8_core_pivotalBridge_degenerate (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (x y : V)
    (hxy : x ≠ y) :
    ∃ (D Z' : ℝ), (0 ≤ D) ∧ (0 < Z') ∧ eg_ursell3 G β h x x y * Z' = - D := by
  refine ⟨- eg_ursell3 G β h x x y, 1, ?_, one_pos, by ring⟩
  have hle : eg_ursell3 G β h x x y ≤ 0 := gc_ursell_nonpos_degenerate G β h hβ hh x y hxy
  linarith












theorem gc8_core_consistent (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hid : gc6_EqSwiIdentity G β h o) :
    gc8_PivotalSignBridge G β h o :=
  gc8_pivotalBridge_of_eqSwi G β h hβ hh o hid

end StatMech.Walls
