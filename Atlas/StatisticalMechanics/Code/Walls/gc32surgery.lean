/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































































import Mathlib
import Code.Walls.gc31surgery
import Code.Walls.gc30reroute
import Code.Ising.BackboneResummation
import Code.Ising.HdomNativeWeight
import Code.Ising.HdomMultiplicity
import Code.Sharpness.Switching

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
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]














variable {ι : Type*} [DecidableEq ι] [Fintype ι]







theorem gc32_switch_card_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : RandomCurrent.sources ends m = A) {u v : V} (huv : u ≠ v)
    (hconn : RandomCurrent.connK ends m u v) :
    #(m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {u, v}))
      = #(m.powerset.filter (fun K => RandomCurrent.sources ends K = A)) := by
  rw [RandomCurrent.switching_card ends m hnd A hm huv, if_pos hconn]













theorem gc32_switch_bijOn (ends : ι → Sym2 V) (m P : Finset ι) (hP : P ⊆ m)
    {u v : V} (hPsrc : RandomCurrent.sources ends P = {u, v}) (A : Finset V) :
    Set.BijOn (fun K => K ∆ P)
      {K | K ⊆ m ∧ RandomCurrent.sources ends K = A}
      {K | K ⊆ m ∧ RandomCurrent.sources ends K = A ∆ {u, v}} := by
  have := RandomCurrent.sources_shift_bijOn ends m P hP A
  rwa [hPsrc] at this






theorem gc32_switch_card_disc (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : RandomCurrent.sources ends m = A) {u v : V} (huv : u ≠ v)
    (hdisc : ¬ RandomCurrent.connK ends m u v) :
    #(m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {u, v})) = 0 := by
  rw [RandomCurrent.switching_card ends m hnd A hm huv, if_neg hdisc]























theorem gc32_split_weight_cut_factor (β : ℝ) (J : Sym2 V → ℝ) (m n : Sharpness.Current V)
    (p : Sym2 V → Prop) [DecidablePred p] :
    Sharpness.weight G β J n * Sharpness.weight G β J (fun e => m e - n e)
      = (Sharpness.weight G β J (StatMech.Ising.restrictCut n p)
          * Sharpness.weight G β J (StatMech.Ising.restrictCut (fun e => m e - n e) p))
        * (Sharpness.weight G β J (StatMech.Ising.restrictCut n (fun e => ¬ p e))
          * Sharpness.weight G β J (StatMech.Ising.restrictCut (fun e => m e - n e) (fun e => ¬ p e))) := by
  rw [StatMech.Ising.bbr_weight_cut_factor G β J n p,
      StatMech.Ising.bbr_weight_cut_factor G β J (fun e => m e - n e) p]
  ring






theorem gc32_sources_cut_split (n : Sharpness.Current V) (p : Sym2 V → Prop) [DecidablePred p] :
    Sharpness.sources G n
      = Sharpness.sources G (StatMech.Ising.restrictCut n p)
        ∆ Sharpness.sources G (StatMech.Ising.restrictCut n (fun e => ¬ p e)) :=
  StatMech.Ising.bbr_sources_cut_split G n p





















theorem gc32_massDoubling_forces_zero (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m m' : Sharpness.Current V) (B : Finset V)
    (htarget : hnw_mass G β J m' B = 0)
    (hdoub : 2 * hnw_mass G β J m B ≤ hnw_mass G β J m' B) :
    hnw_mass G β J m B = 0 := by
  have hnn := hnw_mass_nonneg G β J hβ hJ m B
  rw [htarget] at hdoub
  linarith








theorem gc32_massDoubling_unsat_of_zero_targets (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V)
    (ma : Sharpness.Current V) (hma : ma ∈ bbr_allFilter G M o x y)
    (hpos : 0 < hnw_mass G β J ma B)
    (hzero : ∀ m' ∈ bbr_noneFilter G M o x y, hnw_mass G β J m' B = 0) :
    ¬ gc31_MassDoublingSurgery G β J M B o x y := by
  rintro ⟨Φ, hmem, _hinj, hdoub⟩
  have htgt : hnw_mass G β J (Φ ma) B = 0 := hzero (Φ ma) (hmem ma hma)
  have := gc32_massDoubling_forces_zero G β J hβ hJ ma (Φ ma) B htgt (hdoub ma hma)
  exact absurd this (ne_of_gt hpos)













theorem gc32_gap_nonneg_of_massDoubling (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Sharpness.Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (B : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = B) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (h : gc31_MassDoublingSurgery G β J M B o x y) :
    0 ≤ ∑ m ∈ M, hnw_gap G β J m B o x y :=
  gc31_native_gap_nonneg_of_massDoubling G β J hβ hJ M hnd B hm hox hoy hxy hcoh h

end StatMech.Walls
