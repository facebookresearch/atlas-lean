/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Ising.TwoReplica
import Code.Ising.TwoReplicaWeighted
import Code.Ising.AizenmanSignDominance
import Code.Ising.HdomNativeWeight
import Code.Ising.BackboneResummation

open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]






















theorem bse_surgery_of_inj_zeroAllMass (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (A : Finset V) (o x y : V)
    (ι : Current V → Current V)
    (hmem : ∀ m ∈ bbr_allFilter G M o x y, ι m ∈ bbr_noneFilter G M o x y)
    (hinj : ∀ m ∈ bbr_allFilter G M o x y, ∀ m' ∈ bbr_allFilter G M o x y, ι m = ι m' → m = m')
    (hzero : ∀ m ∈ bbr_allFilter G M o x y, hnw_mass G β J m A = 0) :
    bbr_BackboneSurgery G β J M A o x y := by
  refine ⟨ι, hmem, hinj, ?_⟩
  intro m hm
  rw [hzero m hm, mul_zero]
  exact bbr_mass_nonneg G β J hβ hJ (ι m) A







theorem bse_surgery_of_card_le_zeroAllMass (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Current V)) (A : Finset V) (o x y : V)
    (hcard : (bbr_allFilter G M o x y).card ≤ (bbr_noneFilter G M o x y).card)
    (hzero : ∀ m ∈ bbr_allFilter G M o x y, hnw_mass G β J m A = 0) :
    bbr_BackboneSurgery G β J M A o x y := by
  
  have hcard' : Fintype.card {m : Current V // m ∈ bbr_allFilter G M o x y}
      ≤ (bbr_noneFilter G M o x y).card := by
    rw [Fintype.card_coe]; exact hcard
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := {m : Current V // m ∈ bbr_allFilter G M o x y}) hcard'
  
  set ι : Current V → Current V :=
    fun m => if h : m ∈ bbr_allFilter G M o x y then (f ⟨m, h⟩ : Current V) else m with hι
  have hmem : ∀ m ∈ bbr_allFilter G M o x y, ι m ∈ bbr_noneFilter G M o x y := by
    intro m hm
    rw [hι]; simp only [dif_pos hm]
    exact hf (Set.mem_range_self _)
  have hinj : ∀ m ∈ bbr_allFilter G M o x y, ∀ m' ∈ bbr_allFilter G M o x y,
      ι m = ι m' → m = m' := by
    intro m hm m' hm' h
    rw [hι] at h; simp only [dif_pos hm, dif_pos hm'] at h
    exact congrArg Subtype.val (f.injective h)
  exact bse_surgery_of_inj_zeroAllMass G β J hβ hJ M A o x y ι hmem hinj hzero






theorem bse_surgery_satisfiable_via (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (A : Finset V) (o x y : V)
    (hno : bbr_allFilter G M o x y = ∅) :
    bbr_BackboneSurgery G β J M A o x y := by
  refine bse_surgery_of_card_le_zeroAllMass G β J hβ hJ M A o x y ?_ ?_
  · rw [hno]; exact Nat.zero_le _
  · intro m hm; rw [hno] at hm; simp at hm


















theorem bse_switching_fixes_m (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    {u v : V} (huv : u ≠ v) (hconn : connP (oddEdges G.edgeFinset m) u v) (A : Finset V) :
    hnw_mass G β J m (A ∆ {u, v}) = hnw_mass G β J m A :=
  hnw_switching G β J m huv hconn A












theorem bse_allMass_eq_self_paired (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hall : hnw_allConn G m o x y) :
    hnw_mass G β J m (A ∆ {x, y}) = hnw_mass G β J m A
      ∧ hnw_mass G β J m (A ∆ {o, y}) = hnw_mass G β J m A
      ∧ hnw_mass G β J m (A ∆ {o, x}) = hnw_mass G β J m A :=
  hnw_allMass_eq_paired G β J m A hox hoy hxy hall










theorem bse_selfPairing_doubling_forces_zero (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (m : Current V) (A : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hall : hnw_allConn G m o x y)
    (hself : 2 * hnw_mass G β J m A ≤ hnw_mass G β J m (A ∆ {x, y})) :
    hnw_mass G β J m A = 0 := by
  have hpair := (bse_allMass_eq_self_paired G β J m A hox hoy hxy hall).1
  have hnn := bbr_mass_nonneg G β J hβ hJ m A
  rw [hpair] at hself
  linarith















theorem bse_addBackbone_leaves_family (m : Current V) (A : Finset V) {x y : V} (_hxy : x ≠ y)
    (P : Finset (Sym2 V)) (hP : P ⊆ G.edgeFinset) (hsrcP : srcP P = {x, y})
    (hm : Sharpness.sources G m = A) :
    Sharpness.sources G (fun e => m e + (if e ∈ P then 1 else 0)) ≠ A := by
  rw [hnw_addBackbone_sources G m P hP, hsrcP, hm]
  
  intro hcontra
  exact Finset.insert_ne_empty x {y} (symmDiff_eq_left.mp hcontra)












theorem bse_addBackbone_weight_not_doubling (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) :
    Sharpness.weight G β J (fun e => m e + (if e ∈ (∅ : Finset (Sym2 V)) then 1 else 0))
      = Sharpness.weight G β J m := by
  rw [hnw_addBackbone_weight G β J m ∅]
  simp

end Ising

end StatMech
