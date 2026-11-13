/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Mathlib
import Code.Walls.gc39threereplica
import Code.Walls.gc25resummation

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
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]














theorem gc80_sharpResidue_iff_ghs (β h : ℝ) (o x y : V) :
    gc38_SharpGHSResidue G β h o x y ↔ eg_ursell3 G β h o x y ≤ 0 := by
  rw [gc38_SharpGHSResidue, ← gc37_ursell3_nonpos_iff_sharp]








theorem gc80_routeA_residue_iff_ghs (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc39_ThreeReplicaImprovedBound G β h o x y ↔ eg_ursell3 G β h o x y ≤ 0 := by
  constructor
  · exact gc39_ursell3_nonpos_of_improvedBound G β h hβ hh o x y hox hoy hxy
  · intro hu3
    have hsharp : gc38_SharpGHSResidue G β h o x y := (gc80_sharpResidue_iff_ghs G β h o x y).mpr hu3
    exact (gc39_improvedBound_iff_sharpResidue G β h hβ hh o x y hox hoy hxy).mpr hsharp











theorem gc80_routeB_closes_ghs (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc25_NativeResummation G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc25_ursell_nonpos_of_nativeResummation G β h hβ hh o x y hox hoy hxy hres







theorem gc80_routeB_closes_routeA (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc25_NativeResummation G β h o x y) :
    gc39_ThreeReplicaImprovedBound G β h o x y :=
  (gc80_routeA_residue_iff_ghs G β h hβ hh o x y hox hoy hxy).mpr
    (gc80_routeB_closes_ghs G β h hβ hh o x y hox hoy hxy hres)





theorem gc80_routeB_is_identity (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc25_NativeResummation G β h o x y
      ↔ (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y
          = -2 * gc25_nativeAllConnMass G β h o x y := by
  unfold gc25_NativeResummation
  rw [gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy]











theorem gc80_routeA_closes_ghsSym (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc39_ThreeReplicaImprovedBound G β h o x y) :
    GHSThreePointSym G β h o := by
  rw [ghc_ghsSym_iff_ursell_nonpos]
  intro x y he
  have hxy : x ≠ y := by rw [SimpleGraph.mem_edgeFinset] at he; exact G.ne_of_adj he
  by_cases hox : o = x
  · subst hox; exact ghc_ursell_nonpos_degenerate G β h hβ hh o y hxy
  · by_cases hoy : o = y
    · subst hoy; rw [ghc_ursell_swap]; exact ghc_ursell_nonpos_degenerate G β h hβ hh o x hox
    · exact (gc80_routeA_residue_iff_ghs G β h hβ hh o x y hox hoy hxy).mp (hres x y hox hoy hxy)



theorem gc80_routeB_closes_ghsSym (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc25_NativeResummation G β h o x y) :
    GHSThreePointSym G β h o :=
  gc25_ghs_of_nativeResummation G β h hβ hh o hres











theorem gc80_routeA_ghs_at_zero (β : ℝ) (hβ : 0 ≤ β) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc39_ThreeReplicaImprovedBound G β 0 o x y ∧ eg_ursell3 G β 0 o x y ≤ 0 := by
  have hA : gc39_ThreeReplicaImprovedBound G β 0 o x y :=
    gc39_improvedBound_at_zero G β hβ o x y hox hoy hxy
  exact ⟨hA, (gc80_routeA_residue_iff_ghs G β 0 hβ le_rfl o x y hox hoy hxy).mp hA⟩



















theorem gc80_bookroute_status (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    (∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
        (gc39_ThreeReplicaImprovedBound G β h o x y ↔ eg_ursell3 G β h o x y ≤ 0))
    ∧ (∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
        gc25_NativeResummation G β h o x y → eg_ursell3 G β h o x y ≤ 0)
    ∧ (∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
        gc25_NativeResummation G β h o x y → gc39_ThreeReplicaImprovedBound G β h o x y)
    ∧ ((∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc39_ThreeReplicaImprovedBound G β h o x y)
        → GHSThreePointSym G β h o)
    ∧ ((∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc25_NativeResummation G β h o x y)
        → GHSThreePointSym G β h o) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun x y hox hoy hxy => gc80_routeA_residue_iff_ghs G β h hβ hh o x y hox hoy hxy
  · exact fun x y hox hoy hxy hres => gc80_routeB_closes_ghs G β h hβ hh o x y hox hoy hxy hres
  · exact fun x y hox hoy hxy hres => gc80_routeB_closes_routeA G β h hβ hh o x y hox hoy hxy hres
  · exact fun hres => gc80_routeA_closes_ghsSym G β h hβ hh o hres
  · exact fun hres => gc80_routeB_closes_ghsSym G β h hβ hh o hres

end StatMech.Walls
