/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Mathlib
import Code.Walls.gc38sharp

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
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]







open StatMech.Sharpness (currentSum)


noncomputable def gc39_allConnSum (β h : ℝ) (o x y : V) : ℝ :=
  gc38_sourcePairAllConnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
    ({some o, some x, some y, none} : Finset (Option V)) (some o) (some x) (some y) none



noncomputable def gc39_csTriple (β h : ℝ) (o x y : V) : ℝ :=
  currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, none} : Finset (Option V))
    * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some x, none} : Finset (Option V))
    * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some y, none} : Finset (Option V))





theorem gc39_sharpResidue_iff_allConn_ge_triple (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc38_SharpGHSResidue G β h o x y
      ↔ (gc15_Z0 G β h) ^ 2 * gc37_triple G β h o x y ≤ gc39_allConnSum G β h o x y := by
  unfold gc38_SharpGHSResidue gc39_allConnSum
  have hid := gc38_Z0sq_U4_eq_neg_two_allConn G β h hβ hh o x y hox hoy hxy
  have hZpos : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hZ2 : 0 < (gc15_Z0 G β h) ^ 2 := by positivity
  constructor
  · intro hres
    nlinarith [hid, hres, hZ2]
  · intro hle
    nlinarith [hid, hle, hZ2]





theorem gc39_sharpResidue_of_csTriple_le (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hdom : gc39_csTriple G β h o x y ≤ gc15_Z0 G β h * gc39_allConnSum G β h o x y) :
    gc38_SharpGHSResidue G β h o x y := by
  rw [gc39_sharpResidue_iff_allConn_ge_triple G β h hβ hh o x y hox hoy hxy]
  have htriple := gc37_Z0cubed_triple G β h o x y
  have hZpos : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  
  
  have hcs : gc39_csTriple G β h o x y = (gc15_Z0 G β h) ^ 3 * gc37_triple G β h o x y := by
    unfold gc39_csTriple
    rw [htriple]
    
    
    rw [gc15_gsingle o, gc15_gsingle x, gc15_gsingle y]
    rfl
  rw [hcs] at hdom
  
  have h2 : gc15_Z0 G β h * ((gc15_Z0 G β h) ^ 2 * gc37_triple G β h o x y)
      ≤ gc15_Z0 G β h * gc39_allConnSum G β h o x y := by nlinarith [hdom]
  exact le_of_mul_le_mul_left h2 hZpos















































def gc39_ThreeReplicaImprovedBound (β h : ℝ) (o x y : V) : Prop :=
  gc39_csTriple G β h o x y ≤ gc15_Z0 G β h * gc39_allConnSum G β h o x y



theorem gc39_sharpResidue_of_improvedBound (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc39_ThreeReplicaImprovedBound G β h o x y) :
    gc38_SharpGHSResidue G β h o x y :=
  gc39_sharpResidue_of_csTriple_le G β h hβ hh o x y hox hoy hxy hres



theorem gc39_ursell3_nonpos_of_improvedBound (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc39_ThreeReplicaImprovedBound G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc38_ursell3_nonpos_of_sharpResidue G β h o x y
    (gc39_sharpResidue_of_improvedBound G β h hβ hh o x y hox hoy hxy hres)






theorem gc39_improvedBound_iff_sharpResidue (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc39_ThreeReplicaImprovedBound G β h o x y ↔ gc38_SharpGHSResidue G β h o x y := by
  constructor
  · exact gc39_sharpResidue_of_improvedBound G β h hβ hh o x y hox hoy hxy
  · intro hsharp
    
    
    rw [gc39_sharpResidue_iff_allConn_ge_triple G β h hβ hh o x y hox hoy hxy] at hsharp
    unfold gc39_ThreeReplicaImprovedBound
    have htriple := gc37_Z0cubed_triple G β h o x y
    have hZpos : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
    have hcs : gc39_csTriple G β h o x y = (gc15_Z0 G β h) ^ 3 * gc37_triple G β h o x y := by
      unfold gc39_csTriple
      rw [htriple, gc15_gsingle o, gc15_gsingle x, gc15_gsingle y]; rfl
    rw [hcs]
    nlinarith [hsharp, hZpos, sq_nonneg (gc15_Z0 G β h)]













theorem gc39_improvedBound_at_zero (β : ℝ) (hβ : 0 ≤ β) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc39_ThreeReplicaImprovedBound G β 0 o x y :=
  (gc39_improvedBound_iff_sharpResidue G β 0 hβ le_rfl o x y hox hoy hxy).mpr
    (gc38_sharpResidue_at_zero G β o x y)





theorem gc39_improvedBound_sides_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    0 ≤ gc39_csTriple G β h o x y ∧ 0 ≤ gc15_Z0 G β h * gc39_allConnSum G β h o x y := by
  have hJnn : ∀ e, (0 : ℝ) ≤ ghostCoupling h β (fun _ => 1) e :=
    gc6_ghostCoupling_nonneg (V := V) β h hh
  have hZpos : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  refine ⟨?_, ?_⟩
  · unfold gc39_csTriple
    
    have hcs : ∀ A : Finset (Option V), (0 : ℝ) ≤ currentSum (withGhost G) β
        (ghostCoupling h β (fun _ => 1)) A := by
      intro A
      
      unfold currentSum
      refine tsum_nonneg (fun n => ?_)
      by_cases hs : StatMech.Sharpness.sources (withGhost G)
          (StatMech.Sharpness.ofEdgeFun (withGhost G) n) = A
      · simp only [hs, if_true]; exact acw_weight_nonneg (withGhost G) β _ hβ hJnn _
      · simp only [hs, if_false, le_refl]
    exact mul_nonneg (mul_nonneg (hcs _) (hcs _)) (hcs _)
  · refine mul_nonneg (le_of_lt hZpos) ?_
    exact gc38_sourcePairAllConnSum_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1))
      hβ hJnn ({some o, some x, some y, none} : Finset (Option V)) (some o) (some x) (some y) none
























open StatMech.Sharpness.RandomCurrent (sources connK)













def gc39_ThreeColouringCountIneq {ι W : Type*} [DecidableEq ι] [Fintype ι]
    [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (o x y g : W) : Prop :=
  #((univ : Finset (Finset ι × Finset ι)).filter (fun p : Finset ι × Finset ι =>
      p.2 ⊆ univ \ p.1
        ∧ sources ends p.1 = ({o, g} : Finset W)
        ∧ sources ends p.2 = ({x, g} : Finset W)
        ∧ sources ends ((univ \ p.1) \ p.2) = ({y, g} : Finset W)))
    ≤ #((univ : Finset (Finset ι × Finset ι)).filter (fun p : Finset ι × Finset ι =>
      p.2 ⊆ univ \ p.1
        ∧ sources ends p.1 = ({o, x, y, g} : Finset W)
        ∧ sources ends p.2 = (∅ : Finset W)
        ∧ sources ends ((univ \ p.1) \ p.2) = (∅ : Finset W)
        ∧ connK ends (p.1 ∪ p.2) o x ∧ connK ends (p.1 ∪ p.2) o y ∧ connK ends (p.1 ∪ p.2) o g))

end StatMech.Walls
