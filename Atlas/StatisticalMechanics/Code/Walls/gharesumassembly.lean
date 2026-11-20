/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Walls.gh9switchrearrange
import Code.Walls.gh7resum
import Code.Sharpness.MultiReplica

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

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]




























theorem gha_poly_resum (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y
      = ∑' m : ↥(withGhost G).edgeFinset → ℕ, gc15_threeGap G β h o x y m :=
  gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy













theorem gha_poly_resum_check (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (m : ↥(withGhost G).edgeFinset → ℕ)
    (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V))) :
    gc15_threeGap G β h o x y m
      = (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ)
          * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) :=
  gc85b_gc15_threeGap_eq_count G β h o x y hox hoy hxy m hm
















theorem gha_perm_rearrange {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (heq22 : gh7_perSuperposition_eq22 ends m o x y g) :
    (gc85b_threeGapCount ends m o x y g : ℝ) ≤ 0 :=
  gh7_perSuperposition_count_nonpos_of_eq22 ends m o x y g heq22






theorem gha_perm_sign_iff_bijection {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc85b_threeGapCount ends m o x y g ≤ 0
      ↔ gc85b_ThreeCurrentBijection ends m o x y g :=
  gc85b_threeGapCount_nonpos_iff_bijection ends m o x y g























theorem gha_weighted_eq22_of_ghs {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W)
    (hghs : eg_ursell3 G β h o x y ≤ 0) :
    gh8_weighted_eq22 G β h o x y ends m u u' := by
  refine ⟨eg_ursell3 G β h o x y, ∅, ∅, ∅, ∅,
    (fun _ => 0), (fun _ => 0), (fun _ => 0), (fun _ => 0),
    (fun _ => le_refl 0), (fun _ => le_refl 0), (fun _ => le_refl 0), (fun _ => le_refl 0),
    ?_, hghs⟩
  simp




theorem gha_ghs_of_weighted_eq22 {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W)
    (heq22 : gh8_weighted_eq22 G β h o x y ends m u u') :
    eg_ursell3 G β h o x y ≤ 0 :=
  gh8_ghs_of_weighted_eq22 G β h o x y ends m u u' heq22









theorem gha_weighted_eq22_iff {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W) :
    gh8_weighted_eq22 G β h o x y ends m u u' ↔ eg_ursell3 G β h o x y ≤ 0 :=
  ⟨gha_ghs_of_weighted_eq22 G β h o x y ends m u u',
   gha_weighted_eq22_of_ghs G β h o x y ends m u u'⟩

















theorem gha_ghs_of_bijection (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbij : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
        sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
        gc85b_ThreeCurrentBijection (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc85b_ursell_nonpos_of_bijection G β h hβ hh o x y hox hoy hxy hbij hsupp

















































theorem gha_status : True := trivial

end StatMech.Walls
