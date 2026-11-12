/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Walls.gc25resummation
import Code.Walls.gc24deltabridge
import Code.Walls.gc15core

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
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

















def gc27_GHSPolyIneq (β h : ℝ) (o x y : V) : Prop :=
  gc15_Z0 G β h * gc25_nativeAllConnMass G β h o x y
      + 2 * (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none}
          * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none}
          * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none})
    ≤ gc15_Z0 G β h
          * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x}
          * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none}
      + gc15_Z0 G β h
          * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some y}
          * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none}








theorem gc27_tsumThreeGap_nonpos_iff_polyIneq (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (∑' m, gc15_threeGap G β h o x y m) ≤ 0 ↔ gc27_GHSPolyIneq G β h o x y := by
  rw [gc25_threeGap_sum_decomp G β h o x y hox hoy hxy]
  unfold gc27_GHSPolyIneq
  constructor <;> intro hh <;> linarith [hh]





theorem gc27_ghs_iff_polyIneq (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 0 ↔ gc27_GHSPolyIneq G β h o x y := by
  have hZ : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  rw [← gc27_tsumThreeGap_nonpos_iff_polyIneq G β h o x y hox hoy hxy,
      ← gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy]
  constructor
  · intro hu; nlinarith [pow_pos hZ 3, hu]
  · intro hs; nlinarith [pow_pos hZ 3, hs]



theorem gc27_polyIneq_closes_ghs (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hpoly : gc27_GHSPolyIneq G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  (gc27_ghs_iff_polyIneq G β h o x y hox hoy hxy).mpr hpoly




theorem gc27_ghs_of_polyIneq (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hpoly : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc27_GHSPolyIneq G β h o x y) :
    GHSThreePointSym G β h o := by
  rw [ghc_ghsSym_iff_ursell_nonpos]
  intro x y he
  have hxy : x ≠ y := by rw [SimpleGraph.mem_edgeFinset] at he; exact G.ne_of_adj he
  by_cases hox : o = x
  · subst hox
    exact ghc_ursell_nonpos_degenerate G β h hβ hh o y hxy
  · by_cases hoy : o = y
    · subst hoy
      rw [ghc_ursell_swap]
      exact ghc_ursell_nonpos_degenerate G β h hβ hh o x hox
    · exact gc27_polyIneq_closes_ghs G β h o x y hox hoy hxy (hpoly x y hox hoy hxy)



theorem gc27_aizenman_barsky_of_polyIneq (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hpoly : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc27_GHSPolyIneq G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o J (gc27_ghs_of_polyIneq G β h hβ hh o hpoly) hfactor







theorem gc27_polyIneq_of_nativeResummation (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc25_NativeResummation G β h o x y) :
    gc27_GHSPolyIneq G β h o x y := by
  rw [← gc27_tsumThreeGap_nonpos_iff_polyIneq G β h o x y hox hoy hxy]
  have hN : 0 ≤ gc25_nativeAllConnMass G β h o x y :=
    gc25_nativeAllConnMass_nonneg G β h hβ hh o x y
  rw [hres]; nlinarith [hN]























def gc27_TwoSourceGapFamily (a b c r q p t : ℝ) : Prop :=
  
  (a * a ≤ 1 ∧ b * b ≤ 1 ∧ c * c ≤ 1 ∧ r * r ≤ 1 ∧ q * q ≤ 1 ∧ p * p ≤ 1 ∧ t * t ≤ 1)
  
  ∧ (a * b ≤ r ∧ a * c ≤ q ∧ b * c ≤ p)
  
  ∧ (a * p ≤ t ∧ b * q ≤ t ∧ c * r ≤ t)
  
  ∧ (a * q ≤ c ∧ a * r ≤ b ∧ b * p ≤ c ∧ b * r ≤ a ∧ c * p ≤ b ∧ c * q ≤ a)
  
  ∧ (a * t ≤ p ∧ b * t ≤ q ∧ c * t ≤ r)
  
  ∧ (p * q ≤ r ∧ p * r ≤ q ∧ q * r ≤ p)
  
  ∧ (p * t ≤ a ∧ q * t ≤ b ∧ r * t ≤ c)





theorem gc27_threeUsedGaps_in_family (a b c r q p t : ℝ)
    (hfam : gc27_TwoSourceGapFamily a b c r q p t) :
    a * p ≤ t ∧ b * q ≤ t ∧ c * r ≤ t :=
  hfam.2.2.1














theorem gc27_twoSourceGaps_insufficient :
    ∃ a b c r q p t : ℝ,
      gc27_TwoSourceGapFamily a b c r q p t
        ∧ ¬ (t + 2 * (a * b * c) ≤ a * p + b * q + c * r) := by
  refine ⟨0, 0, 0, 0, 0, 0, 1, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> norm_num
  · norm_num






theorem gc27_tripleBound_not_from_family :
    ∃ a b c r q p t : ℝ,
      gc27_TwoSourceGapFamily a b c r q p t
        ∧ ¬ (2 * (a * b * c) ≤ a * p + b * q + c * r - t) := by
  refine ⟨0, 0, 0, 0, 0, 0, 1, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> norm_num
  · norm_num














theorem gc27_three_switchingGaps_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, some y}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some y}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) :=
  gc25_three_switchingGaps_nonneg G β h hβ hh o x y hox hoy hxy









theorem gc27_obstruction_named (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc27_GHSPolyIneq G β h o x y ↔ eg_ursell3 G β h o x y ≤ 0)
      ∧ (gc25_NativeResummation G β h o x y → gc27_GHSPolyIneq G β h o x y)
      ∧ (∃ a b c r q p t : ℝ, gc27_TwoSourceGapFamily a b c r q p t
          ∧ ¬ (t + 2 * (a * b * c) ≤ a * p + b * q + c * r)) :=
  ⟨(gc27_ghs_iff_polyIneq G β h o x y hox hoy hxy).symm,
   gc27_polyIneq_of_nativeResummation G β h hβ hh o x y hox hoy hxy,
   gc27_twoSourceGaps_insufficient⟩

end StatMech.Walls
