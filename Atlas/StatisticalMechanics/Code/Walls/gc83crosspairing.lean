/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Mathlib
import Code.Walls.gc82grahamgeometric

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














noncomputable def gc83_fam1 (β h : ℝ) (o x y : V) (m : ↥(withGhost G).edgeFinset → ℕ) : ℝ :=
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
    - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
    - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
    - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}





noncomputable def gc83_fam2 (β h : ℝ) (o x y : V) (m : ↥(withGhost G).edgeFinset → ℕ) : ℝ :=
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none}





def gc83_fourMark (o x y : V) (m : ↥(withGhost G).edgeFinset → ℕ) : Prop :=
  sources (withGhost G) (ofEdgeFun (withGhost G) m)
    = ({some o, some x, some y, none} : Finset (Option V))

noncomputable instance (o x y : V) (m : ↥(withGhost G).edgeFinset → ℕ) :
    Decidable (gc83_fourMark G o x y m) := Classical.dec _
















theorem gc83_threeGap_eq_fam (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ) :
    gc15_threeGap G β h o x y m
      = (if gc83_fourMark G o x y m then gc83_fam1 G β h o x y m + 2 * gc83_fam2 G β h o x y m
          else 0) := by
  obtain ⟨dOX, dOY, dOg, dXY, dXg, dYg⟩ := gc15_marks_distinct hox hoy hxy
  unfold gc15_threeGap gc83_fam1 gc83_fam2 gc83_fourMark
  
  unfold gc15_tFiber
  rw [gc15_sd0 (some o) (some x) (some y) none,
      gc15_sd1 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd2 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd3 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd4 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg]
  by_cases hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
      = ({some o, some x, some y, none} : Finset (Option V))
  · simp only [if_pos hm]
  · simp only [if_neg hm]; ring





theorem gc83_threeGap_zero_off_fourMark (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ) (hm : ¬ gc83_fourMark G o x y m) :
    gc15_threeGap G β h o x y m = 0 := by
  rw [gc83_threeGap_eq_fam G β h o x y hox hoy hxy m, if_neg hm]










theorem gc83_ghostCoupling_nonneg (β h : ℝ) (hh : 0 ≤ h) :
    ∀ e : Sym2 (Option V), 0 ≤ ghostCoupling h β (fun _ => (1 : ℝ)) e := by
  intro e
  refine Sym2.ind (fun a b => ?_) e
  match a, b with
  | some p, some q => simp
  | some p, none => simpa using hh
  | none, some q => simpa [ghostCoupling] using hh
  | none, none => simp [ghostCoupling]




theorem gc83_weight_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (n : Sharpness.Current (Option V)) :
    0 ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => (1 : ℝ))) n := by
  unfold weight
  refine Finset.prod_nonneg (fun e _ => ?_)
  exact div_nonneg
    (pow_nonneg (mul_nonneg hβ (gc83_ghostCoupling_nonneg (V := V) β h hh e)) _) (by positivity)






theorem gc83_fam2_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (m : ↥(withGhost G).edgeFinset → ℕ) :
    0 ≤ gc83_fam2 G β h o x y m := by
  unfold gc83_fam2 gc15_tpsum
  refine Finset.sum_nonneg (fun K _ => ?_)
  have h1 : 0 ≤ (if sources (withGhost G) (ofEdgeFun (withGhost G) K.1.1) = {some o, none}
        then weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) K.1.1)
        else 0) := by
    split
    · exact gc83_weight_nonneg G β h hβ hh _
    · exact le_refl 0
  have h2 : 0 ≤ (if sources (withGhost G) (ofEdgeFun (withGhost G) K.1.2) = {some x, none}
        then weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) K.1.2)
        else 0) := by
    split
    · exact gc83_weight_nonneg G β h hβ hh _
    · exact le_refl 0
  have h3 : 0 ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (ofEdgeFun (withGhost G) (fun e => m e - K.1.1 e - K.1.2 e)) :=
    gc83_weight_nonneg G β h hβ hh _
  exact mul_nonneg (mul_nonneg h1 h2) h3














def gc83_NetNonpos (β h : ℝ) (o x y : V) : Prop :=
  ∀ m : ↥(withGhost G).edgeFinset → ℕ, gc83_fourMark G o x y m →
    gc83_fam1 G β h o x y m + 2 * gc83_fam2 G β h o x y m ≤ 0





theorem gc83_netNonpos_iff_threeGapNonpos (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc83_NetNonpos G β h o x y ↔ gc82_ThreeGapNonpos G β h o x y := by
  unfold gc83_NetNonpos gc82_ThreeGapNonpos
  constructor
  · intro hnet m
    rw [gc83_threeGap_eq_fam G β h o x y hox hoy hxy m]
    by_cases hm : gc83_fourMark G o x y m
    · rw [if_pos hm]; exact hnet m hm
    · rw [if_neg hm]
  · intro hsign m hm
    have := hsign m
    rw [gc83_threeGap_eq_fam G β h o x y hox hoy hxy m, if_pos hm] at this
    exact this






theorem gc83_ursell_nonpos_of_netNonpos (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hnet : gc83_NetNonpos G β h o x y)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc82_ursell_nonpos G β h o x y hox hoy hxy
    ((gc83_netNonpos_iff_threeGapNonpos G β h o x y hox hoy hxy).1 hnet) hsupp

































abbrev gc83_MissingBijection (β h : ℝ) (o x y : V) : Prop :=
  gc83_NetNonpos G β h o x y







theorem gc83_ursell_nonpos_of_missingBijection (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbij : gc83_MissingBijection G β h o x y)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc83_ursell_nonpos_of_netNonpos G β h o x y hox hoy hxy hbij hsupp





















theorem gc83_crosspairing_status (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (∀ m : ↥(withGhost G).edgeFinset → ℕ,
        gc15_threeGap G β h o x y m
          = (if gc83_fourMark G o x y m
              then gc83_fam1 G β h o x y m + 2 * gc83_fam2 G β h o x y m else 0))
    ∧ (∀ m : ↥(withGhost G).edgeFinset → ℕ, 0 ≤ gc83_fam2 G β h o x y m)
    ∧ (gc83_NetNonpos G β h o x y ↔ gc82_ThreeGapNonpos G β h o x y) :=
  ⟨fun m => gc83_threeGap_eq_fam G β h o x y hox hoy hxy m,
   fun m => gc83_fam2_nonneg G β h hβ hh o x y m,
   gc83_netNonpos_iff_threeGapNonpos G β h o x y hox hoy hxy⟩

end StatMech.Walls
