/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Walls.gc83crosspairing
import Code.Walls.gc27polyineq

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

















noncomputable def gc84b_ghsResidual (c : Finset (Fin 4) → ℝ) : ℝ :=
  c {0, 3} * c {1, 2} + c {1, 3} * c {0, 2} + c {2, 3} * c {0, 1}
    - c {0, 1, 2, 3} - 2 * (c {0, 3} * c {1, 3} * c {2, 3})










def gc84b_GriffithsFamily (c : Finset (Fin 4) → ℝ) : Prop :=
  c ∅ = 1 ∧ (∀ S : Finset (Fin 4), 0 ≤ c S) ∧ (∀ A B : Finset (Fin 4), c A * c B ≤ c (A ∆ B))












noncomputable def gc84b_parityCorr (S : Finset (Fin 4)) : ℝ :=
  if S = ∅ ∨ S = Finset.univ then 1 else 0



theorem gc84b_parity_closed (A B : Finset (Fin 4))
    (hA : A = ∅ ∨ A = Finset.univ) (hB : B = ∅ ∨ B = Finset.univ) :
    A ∆ B = ∅ ∨ A ∆ B = Finset.univ := by
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · left; simp
  · right; simp
  · right; simp
  · left; simp


theorem gc84b_parityCorr_zero (S : Finset (Fin 4)) (h : S ≠ ∅ ∧ S ≠ Finset.univ) :
    gc84b_parityCorr S = 0 := by
  unfold gc84b_parityCorr; rw [if_neg]; rintro (h1 | h2)
  · exact h.1 h1
  · exact h.2 h2


theorem gc84b_parity_gks1 (S : Finset (Fin 4)) : 0 ≤ gc84b_parityCorr S := by
  unfold gc84b_parityCorr; split <;> norm_num





theorem gc84b_parity_gks2 (A B : Finset (Fin 4)) :
    gc84b_parityCorr A * gc84b_parityCorr B ≤ gc84b_parityCorr (A ∆ B) := by
  unfold gc84b_parityCorr
  by_cases hA : A = ∅ ∨ A = Finset.univ
  · by_cases hB : B = ∅ ∨ B = Finset.univ
    · rw [if_pos hA, if_pos hB, if_pos (gc84b_parity_closed A B hA hB)]; norm_num
    · rw [if_pos hA, if_neg hB]
      simp only [mul_zero, symmDiff_eq_empty]; positivity
  · rw [if_neg hA]
    simp only [mul_ite, mul_one, mul_zero, ite_self, symmDiff_eq_empty]; positivity




theorem gc84b_parity_griffiths : gc84b_GriffithsFamily gc84b_parityCorr := by
  refine ⟨?_, gc84b_parity_gks1, gc84b_parity_gks2⟩
  unfold gc84b_parityCorr; rw [if_pos (Or.inl rfl)]





theorem gc84b_parity_violates : gc84b_ghsResidual gc84b_parityCorr < 0 := by
  unfold gc84b_ghsResidual
  have h03 : gc84b_parityCorr {0, 3} = 0 := gc84b_parityCorr_zero _ (by decide)
  have h12 : gc84b_parityCorr {1, 2} = 0 := gc84b_parityCorr_zero _ (by decide)
  have h13 : gc84b_parityCorr {1, 3} = 0 := gc84b_parityCorr_zero _ (by decide)
  have h02 : gc84b_parityCorr {0, 2} = 0 := gc84b_parityCorr_zero _ (by decide)
  have h23 : gc84b_parityCorr {2, 3} = 0 := gc84b_parityCorr_zero _ (by decide)
  have h01 : gc84b_parityCorr {0, 1} = 0 := gc84b_parityCorr_zero _ (by decide)
  have huniv : ({0, 1, 2, 3} : Finset (Fin 4)) = Finset.univ := by decide
  have ht : gc84b_parityCorr {0, 1, 2, 3} = 1 := by
    rw [huniv]; unfold gc84b_parityCorr; rw [if_pos (Or.inr rfl)]
  rw [h03, h12, h13, h02, h23, h01, ht]; norm_num















def gc84b_GriffithsConsequence (P : (Finset (Fin 4) → ℝ) → ℝ) : Prop :=
  ∀ c : Finset (Fin 4) → ℝ, gc84b_GriffithsFamily c → 0 ≤ P c







theorem gc84b_nonneg_combination {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (gen : ι → ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (hgen : ∀ i ∈ s, 0 ≤ gen i) :
    0 ≤ ∑ i ∈ s, lam i * gen i :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (hlam i hi) (hgen i hi))










theorem gc84b_no_positivstellensatz : ¬ gc84b_GriffithsConsequence gc84b_ghsResidual := by
  intro hcons
  have hnn := hcons gc84b_parityCorr gc84b_parity_griffiths
  have hneg := gc84b_parity_violates
  linarith







theorem gc84b_griffithsFamily_insufficient :
    ∃ c : Finset (Fin 4) → ℝ,
      gc84b_GriffithsFamily c ∧ ¬ (0 ≤ gc84b_ghsResidual c) :=
  ⟨gc84b_parityCorr, gc84b_parity_griffiths, by have := gc84b_parity_violates; linarith⟩















theorem gc84b_griffiths_sound (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, some y}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some y}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) :=
  gc25_three_switchingGaps_nonneg G β h hβ hh o x y hox hoy hxy














theorem gc84b_residual_closes_ghs (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hpoly : gc27_GHSPolyIneq G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc27_polyIneq_closes_ghs G β h o x y hox hoy hxy hpoly






















theorem gc84b_directSOS_status :
    (gc84b_GriffithsFamily gc84b_parityCorr ∧ gc84b_ghsResidual gc84b_parityCorr < 0)
    ∧ ¬ gc84b_GriffithsConsequence gc84b_ghsResidual
    ∧ (∃ c : Finset (Fin 4) → ℝ, gc84b_GriffithsFamily c ∧ ¬ (0 ≤ gc84b_ghsResidual c)) :=
  ⟨⟨gc84b_parity_griffiths, gc84b_parity_violates⟩,
   gc84b_no_positivstellensatz,
   gc84b_griffithsFamily_insufficient⟩

end StatMech.Walls
