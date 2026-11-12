/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































































import Mathlib
import Code.Walls.bc90boxopenforest
import Code.Walls.bc88genuinecount

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}















theorem bc91_upperLines_coarse_at_zero {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) :=
  bc89_coarse_target_faithful hL





theorem bc91_upperLines_not_genuine_at_zero :
    ¬ bc89_GenuineTrif 2 bc60_upperLines (0 : Site 2) :=
  bc89_upperLines_not_genuineTrif (0 : Site 2)





theorem bc91_coarse_notImp_genuine_at_zero {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧
    ¬ bc89_GenuineTrif 2 bc60_upperLines (0 : Site 2) :=
  ⟨bc91_upperLines_coarse_at_zero hL, bc91_upperLines_not_genuine_at_zero⟩










theorem bc91_coarse_imp_genuine_FALSE :
    ¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2),
        bc61_IsCoarseTrifurcation ω L y → bc89_GenuineTrif 2 ω y) := by
  intro h
  exact bc91_upperLines_not_genuine_at_zero
    (h bc60_upperLines 3 (0 : Site 2) (bc91_upperLines_coarse_at_zero (le_refl 3)))














theorem bc91_isTrif_not_genuine_at_zeroOne :
    IsTrifurcation 2 bc60_upperLines (bc57_pt 0 1) ∧
    ¬ bc89_GenuineTrif 2 bc60_upperLines (bc57_pt 0 1) :=
  ⟨bc88_upperLines_isTrifurcation, bc89_upperLines_not_genuineTrif (bc57_pt 0 1)⟩






theorem bc91_isTrif_imp_genuine_FALSE :
    ¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2),
        IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x) := by
  intro h
  exact (bc91_isTrif_not_genuine_at_zeroOne).2
    (h bc60_upperLines (bc57_pt 0 1) (bc91_isTrif_not_genuine_at_zeroOne).1)













theorem bc91_mem_boxAround_zero_scale {x v : Site d} :
    v ∈ bc61_boxAround d 0 x ↔ v = x := by
  rw [bc61_mem_boxAround, mem_box]
  constructor
  · intro h
    funext i
    have := h i
    have hx := sub_eq_zero.mp (Int.natAbs_eq_zero.mp (Nat.le_zero.mp this))
    simpa using hx
  · rintro rfl i; simp



theorem bc91_removeSites_boxZero_eq_removeSite (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites (bc61_boxAround d 0 x) ω = removeSite x ω := by
  funext e
  unfold removeSites removeSite
  by_cases hx : x ∈ e
  · rw [if_pos hx, if_pos ⟨x, by rw [bc91_mem_boxAround_zero_scale], hx⟩]
  · rw [if_neg hx, if_neg ?_]
    rintro ⟨t, ht, hte⟩
    rw [bc91_mem_boxAround_zero_scale] at ht
    exact hx (ht ▸ hte)







theorem bc91_genuine_imp_coarse_scale (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : bc89_GenuineTrif d ω x) : bc61_IsCoarseTrifurcation ω 0 x := by
  obtain ⟨a₁, a₂, a₃, _hne, _hnx, hadj, hinf, hsep⟩ := h
  have hxmem : x ∈ bc61_boxAround d 0 x := bc91_mem_boxAround_zero_scale.mpr rfl
  rw [bc61_IsCoarseTrifurcation]
  refine ⟨a₁, a₂, a₃, ⟨x, hxmem, hadj.1⟩, ⟨x, hxmem, hadj.2.1⟩, ⟨x, hxmem, hadj.2.2⟩, ?_, ?_⟩
  · rw [bc91_removeSites_boxZero_eq_removeSite]; exact hinf
  · rw [bc91_removeSites_boxZero_eq_removeSite]; exact hsep




















theorem bc91_hcanon_not_free :
    (¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2),
        bc61_IsCoarseTrifurcation ω L y → bc89_GenuineTrif 2 ω y)) ∧
    (¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2),
        IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x)) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2),
        bc89_GenuineTrif 2 ω x → bc61_IsCoarseTrifurcation ω 0 x) :=
  ⟨bc91_coarse_imp_genuine_FALSE, bc91_isTrif_imp_genuine_FALSE,
   fun ω x h => bc91_genuine_imp_coarse_scale ω x h⟩


















theorem bc91_as_residue (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (L : ℕ) (bdry : ℕ → ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc61_coarseTcount ω L R ≤ bdry R)
    (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
    (hdens : Filter.Tendsto
      (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0)) :
    μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 :=
  bc61_coarseTrif_prob_eq_zero μ L bdry hexp hbound hvol hdens







































theorem bc91_status :
    
    (¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2),
        bc61_IsCoarseTrifurcation ω L y → bc89_GenuineTrif 2 ω y)) ∧
    
    (∀ {L : ℕ}, 3 ≤ L →
      bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧
      ¬ bc89_GenuineTrif 2 bc60_upperLines (0 : Site 2)) ∧
    
    (¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2),
        IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2),
        bc89_GenuineTrif 2 ω x → bc61_IsCoarseTrifurcation ω 0 x) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ) (bdry : ℕ → ℕ),
      (∀ R : ℕ, ((boxFinsetBK 2 R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ) →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ), bc61_coarseTcount ω L R ≤ bdry R) →
      (∀ R, 0 < (boxFinsetBK 2 R).card) →
      Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK 2 R).card : ℝ)) Filter.atTop (nhds 0) →
      μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) := by
  refine ⟨bc91_coarse_imp_genuine_FALSE, ?_, bc91_isTrif_imp_genuine_FALSE,
    fun ω x h => bc91_genuine_imp_coarse_scale ω x h, ?_⟩
  · intro L hL; exact bc91_coarse_notImp_genuine_at_zero hL
  · intro μ _ L bdry hexp hbound hvol hdens
    exact bc91_as_residue μ L bdry hexp hbound hvol hdens

end StatMech.Walls
