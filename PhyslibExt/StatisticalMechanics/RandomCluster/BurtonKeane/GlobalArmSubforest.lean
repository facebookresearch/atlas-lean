/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Filter.Defs
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GnSpanningTreeRay
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmSubforestCount

/-!
# Arm subforests of the contracted lattice

An arm subforest of the contracted lattice for every configuration gives uniqueness for Bernoulli
percolation in the plane.

## i. Overview

`bfin_SuperCutBridge` asks that every contracted-lattice trifurcation have three neighbours in the
coarse graph `bgn_Gn` that are pairwise disconnected after the trifurcation is deleted.
`bfin_GlobalArmForest` is the arm subforest data `bau_ArmSubforestData`, which implies the global
contracted forest and hence the coarse counting bound.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bfin_status` : the statements together

## iii. Table of contents

- A. Results
- B. Summary

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation


/-! ## A. Results -/

lemma bfin_datum_of_noTrif (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (hR : 1 ≤ R)
    (hno : ∀ y, y ∈ box 2 R → ¬ bc67_IsGnTrifurcation ω L y) :
    bau_ArmSubforestData ω L R := by
  classical
  set p : Site 2 := ![(R:ℤ), 0] with hp
  set q : Site 2 := ![(-(R:ℤ)), 0] with hq
  have hpq : p ≠ q := by
    intro h; have := congrFun h 0; simp only [hp, hq, Matrix.cons_val_zero] at this; omega
  have hpbd : p ∈ vertexBoundary 2 R := by
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i <;> simp [hp, Int.natAbs_natCast]
    · intro h; have := h 0; simp only [hp, Matrix.cons_val_zero, Int.natAbs_natCast] at this; omega
  have hqbd : q ∈ vertexBoundary 2 R := by
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i <;> simp [hq, Int.natAbs_neg, Int.natAbs_natCast]
    · intro h; have := h 0; simp only [hq, Matrix.cons_val_zero, Int.natAbs_neg, Int.natAbs_natCast] at this; omega
  set S : Set (Site 2) := {p, q} with hS
  have hSfin : Fintype ↑S := ((Set.finite_singleton q).insert p).fintype
  have hpS : p ∈ S := by left; rfl
  have hqS : q ∈ S := by right; rfl
  have hSne : Nonempty ↑S := ⟨⟨p, hpS⟩⟩
  have hmemBd : ∀ v : ↑S, (v : Site 2) ∈ vertexBoundary 2 R := by
    rintro ⟨v, hv⟩
    rcases hv with hvp | hvq
    · simpa [hvp] using hpbd
    · simp only [Set.mem_singleton_iff] at hvq; simpa [hvq] using hqbd
  refine ⟨S, hSfin, hSne, (⊤ : SimpleGraph ↑S), (⊤ : SimpleGraph ↑S), (⊤ : SimpleGraph ↑S),
    (inferInstance : DecidableRel (⊤ : SimpleGraph ↑S).Adj), (fun _ => ⟨p, hpS⟩),
    connected_top, le_rfl, ⟨connected_top, ?_⟩, le_rfl, ?_, ?_, ?_, ?_⟩
  · apply IsAcyclic.of_card_le_two
    rw [ENat.card_coe_set_eq, hS, Set.encard_pair hpq]
  · intro v
    obtain ⟨w, hw⟩ : ∃ w : ↑S, (⊤ : SimpleGraph ↑S).Adj v w := by
      rcases v with ⟨v, hv⟩
      rcases hv with hvp | hvq
      · exact ⟨⟨q, hqS⟩, by rw [SimpleGraph.top_adj]; intro h; apply hpq; rw [← hvp]; exact congrArg Subtype.val h⟩
      · simp only [Set.mem_singleton_iff] at hvq
        exact ⟨⟨p, hpS⟩, by rw [SimpleGraph.top_adj]; intro h; apply hpq; rw [← hvq]; exact (congrArg Subtype.val h).symm⟩
    have hne : ((⊤ : SimpleGraph ↑S).neighborFinset v).Nonempty :=
      ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).mpr hw⟩
    exact Finset.Nonempty.card_pos hne
  · intro y hy htri; exact absurd htri (hno y hy)
  · intro y hy htri; exact absurd htri (hno y hy)
  · intro v hv; exact absurd (hmemBd v) hv


/-- Every contracted-lattice trifurcation has three coarse neighbours that are pairwise disconnected
after it is deleted. -/
def bfin_SuperCutBridge (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) : Prop :=
  ∀ y : Site 2, bc67_IsGnTrifurcation ω L y →
    ∃ w₁ w₂ w₃ : Site 2,
      w₁ ≠ bgn_idx L y ∧ w₂ ≠ bgn_idx L y ∧ w₃ ≠ bgn_idx L y ∧
      (bgn_Gn ω L).Adj (bgn_idx L y) w₁ ∧ (bgn_Gn ω L).Adj (bgn_idx L y) w₂ ∧
      (bgn_Gn ω L).Adj (bgn_idx L y) w₃ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₁ w₂ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₁ w₃ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₂ w₃ ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₁).Infinite ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₂).Infinite ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₃).Infinite

/-- Arm subforest data on the contracted lattice for box size `L` and box `B_R`. -/
def bfin_GlobalArmForest (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) : Prop :=
  bau_ArmSubforestData ω L R

lemma bfin_bk_of_globalArmForest (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bfin_GlobalArmForest ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bau_bk_of_subforestData p hp1 hp0 hdata

/-! ## B. Summary -/

lemma bfin_status :
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧
    (∀ {V : Type} {T G : SimpleGraph V}, T.IsAcyclic → G ≤ T → G.IsAcyclic) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), 1 ≤ R →
      (∀ y, y ∈ box 2 R → ¬ bc67_IsGnTrifurcation ω L y) → bau_ArmSubforestData ω L R) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp1 hp0 hdata; exact bau_bk_of_subforestData p hp1 hp0 hdata
  · intro V T G hT hle; exact bau_isAcyclic_of_le_acyclic hT hle
  · intro ω L R hR hno; exact bfin_datum_of_noTrif ω L R hR hno
  · intro ω L R h; exact bca_datum_implies_count ω L R h

end StatMech.Walls
