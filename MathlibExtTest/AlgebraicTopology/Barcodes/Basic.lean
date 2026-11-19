/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Paul Bendich
-/
module

public import MathlibExt.AlgebraicTopology.Barcodes.Basic

@[expose] public section

namespace MathlibExtTest.AlgebraicTopology.Barcodes.Basic

open MetaMathlibExt

-- Topology 667: Barcode

def infiniteBar (deg : ℕ) (b : ℝ) : PersistenceBar :=
  ⟨deg, b, ⊤, WithTop.coe_lt_top b⟩

def myBar : PersistenceBar := infiniteBar 0 0

lemma myBar_positive : (myBar.birth : WithTop ℝ) < myBar.death :=
  myBar.positive_length

-- Topology 668: Number of Bars at Specific Threshold

lemma barcodeRank_single (s t : ℝ) (hs : 0 ≤ s) :
    barcodeRank (Multiset.replicate 1 myBar) 0 s t = 1 := by
  classical
  unfold barcodeRank
  have hP : myBar.degree = 0 ∧ myBar.birth ≤ s ∧ (t : WithTop ℝ) < myBar.death :=
    ⟨rfl, hs, WithTop.coe_lt_top _⟩
  have hall : ∀ x ∈ Multiset.replicate 1 myBar,
      (fun b => b.degree = 0 ∧ b.birth ≤ s ∧ (t : WithTop ℝ) < b.death) x := by
    intro x hx
    have : x = myBar := (Multiset.mem_replicate.mp hx).2
    rw [this]
    exact hP
  rw [Multiset.filter_eq_self.mpr hall]
  simp

-- Topology 737: Bottleneck Distance between Barcodes

theorem bottleneckDist_le_cost {B C : Barcode} (M : Matching B C) :
    bottleneckDist B C ≤ M.cost := by
  unfold bottleneckDist
  exact sInf_le ⟨M, le_rfl⟩

-- Topology 739: Wasserstein Distance between Barcodes

theorem wassersteinDist_le_cost (p : ℝ) {B C : Barcode} (M : Matching B C) :
    wassersteinDist p B C ≤ M.wassersteinCost p := by
  unfold wassersteinDist
  exact sInf_le ⟨M, le_rfl⟩

end MathlibExtTest.AlgebraicTopology.Barcodes.Basic

end
