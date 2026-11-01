/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalOrbit

/-! Twenty-four coordinate lifts and the central involution generate the actual Q. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The positive lift of one of the fixed twenty-four binary coordinates. -/
def qCoordinateGenerator (i : Fin 24) : Q :=
  ⟨ofAdd (Pi.single i 1), 1⟩

/-- Its image is the corresponding coordinate vector. -/
theorem qCoordinateGenerator_binary (i : Fin 24) :
    qQuotHom (qCoordinateGenerator i) = ofAdd (Pi.single i 1) := rfl

/-- A subgroup containing the coordinate lifts has full binary image. -/
theorem qCoordinate_binaryImage_eq_top (K : Subgroup Q)
    (h : ∀ i : Fin 24, qCoordinateGenerator i ∈ K) : qSubgroupBinaryImage K = ⊤ := by
  apply top_unique
  intro v _
  rw [← Finset.univ_sum_single v]
  apply Submodule.sum_mem
  intro i _
  have hi : Pi.single i (1 : ZMod 2) ∈ qSubgroupBinaryImage K :=
    ⟨qCoordinateGenerator i, h i, rfl⟩
  have hs := (qSubgroupBinaryImage K).smul_mem (v i) hi
  have he : v i • Pi.single i (1 : ZMod 2) = Pi.single i (v i) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [he] at hs
  exact hs

/-- Adding the central involution gives the whole extraspecial group, including phases. -/
theorem qCoordinate_subgroup_eq_top (K : Subgroup Q)
    (h : ∀ i : Fin 24, qCoordinateGenerator i ∈ K)
    (hz : qCentralInvolution ∈ K) : K = ⊤ :=
  qSubgroup_eq_top_of_binaryImage_eq_top K (centerQ_le_of_central_mem K hz)
    (qCoordinate_binaryImage_eq_top K h)

/-- The twenty-five stated elements generate Q as a group. -/
theorem qCoordinate_closure_eq_top :
    Subgroup.closure (Set.range qCoordinateGenerator ∪ {qCentralInvolution}) = ⊤ := by
  apply qCoordinate_subgroup_eq_top
  · intro i
    exact Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  · exact Subgroup.subset_closure (Or.inr rfl)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
