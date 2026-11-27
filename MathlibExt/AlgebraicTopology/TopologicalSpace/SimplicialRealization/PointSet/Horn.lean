/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Subcomplex

/-!
# Closed inclusions and face ranges of realized horns

For every `n : ℕ`, `i : Fin (n+1)`, and universe `u`, the realization of the horn inclusion
`SSet.horn n i ⟶ Δ[n]` is a closed T1-embedding and hence a closed embedding. For the
positive-dimensional horn `Λ_k[n+1]`, its image in the realized standard simplex is the union
of the realized codimension-one faces with indices different from `k`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace SSet

namespace horn

/-- For `n : ℕ`, `i : Fin (n+1)`, and universe `u`,
`TopCat.closedT1Embeddings (SSet.toTop.{u}.map (SSet.horn.{u} n i).ι)`.
Thus `|Λ_i[n]| → |Δ[n]|` is a closed embedding satisfying the relative T1 condition. -/
theorem closedT1Embeddings_toTop_map_ι (n : ℕ) (i : Fin (n + 1)) :
    TopCat.closedT1Embeddings (SSet.toTop.{u}.map (SSet.horn.{u} n i).ι) :=
  SSet.closedT1Embeddings_toTop_map_of_mono _

/-- For `n : ℕ`, `i : Fin (n+1)`, and universe `u`,
`TopCat.closedEmbeddings (SSet.toTop.{u}.map (SSet.horn.{u} n i).ι)`.
The image of the realized horn inclusion is closed and the map identifies its domain with that subspace. -/
theorem closedEmbeddings_toTop_map_ι (n : ℕ) (i : Fin (n + 1)) :
    TopCat.closedEmbeddings (SSet.toTop.{u}.map (SSet.horn.{u} n i).ι) :=
  TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (closedT1Embeddings_toTop_map_ι n i)

/-- For `n : ℕ`, `k : Fin (n+2)`, and universe `u`, the image of `|Λ_k[n+1]| → |Δ[n+1]|` equals
`⋃ (j : Fin (n+2)) (_ : j≠k), Set.range (SSet.toTop.{u}.map (SSet.stdSimplex.face.{u} (n := n+1) {j}ᶜ).ι)`.
The union runs over exactly the codimension-one faces other than the missing `k`-th face. -/
theorem toTop_map_ι_range_eq_iUnion (n : ℕ) (k : Fin (n + 2)) :
    Set.range (SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) k).ι) =
      ⋃ (j : Fin (n + 2)) (_hj : j ≠ k),
        Set.range (SSet.toTop.{u}.map (SSet.stdSimplex.face.{u} (n := n + 1) {j}ᶜ).ι) := by
  let S := CategoryTheory.Limits.MultispanShape.ofLinearOrder ({k}ᶜ : Set (Fin (n + 2)))
  let DI : CategoryTheory.Limits.MultispanIndex S SSet.{u} :=
    ((SSet.horn.multicoequalizerDiagram k).multispanIndex.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor)
  let D : CategoryTheory.Limits.Cocone DI.multispan :=
    (SSet.horn.multicoequalizerDiagram k).multicofork.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor
  let c := SSet.toTop.{u}.mapCocone D
  have hc : CategoryTheory.Limits.IsColimit c :=
    CategoryTheory.Limits.isColimitOfPreserves SSet.toTop.{u} (SSet.horn.isColimit k)
  have hcType : CategoryTheory.Limits.IsColimit ((CategoryTheory.forget TopCat).mapCocone c) :=
    CategoryTheory.Limits.isColimitOfPreserves (CategoryTheory.forget TopCat) hc
  have hface : ∀ (j : Fin (n + 2)) (hj : j ≠ k),
      SSet.toTop.{u}.map (SSet.horn.faceι k j hj) ≫
        SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) k).ι =
        SSet.toTop.{u}.map (SSet.stdSimplex.face.{u} (n := n + 1) {j}ᶜ).ι := by
    intro j hj
    rw [← CategoryTheory.Functor.map_comp, SSet.horn.faceι_ι]
  have hleg : ∀ (b : S.R),
      c.ι.app (CategoryTheory.Limits.WalkingMultispan.right b) =
        SSet.toTop.{u}.map (SSet.horn.faceι k b.1 b.2) := by
    intro b
    have hD : D.ι.app (CategoryTheory.Limits.WalkingMultispan.right b) =
        SSet.horn.faceι k b.1 b.2 := by
      dsimp [D, S, CategoryTheory.Limits.MultispanShape.ofLinearOrder, SSet.horn.faceι]
      rfl
    have hcleg : c.ι.app (CategoryTheory.Limits.WalkingMultispan.right b) =
        SSet.toTop.{u}.map (D.ι.app (CategoryTheory.Limits.WalkingMultispan.right b)) := rfl
    rw [hcleg, hD]; rfl
  apply le_antisymm
  · intro y hy
    rw [Set.mem_range] at hy
    obtain ⟨x, hx⟩ := hy
    have hmem : ∀ (b : S.R) (w : SSet.toTop.obj
        (SSet.stdSimplex.face.{u} (n := n + 1) {b.1}ᶜ : SSet.{u})),
        c.ι.app (CategoryTheory.Limits.WalkingMultispan.right b) w = x →
        y ∈ ⋃ (j : Fin (n + 2)) (hj : j ≠ k),
          Set.range (SSet.toTop.{u}.map
            (SSet.stdSimplex.face.{u} (n := n + 1) {j}ᶜ).ι) := by
      intro b w hw
      refine Set.mem_iUnion.mpr ⟨b.1, Set.mem_iUnion.mpr ⟨b.2, Set.mem_range.mpr ⟨w, ?_⟩⟩⟩
      have e1 : SSet.toTop.{u}.map (SSet.stdSimplex.face.{u} (n := n + 1) {b.1}ᶜ).ι w =
          SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) k).ι
            (SSet.toTop.{u}.map (SSet.horn.faceι k b.1 b.2) w) := by
        have hcongr := CategoryTheory.ConcreteCategory.congr_hom (hface b.1 b.2) w
        rw [CategoryTheory.comp_apply] at hcongr
        exact hcongr.symm
      have e2 : SSet.toTop.{u}.map (SSet.horn.faceι k b.1 b.2) w =
          c.ι.app (CategoryTheory.Limits.WalkingMultispan.right b) w := by
        rw [← hleg b]; rfl
      rw [e1, e2, hw]
      exact hx
    obtain ⟨j, z, hz⟩ :=
      CategoryTheory.Limits.Types.jointly_surjective_of_isColimit hcType x
    cases j with
    | right b =>
      obtain ⟨w, hw⟩ : ∃ (w : SSet.toTop.obj
          (SSet.stdSimplex.face.{u} (n := n + 1) {b.1}ᶜ : SSet.{u})),
          c.ι.app (CategoryTheory.Limits.WalkingMultispan.right b) w = x := ⟨z, hz⟩
      exact hmem b w hw
    | left p =>
      have hz' : c.ι.app (CategoryTheory.Limits.WalkingMultispan.left p) z = x := hz
      have hEq := c.w (CategoryTheory.Limits.WalkingMultispan.Hom.fst p)
      have hEqz := CategoryTheory.ConcreteCategory.congr_hom hEq z
      rw [CategoryTheory.comp_apply] at hEqz
      exact hmem (S.fst p) _ (hEqz.trans hz')
  · refine Set.iUnion_subset fun j => Set.iUnion_subset fun hj => ?_
    intro w hw
    rw [Set.mem_range] at hw
    obtain ⟨z, hz⟩ := hw
    refine Set.mem_range.mpr ⟨SSet.toTop.{u}.map (SSet.horn.faceι k j hj) z, ?_⟩
    have e1 : SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) k).ι
          (SSet.toTop.{u}.map (SSet.horn.faceι k j hj) z) =
        SSet.toTop.{u}.map (SSet.stdSimplex.face.{u} (n := n + 1) {j}ᶜ).ι z := by
      have hcongr := CategoryTheory.ConcreteCategory.congr_hom (hface j hj) z
      rw [CategoryTheory.comp_apply] at hcongr
      exact hcongr
    rw [e1]
    exact hz

end horn

end SSet
