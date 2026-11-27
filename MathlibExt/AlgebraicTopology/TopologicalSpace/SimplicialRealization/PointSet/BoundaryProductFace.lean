/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Boundary

/-!
# Face covers of realized boundaries and their products

Every point of the realization of `∂Δ[n+1]` comes from one of the codimension-one faces `face
{i}ᶜ`. Consequently, every point of the product of this realized boundary with a realized
standard simplex comes from a product of one such realized face with that simplex. The product
leg is the face-to-boundary map on the first factor and the identity on the second.
-/

@[expose] public section

open CategoryTheory Limits Simplicial Finset

namespace SSet

namespace boundaryProductFace

/-- For `n : ℕ` and `x : SSet.toTop.obj (SSet.boundary (n+1))`, there exist `i : Fin (n+2)` and a
point `p` of the realization of `SSet.stdSimplex.face (n := n+1) {i}ᶜ` such that the realized
face-to-boundary inclusion sends `p` to `x`. -/
theorem exists_face_cover (n : ℕ) (x : SSet.toTop.obj (SSet.boundary (n + 1))) :
    ∃ (i : Fin (n + 2)) (p : SSet.toTop.obj (SSet.stdSimplex.face (n := n + 1) {i}ᶜ : SSet)),
      SSet.toTop.map (SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary i)) p = x := by
  classical
  let S := MultispanShape.ofLinearOrder (Fin (n + 2))
  let M := SSet.boundary.multicoequalizerDiagram (n := n + 1)
  let DI : MultispanIndex S SSet := M.multispanIndex.toLinearOrder.map SSet.Subcomplex.toSSetFunctor
  let D : Cocone DI.multispan := M.multicofork.toLinearOrder.map SSet.Subcomplex.toSSetFunctor
  let c : Cocone (DI.multispan ⋙ SSet.toTop) := SSet.toTop.mapCocone D
  have hc : IsColimit c := SSet.boundary.isColimitToTop' (n := n + 1)
  have hcType : IsColimit ((forget TopCat).mapCocone c) := isColimitOfPreserves (forget TopCat) hc
  have hRight (i : Fin (n + 2)) : c.ι.app (WalkingMultispan.right (i : S.R)) =
      SSet.toTop.map (SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary i)) := by
    have hD : D.ι.app (WalkingMultispan.right (i : S.R)) =
        SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary i) := by
      dsimp [D, S, M, MultispanShape.ofLinearOrder]; rfl
    have hC : c.ι.app (WalkingMultispan.right (i : S.R)) =
        SSet.toTop.map (D.ι.app (WalkingMultispan.right (i : S.R))) := rfl
    rw [hC]
    exact congrArg _ hD
  obtain ⟨j, z, hz⟩ := Types.jointly_surjective_of_isColimit hcType x
  cases j with
  | right i =>
    exact ⟨(i : Fin (n + 2)), z,
      (ConcreteCategory.congr_hom (hRight (i : Fin (n + 2))) z).symm.trans hz⟩
  | left p =>
    let i : Fin (n + 2) := p.1.1
    have hLE : SSet.stdSimplex.face (n := n + 1) ({i, p.1.2}ᶜ : Finset (Fin (n + 2))) ≤
        SSet.stdSimplex.face (n := n + 1) ({i}ᶜ : Finset (Fin (n + 2))) := by
      rw [SSet.stdSimplex.face_le_face_iff]
      exact compl_subset_compl.mpr (singleton_subset_iff.mpr (mem_insert_self i {p.1.2}))
    have hOrigLE := hLE
    have hDI_fst : DI.fst p = SSet.Subcomplex.homOfLE hLE := by
      dsimp [DI, S, M, MultispanShape.ofLinearOrder]
      change SSet.Subcomplex.homOfLE hOrigLE = SSet.Subcomplex.homOfLE hLE
      congr 1
    have hFst_eq : (DI.multispan ⋙ SSet.toTop).map (WalkingMultispan.Hom.fst p) =
        SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) := by
      change SSet.toTop.map (DI.fst p) = SSet.toTop.map (SSet.Subcomplex.homOfLE hLE)
      rw [hDI_fst]; rfl
    have hW : c.ι.app (WalkingMultispan.left p) z =
        c.ι.app (WalkingMultispan.right (S.fst p))
          (toTop.map (Subcomplex.homOfLE hLE) z) := by
      have hEq : toTop.map (Subcomplex.homOfLE hLE) ≫
          c.ι.app (WalkingMultispan.right (S.fst p)) =
          c.ι.app (WalkingMultispan.left p) := by
        rw [← hFst_eq]; exact c.w (WalkingMultispan.Hom.fst p)
      have hEq_congr :
          (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
            c.ι.app (WalkingMultispan.right (S.fst p))) z =
            c.ι.app (WalkingMultispan.left p) z :=
        ConcreteCategory.congr_hom hEq z
      have hcomp :
          (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) ≫
            c.ι.app (WalkingMultispan.right (S.fst p))) z =
            c.ι.app (WalkingMultispan.right (S.fst p))
              (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) z) :=
        ConcreteCategory.comp_apply (C := TopCat)
          (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE))
          (c.ι.app (WalkingMultispan.right (S.fst p))) z
      exact hEq_congr.symm.trans hcomp
    have hMid : c.ι.app (WalkingMultispan.right (S.fst p))
        (SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) z) = x :=
      hW.symm.trans hz
    exact ⟨(S.fst p : Fin (n + 2)), SSet.toTop.map (SSet.Subcomplex.homOfLE hLE) z,
      (ConcreteCategory.congr_hom (hRight (S.fst p : Fin (n + 2))) _).symm.trans hMid⟩

/-- For `n,m : ℕ` and a point `x` of `|∂Δ[n+1]| × |Δ[m]|` in `TopCat.{0}`, there exist `i : Fin
(n+2)` and a point `p` of `|face {i}ᶜ| × |Δ[m]|` whose image under the product of the realized
face-to-boundary map and the identity of `|Δ[m]|` is `x`. -/
theorem exists_face_cover_prod (n m : ℕ)
    (x : ↑(SSet.toTop.obj (SSet.boundary (n + 1)) ⨯ SSet.toTop.obj (Δ[m] : SSet.{0}))) :
    ∃ (i : Fin (n + 2))
      (p : ↑(SSet.toTop.obj (SSet.stdSimplex.face (n := n + 1) {i}ᶜ : SSet) ⨯
        SSet.toTop.obj (Δ[m] : SSet.{0}))),
      (ConcreteCategory.hom (Limits.prod.map
        (SSet.toTop.map (SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary i)))
        (𝟙 (SSet.toTop.obj (Δ[m] : SSet.{0}))))) p = x := by
  obtain ⟨i, p, hp⟩ := exists_face_cover n
    ((Limits.prod.fst : SSet.toTop.obj (SSet.boundary (n + 1)) ⨯ _ ⟶ _) x)
  have hmem : x ∈ Set.range (Limits.prod.map
      (SSet.toTop.map (SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary i)))
      (𝟙 (SSet.toTop.obj (Δ[m] : SSet.{0})))) := by
    rw [TopCat.range_prod_map]
    exact ⟨⟨p, hp⟩, _, rfl⟩
  obtain ⟨p', hp'⟩ := hmem
  exact ⟨i, p', hp'⟩

end boundaryProductFace
end SSet
