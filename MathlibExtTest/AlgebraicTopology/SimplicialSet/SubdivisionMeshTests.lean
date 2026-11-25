/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Mesh

/-!
# Tests for iterated subdivision mesh

Public-only consumers for iterated geometric cells, their mesh estimate,
and open-cover subordination.
-/

@[expose] public section

universe u v

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial Set Topology
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.SubdivisionMeshTests

section PublicAPI

noncomputable example (n k : ℕ) {d : ℕ}
    (σ : (Δ[d] : SSet.{0}) ⟶
      (SSet.sdIter k).obj (Δ[n] : SSet.{0})) :
    TopCat.of (Convexity.StdSimplex ℝ (Fin (d + 1))) ⟶
      TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  SSet.sdIterCellMap n k σ

example (n k : ℕ) {d : ℕ}
    (σ : (Δ[d] : SSet.{0}) ⟶
      (SSet.sdIter k).obj (Δ[n] : SSet.{0})) :
    Metric.diam (Set.range (SSet.sdIterCellMap n k σ).hom) ≤
      ((n : ℝ) / ((n : ℝ) + 1)) ^ k *
        Metric.diam (Set.univ : Set
          (Convexity.StdSimplex ℝ (Fin (n + 1)))) :=
  SSet.diam_range_sdIterCellMap_le n k σ

example {B : TopCat.{0}} {n : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{0}) ⟶ B)
    {ι : Type*} (U : ι → TopologicalSpace.Opens B)
    (hU : TopologicalSpace.IsOpenCover U) :
    ∃ k : ℕ, ∀ {d : ℕ}
      (σ : (Δ[d] : SSet.{0}) ⟶
        (SSet.sdIter k).obj (Δ[n] : SSet.{0})),
      ∃ i,
        Set.range
          (SSet.toTop.map σ ≫
            (SSet.toTopSdIterIso (Δ[n] : SSet.{0}) k).hom ≫ b).hom ⊆
          (U i : Set B) :=
  SSet.exists_sdIter_simplex_range_subset b U hU

end PublicAPI

section AllUniverseAPI

noncomputable example (n k : ℕ) {d : ℕ}
    (σ : (Δ[d] : SSet.{u}) ⟶
      (SSet.sdIter k).obj (Δ[n] : SSet.{u})) :
    TopCat.of (Convexity.StdSimplex ℝ (Fin (d + 1))) ⟶
      TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  SSet.sdIterCellMap n k σ

example (n k : ℕ) {d : ℕ}
    (σ : (Δ[d] : SSet.{u}) ⟶
      (SSet.sdIter k).obj (Δ[n] : SSet.{u})) :
    Metric.diam (Set.range (SSet.sdIterCellMap n k σ).hom) ≤
      ((n : ℝ) / ((n : ℝ) + 1)) ^ k *
        Metric.diam (Set.univ : Set
          (Convexity.StdSimplex ℝ (Fin (n + 1)))) :=
  SSet.diam_range_sdIterCellMap_le n k σ

example {B : TopCat.{u}} {n : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ B)
    {ι : Type v} (U : ι → TopologicalSpace.Opens B)
    (hU : TopologicalSpace.IsOpenCover U) :
    ∃ k : ℕ, ∀ {d : ℕ}
      (σ : (Δ[d] : SSet.{u}) ⟶
        (SSet.sdIter k).obj (Δ[n] : SSet.{u})),
      ∃ i,
        Set.range
          (SSet.toTop.map σ ≫
            (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b).hom ⊆
          (U i : Set B) :=
  SSet.exists_sdIter_simplex_range_subset b U hU

end AllUniverseAPI

section Orientations

example (n d : ℕ)
    (σ : (Δ[d] : SSet.{0}) ⟶ (Δ[n] : SSet.{0})) :
    SSet.sdIterCellMap n 0 σ =
      (SSet.stdSimplex.toTopIso ⦋d⦌).inv ≫
        SSet.toTop.map σ ≫
        (SSet.stdSimplex.toTopIso ⦋n⦌).hom := by
  apply TopCat.ext
  intro z
  rfl

example (n d : ℕ)
    (σ : (Δ[d] : SSet.{0}) ⟶
      SSet.sd.obj (Δ[n] : SSet.{0})) :
    SSet.sdIterCellMap n 1 σ =
      (SSet.stdSimplex.toTopIso ⦋d⦌).inv ≫
        SSet.toTop.map σ ≫
        (SSet.toTopSdIso (Δ[n] : SSet.{0})).hom ≫
        (SSet.stdSimplex.toTopIso ⦋n⦌).hom := by
  apply TopCat.ext
  intro z
  rfl

example :
    SSet.sdIterCellMap 0 0 (𝟙 (Δ[0] : SSet.{0})) = 𝟙 _ := by
  apply TopCat.ext
  intro z
  simp [SSet.sdIterCellMap]
  change (SimplexCategory.toTopHomeo ⦋0⦌)
    ((SimplexCategory.toTopHomeo ⦋0⦌).symm z) = z
  exact Homeomorph.apply_symm_apply _ z

example (n d : ℕ)
    (σ : (Δ[d] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}))
    (z : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    SSet.sdIterCellMap n 0 σ z =
      (SimplexCategory.toTopHomeo.{u} ⦋n⦌)
        (SSet.toTop.map σ
          ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z)) := by
  unfold SSet.sdIterCellMap
  have hid :
      (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) 0).hom
          (SSet.toTop.map σ
            ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z)) =
        SSet.toTop.map σ
          ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z) := by
    rw [SSet.toTopSdIterIso_zero]
    rfl
  exact congrArg (SimplexCategory.toTopHomeo.{u} ⦋n⦌) hid

example (n d : ℕ)
    (σ : (Δ[d] : SSet.{u}) ⟶
      SSet.sd.obj (Δ[n] : SSet.{u}))
    (z : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    SSet.sdIterCellMap n 1 σ z =
      (SimplexCategory.toTopHomeo.{u} ⦋n⦌)
        ((SSet.toTopSdIso (Δ[n] : SSet.{u})).hom
          (SSet.toTop.map σ
            ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm z))) := by
  unfold SSet.sdIterCellMap
  have hiter : SSet.toTopSdIterIso (Δ[n] : SSet.{u}) 1 =
      SSet.toTopSdIso (Δ[n] : SSet.{u}) := by
    simp
  rw [hiter]
  rfl

end Orientations

section Cells

private def degenerateEdge :
    (Δ[1] : SSet.{0}) ⟶ (Δ[1] : SSet.{0}) :=
  SSet.stdSimplex.map
    (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)

private def faceZero :
    PartialOrder.NonemptyFiniteChains (ULift (Fin 2)) where
  finset := {ULift.up 0}
  comparable a b := le_total a b

private def faceFull :
    PartialOrder.NonemptyFiniteChains (ULift (Fin 2)) where
  finset := {ULift.up 0, ULift.up 1}
  comparable a b := le_total a b

private theorem faceZero_le_faceFull : faceZero ≤ faceFull := by
  intro x hx
  simp only [faceZero, Finset.mem_singleton] at hx
  subst x
  simp [faceFull]

private noncomputable def sdVertexFull :
    (SimplexCategory.sd.{0}.obj ⦋1⦌) _⦋0⦌ :=
  ComposableArrows.mk₀ faceFull

private noncomputable def sdEdgeZeroFull :
    (SimplexCategory.sd.{0}.obj ⦋1⦌) _⦋1⦌ :=
  ComposableArrows.mk₁ (homOfLE faceZero_le_faceFull)

private noncomputable def sdEdgeRepeated :
    (SimplexCategory.sd.{0}.obj ⦋1⦌) _⦋1⦌ :=
  (SimplexCategory.sd.obj ⦋1⦌).map
    (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op sdVertexFull

private noncomputable def strictSigma :
    (Δ[1] : SSet.{0}) ⟶ SSet.sd.obj (Δ[1] : SSet.{0}) :=
  SSet.yonedaEquiv.symm
    ((SSet.stdSimplex.sdIso.inv.app ⦋1⦌).app _ sdEdgeZeroFull)

private noncomputable def repeatedSigma :
    (Δ[1] : SSet.{0}) ⟶ SSet.sd.obj (Δ[1] : SSet.{0}) :=
  SSet.yonedaEquiv.symm
    ((SSet.stdSimplex.sdIso.inv.app ⦋1⦌).app _ sdEdgeRepeated)

noncomputable example :
    TopCat.of (Convexity.StdSimplex ℝ (Fin 2)) ⟶
      TopCat.of (Convexity.StdSimplex ℝ (Fin 2)) :=
  SSet.sdIterCellMap 1 0 degenerateEdge

example :
    Metric.diam
        (Set.range (SSet.sdIterCellMap 1 0 degenerateEdge).hom) ≤
      ((1 : ℝ) / 2) ^ 0 *
        Metric.diam (Set.univ : Set
          (Convexity.StdSimplex ℝ (Fin 2))) := by
  simpa using SSet.diam_range_sdIterCellMap_le 1 0 degenerateEdge

noncomputable example :
    TopCat.of (Convexity.StdSimplex ℝ (Fin 2)) ⟶
      TopCat.of (Convexity.StdSimplex ℝ (Fin 2)) :=
  SSet.sdIterCellMap 1 1 strictSigma

noncomputable example :
    TopCat.of (Convexity.StdSimplex ℝ (Fin 2)) ⟶
      TopCat.of (Convexity.StdSimplex ℝ (Fin 2)) :=
  SSet.sdIterCellMap 1 1 repeatedSigma

example :
    Metric.diam (Set.range (SSet.sdIterCellMap 1 1 strictSigma).hom) ≤
      ((1 : ℝ) / 2) ^ 1 *
        Metric.diam (Set.univ : Set
          (Convexity.StdSimplex ℝ (Fin 2))) := by
  convert SSet.diam_range_sdIterCellMap_le 1 1 strictSigma using 1
  norm_num

example :
    Metric.diam
        (Set.range (SSet.sdIterCellMap 1 1 repeatedSigma).hom) ≤
      ((1 : ℝ) / 2) ^ 1 *
        Metric.diam (Set.univ : Set
          (Convexity.StdSimplex ℝ (Fin 2))) := by
  convert SSet.diam_range_sdIterCellMap_le 1 1 repeatedSigma using 1
  norm_num

end Cells

section MeshBoundaries

example :
    Metric.diam
        (Set.range
          (SSet.sdIterCellMap 0 0 (𝟙 (Δ[0] : SSet.{0}))).hom) ≤
      ((0 : ℝ) / ((0 : ℝ) + 1)) ^ 0 *
        Metric.diam (Set.univ : Set
          (Convexity.StdSimplex ℝ (Fin 1))) := by
  simpa only [Nat.cast_zero] using
    SSet.diam_range_sdIterCellMap_le 0 0 (𝟙 (Δ[0] : SSet.{0}))

example : ((0 : ℝ) / ((0 : ℝ) + 1)) ^ 0 = 1 := by
  norm_num

private theorem range_fin0_cell_eq_singleton
    (n k : ℕ)
    (σ : (Δ[0] : SSet.{0}) ⟶
      (SSet.sdIter k).obj (Δ[n] : SSet.{0})) :
    Set.range (SSet.sdIterCellMap n k σ).hom =
      {(SSet.sdIterCellMap n k σ)
        (Convexity.StdSimplex.single (R := ℝ) (0 : Fin 1))} := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    rw [Subsingleton.elim q
      (Convexity.StdSimplex.single (R := ℝ) (0 : Fin 1))]
    simp
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    exact ⟨Convexity.StdSimplex.single (R := ℝ) (0 : Fin 1),
      hy.symm⟩

example (n k : ℕ)
    (σ : (Δ[0] : SSet.{0}) ⟶
      (SSet.sdIter k).obj (Δ[n] : SSet.{0})) :
    Metric.diam (Set.range (SSet.sdIterCellMap n k σ).hom) = 0 := by
  rw [range_fin0_cell_eq_singleton, Metric.diam_singleton]

noncomputable example :
    TopCat.of (Convexity.StdSimplex ℝ (Fin 3)) ⟶
      TopCat.of (Convexity.StdSimplex ℝ (Fin 3)) :=
  SSet.sdIterCellMap 2 0 (𝟙 (Δ[2] : SSet.{u}))

example :
    Metric.diam
        (Set.range
          (SSet.sdIterCellMap 2 0 (𝟙 (Δ[2] : SSet.{u}))).hom) ≤
      ((2 : ℝ) / ((2 : ℝ) + 1)) ^ 0 *
        Metric.diam (Set.univ : Set
          (Convexity.StdSimplex ℝ (Fin 3))) :=
  SSet.diam_range_sdIterCellMap_le 2 0 (𝟙 (Δ[2] : SSet.{u}))

end MeshBoundaries

section Cover

private abbrev GeomInterval :=
  Convexity.StdSimplex ℝ (Fin 2)

private noncomputable def intervalRealizationMap :
    SSet.toTop.obj (Δ[1] : SSet.{0}) ⟶ TopCat.of GeomInterval :=
  (SSet.stdSimplex.toTopIso ⦋1⦌).hom

private def leftMember : TopologicalSpace.Opens GeomInterval where
  carrier := {q | q.weights 1 < (2 : ℝ) / 3}
  is_open' := isOpen_Iio.preimage
    (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) 1)

private def rightMember : TopologicalSpace.Opens GeomInterval where
  carrier := {q | (1 : ℝ) / 3 < q.weights 1}
  is_open' := isOpen_Ioi.preimage
    (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) 1)

private def twoMemberCover :
    Fin 2 → TopologicalSpace.Opens GeomInterval :=
  ![leftMember, rightMember]

private theorem twoMemberCover_isOpenCover :
    TopologicalSpace.IsOpenCover twoMemberCover := by
  apply TopologicalSpace.IsOpenCover.of_sets
    (fun i ↦ (twoMemberCover i).isOpen)
  ext q
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases hq : q.weights 1 < (2 : ℝ) / 3
  · refine ⟨0, ?_⟩
    change q.weights 1 < (2 : ℝ) / 3
    exact hq
  · refine ⟨1, ?_⟩
    change (1 : ℝ) / 3 < q.weights 1
    linarith

private theorem interval_range_not_subset_left :
    ¬Set.range intervalRealizationMap ⊆
      (twoMemberCover 0 : Set GeomInterval) := by
  intro h
  have hv : Convexity.StdSimplex.single (R := ℝ) (1 : Fin 2) ∈
      Set.range intervalRealizationMap := by
    refine ⟨(SSet.stdSimplex.toTopIso ⦋1⦌).inv
      (Convexity.StdSimplex.single (R := ℝ) (1 : Fin 2)), ?_⟩
    simp [intervalRealizationMap]
  have := h hv
  change (Convexity.StdSimplex.single (R := ℝ)
    (1 : Fin 2)).weights 1 < (2 : ℝ) / 3 at this
  norm_num at this

private theorem interval_range_not_subset_right :
    ¬Set.range intervalRealizationMap ⊆
      (twoMemberCover 1 : Set GeomInterval) := by
  intro h
  have hv : Convexity.StdSimplex.single (R := ℝ) (0 : Fin 2) ∈
      Set.range intervalRealizationMap := by
    refine ⟨(SSet.stdSimplex.toTopIso ⦋1⦌).inv
      (Convexity.StdSimplex.single (R := ℝ) (0 : Fin 2)), ?_⟩
    simp [intervalRealizationMap]
  have := h hv
  change (1 : ℝ) / 3 <
    (Convexity.StdSimplex.single (R := ℝ)
      (0 : Fin 2)).weights 1 at this
  norm_num at this

private theorem no_single_cover_member :
    ¬∃ i, Set.range intervalRealizationMap ⊆
      (twoMemberCover i : Set GeomInterval) := by
  rintro ⟨i, hi⟩
  fin_cases i
  · exact interval_range_not_subset_left hi
  · exact interval_range_not_subset_right hi

example :
    ∃ k : ℕ, k ≠ 0 ∧ ∀ {d : ℕ}
      (σ : (Δ[d] : SSet.{0}) ⟶
        (SSet.sdIter k).obj (Δ[1] : SSet.{0})),
      ∃ i,
        Set.range
          (SSet.toTop.map σ ≫
            (SSet.toTopSdIterIso (Δ[1] : SSet.{0}) k).hom ≫
            intervalRealizationMap).hom ⊆
          (twoMemberCover i : Set GeomInterval) := by
  obtain ⟨k, hk⟩ :=
    SSet.exists_sdIter_simplex_range_subset intervalRealizationMap
      twoMemberCover twoMemberCover_isOpenCover
  refine ⟨k, ?_, hk⟩
  intro hk0
  subst k
  obtain ⟨i, hi⟩ := hk (𝟙 (Δ[1] : SSet.{0}))
  have hwhole : Set.range intervalRealizationMap ⊆
      (twoMemberCover i : Set GeomInterval) := by
    simpa using hi
  exact no_single_cover_member ⟨i, hwhole⟩

example {B : TopCat.{0}}
    (b : SSet.toTop.obj (Δ[0] : SSet.{0}) ⟶ B)
    (U : PEmpty → TopologicalSpace.Opens B)
    (hU : TopologicalSpace.IsOpenCover U) : False := by
  let z := b ((SSet.stdSimplex.toTopIso ⦋0⦌).inv
    (Convexity.StdSimplex.single (R := ℝ) (0 : Fin 1)))
  obtain ⟨i, _hi⟩ := hU.exists_mem z
  exact PEmpty.elim i

example {B : TopCat.{u}} {n : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ B)
    (U : ℕ → TopologicalSpace.Opens B)
    (hU : TopologicalSpace.IsOpenCover U) :
    ∃ k : ℕ, ∀ {d : ℕ}
      (σ : (Δ[d] : SSet.{u}) ⟶
        (SSet.sdIter k).obj (Δ[n] : SSet.{u})),
      ∃ i,
        Set.range
          (SSet.toTop.map σ ≫
            (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b).hom ⊆
          (U i : Set B) :=
  SSet.exists_sdIter_simplex_range_subset b U hU

example {B : TopCat.{u}}
    (b : SSet.toTop.obj (Δ[0] : SSet.{u}) ⟶ B)
    (U : PEmpty → TopologicalSpace.Opens B)
    (hU : TopologicalSpace.IsOpenCover U) : False := by
  let z := b ((SimplexCategory.toTopHomeo.{u} ⦋0⦌).symm
    (Convexity.StdSimplex.single (R := ℝ) (0 : Fin 1)))
  obtain ⟨i, _hi⟩ := hU.exists_mem z
  exact PEmpty.elim i

end Cover

section UniverseBoundary

variable
  (σ₁ : (Δ[0] : SSet.{1}) ⟶
    (SSet.sdIter 0).obj (Δ[0] : SSet.{1}))

noncomputable example :
    TopCat.of (Convexity.StdSimplex ℝ (Fin 1)) ⟶
      TopCat.of (Convexity.StdSimplex ℝ (Fin 1)) :=
  SSet.sdIterCellMap 0 0 σ₁

example :
    Metric.diam (Set.range (SSet.sdIterCellMap 0 0 σ₁).hom) ≤
      ((0 : ℝ) / ((0 : ℝ) + 1)) ^ 0 *
        Metric.diam (Set.univ : Set
          (Convexity.StdSimplex ℝ (Fin 1))) :=
  SSet.diam_range_sdIterCellMap_le 0 0 σ₁

example {B : TopCat.{1}}
    (b : SSet.toTop.obj (Δ[0] : SSet.{1}) ⟶ B)
    {ι : Type 2} (U : ι → TopologicalSpace.Opens B)
    (hU : TopologicalSpace.IsOpenCover U) :
    ∃ k : ℕ, ∀ {d : ℕ}
      (σ : (Δ[d] : SSet.{1}) ⟶
        (SSet.sdIter k).obj (Δ[0] : SSet.{1})),
      ∃ i,
        Set.range
          (SSet.toTop.map σ ≫
            (SSet.toTopSdIterIso (Δ[0] : SSet.{1}) k).hom ≫ b).hom ⊆
          (U i : Set B) :=
  SSet.exists_sdIter_simplex_range_subset b U hU

end UniverseBoundary

#print axioms SSet.sdIterCellMap
#print axioms SSet.diam_range_sdIterCellMap_le
#print axioms SSet.exists_sdIter_simplex_range_subset

end MathlibExtTest.AlgebraicTopology.SimplicialSet.SubdivisionMeshTests
