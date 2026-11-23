/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SubordinateCoverWeakEquivalence

/-!
# Tests for subordinate-cover realization weakness

Public-only consumers and cover-shape controls for the subordinate singular
subcomplex theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial Topology
open scoped Simplicial SSet.modelCategoryQuillen

universe u v

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory

namespace SubordinateCoverWeakEquivalenceTests

section PublicAPI

example {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) :
    SSet.realizationWeakEquivalences
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι :=
  AlgebraicTopology.subordinateCover_ι_mem_realizationWeakEquivalences U hU

example {X : TopCat.{1}} {ι : Type 2}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) :
    SSet.realizationWeakEquivalences
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι :=
  AlgebraicTopology.subordinateCover_ι_mem_realizationWeakEquivalences U hU

example {X : TopCat.{0}} {ι : Type 1}
    (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U) :
    SSet.realizationWeakEquivalences
      (AlgebraicTopology.subordinateCover
        (fun i => (U i : Set X))).ι :=
  AlgebraicTopology.subordinateCover_ι_mem_realizationWeakEquivalences U hU

end PublicAPI

section CoverShapes

private def singletonTopCover (X : TopCat.{u}) :
    PUnit → TopologicalSpace.Opens X :=
  fun _ => ⊤

private theorem singletonTopCover_isOpenCover (X : TopCat.{u}) :
    TopologicalSpace.IsOpenCover (singletonTopCover X) := by
  apply TopologicalSpace.IsOpenCover.mk
  simp [singletonTopCover]

private def repeatedTopCover (X : TopCat.{u}) :
    Fin 2 → TopologicalSpace.Opens X :=
  fun _ => ⊤

private theorem repeatedTopCover_isOpenCover (X : TopCat.{u}) :
    TopologicalSpace.IsOpenCover (repeatedTopCover X) := by
  apply TopologicalSpace.IsOpenCover.mk
  apply top_unique
  simpa [repeatedTopCover] using
    (le_iSup (repeatedTopCover X) (0 : Fin 2))

example (X : TopCat.{u}) :
    SSet.realizationWeakEquivalences
      (AlgebraicTopology.subordinateCover
        (fun i => (singletonTopCover X i : Set X))).ι :=
  AlgebraicTopology.subordinateCover_ι_mem_realizationWeakEquivalences
    (singletonTopCover X) (singletonTopCover_isOpenCover X)

example (X : TopCat.{u}) :
    SSet.realizationWeakEquivalences
      (AlgebraicTopology.subordinateCover
        (fun i => (repeatedTopCover X i : Set X))).ι :=
  AlgebraicTopology.subordinateCover_ι_mem_realizationWeakEquivalences
    (repeatedTopCover X) (repeatedTopCover_isOpenCover X)

private abbrev TwoPoint := TopCat.of (Fin 2)

private def twoPointComponentCover :
    Fin 2 → TopologicalSpace.Opens TwoPoint :=
  fun i =>
    { carrier := {i}
      is_open' := isOpen_discrete {i} }

private theorem twoPointComponentCover_isOpenCover :
    TopologicalSpace.IsOpenCover twoPointComponentCover := by
  apply TopologicalSpace.IsOpenCover.of_sets
    (fun i => (twoPointComponentCover i).isOpen)
  ext x
  simp [twoPointComponentCover]

example :
    SSet.realizationWeakEquivalences
      (AlgebraicTopology.subordinateCover
        (fun i => (twoPointComponentCover i : Set TwoPoint))).ι :=
  AlgebraicTopology.subordinateCover_ι_mem_realizationWeakEquivalences
    twoPointComponentCover twoPointComponentCover_isOpenCover

private def emptyCover :
    PEmpty → TopologicalSpace.Opens (TopCat.of PEmpty) :=
  PEmpty.elim

private theorem emptyCover_isOpenCover :
    TopologicalSpace.IsOpenCover emptyCover := by
  apply TopologicalSpace.IsOpenCover.mk
  ext x
  exact x.elim

example :
    SSet.realizationWeakEquivalences
      (AlgebraicTopology.subordinateCover
        (X := TopCat.of PEmpty)
        (fun i => (emptyCover i : Set PEmpty))).ι :=
  AlgebraicTopology.subordinateCover_ι_mem_realizationWeakEquivalences
    emptyCover emptyCover_isOpenCover

example (U : PEmpty → TopologicalSpace.Opens (TopCat.of PUnit)) :
    ¬TopologicalSpace.IsOpenCover U := by
  intro hU
  obtain ⟨i, _⟩ := hU.exists_mem PUnit.unit
  exact i.elim

private abbrev GeomInterval :=
  Convexity.StdSimplex ℝ (Fin 2)

private def leftMember : TopologicalSpace.Opens GeomInterval where
  carrier := {q | q.weights 1 < (2 : ℝ) / 3}
  is_open' := isOpen_Iio.preimage
    (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) 1)

private def rightMember : TopologicalSpace.Opens GeomInterval where
  carrier := {q | (1 : ℝ) / 3 < q.weights 1}
  is_open' := isOpen_Ioi.preimage
    (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) 1)

private def overlappingCover :
    Fin 2 → TopologicalSpace.Opens GeomInterval :=
  ![leftMember, rightMember]

private theorem overlappingCover_isOpenCover :
    TopologicalSpace.IsOpenCover overlappingCover := by
  apply TopologicalSpace.IsOpenCover.of_sets
    (fun i => (overlappingCover i).isOpen)
  ext q
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases hq : q.weights 1 < (2 : ℝ) / 3
  · exact ⟨0, hq⟩
  · refine ⟨1, ?_⟩
    change (1 : ℝ) / 3 < q.weights 1
    linarith

example :
    SSet.realizationWeakEquivalences
      (AlgebraicTopology.subordinateCover
        (X := TopCat.of GeomInterval)
        (fun i => (overlappingCover i : Set GeomInterval))).ι :=
  AlgebraicTopology.subordinateCover_ι_mem_realizationWeakEquivalences
    (X := TopCat.of GeomInterval) (ι := Fin 2)
    overlappingCover overlappingCover_isOpenCover

end CoverShapes

section PrivateAndNegativeGuards

/-! Representative implementation seams stay private after import. -/

#guard_msgs (error, substring := true) in
#check AlgebraicTopology.clientExists_exTower_factor

#guard_msgs (error, substring := true) in
#check AlgebraicTopology.clientExists_exTower_later_eq

#guard_msgs (error, substring := true) in
#check AlgebraicTopology.exists_relStruct_common_stage

#guard_msgs (error, substring := true) in
#check AlgebraicTopology.clientExTowerZeroMapRaw_comp_grid

#guard_msgs (error, substring := true) in
#check AlgebraicTopology.alternateGridToInfinity

#guard_msgs (error, substring := true) in
#check AlgebraicTopology.alternateGridToInfinity_precomp

#guard_msgs (error, substring := true) in
#check AlgebraicTopology.alternateGridToInfinityHomotopy

#guard_msgs (error, substring := true) in
#check AlgebraicTopology.exists_subordinate_common_stage_boundary_filler

#guard_msgs (error, substring := true) in
#check AlgebraicTopology.exists_subordinate_source_relStruct₀

#guard_msgs (error, substring := true) in
#check AlgebraicTopology.subordinateCover_mapπ₀_bijective

#guard_msgs (error, substring := true) in
#check AlgebraicTopology.subordinateCover_piMap_bijective

/-! Proof-only imports do not leak stronger or unrelated endpoints.  Every
name below is an actual declaration in its owning module. -/

#guard_msgs (error, substring := true) in
#check SSet.exInfinityUnit_mem_realizationWeakEquivalences

#guard_msgs (error, substring := true) in
#check SSet.KanComplex.W_iff

#guard_msgs (error, substring := true) in
#check SSet.exists_sdIter_simplex_range_subset

#guard_msgs (error, substring := true) in
#check TopCat.sdr_pushout_inr_mem_weakHomotopyEquivalences

#guard_msgs (error, substring := true) in
#check TopCat.weakEquivalence_homotopyCofiberPointQuotientComparison_of_leftProper

#guard_msgs (error, substring := true) in
#check SSet.Rezk.segalTwoComparison

/-! The subordinate inclusion acquires no proof-global model dictionaries. -/

example {X : TopCat.{u}} {ι : Type v}
    (U : ι → TopologicalSpace.Opens X) : True := by
  let A : SSet.{u} :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X)) : SSet.{u})
  let j : A ⟶ TopCat.toSSet.obj X :=
    (AlgebraicTopology.subordinateCover
      (fun i => (U i : Set X))).ι
  fail_if_success
    let _ : A.KanComplex := inferInstance
  fail_if_success
    let _ : HomotopicalAlgebra.Fibration j := inferInstance
  fail_if_success
    let _ : HomotopicalAlgebra.WeakEquivalence j := inferInstance
  trivial

end PrivateAndNegativeGuards

#print axioms AlgebraicTopology.subordinateCover_ι_mem_realizationWeakEquivalences

end SubordinateCoverWeakEquivalenceTests

end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
