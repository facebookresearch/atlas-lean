/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.CWComplex.CommonDimensionUnion

/-! Importing clients of the actual common dimension union. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex
open PreAbstractSimplicialComplex
open scoped Classical

universe u v

#check Topology.CWComplex.CommonDimensionUnionData
#print axioms Topology.CWComplex.CommonDimensionUnionData
#check Topology.CWComplex.commonDimensionUnion
#print axioms Topology.CWComplex.commonDimensionUnion

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

example : IsColimit (commonDimensionUnion.{u, v} X).commonCocone :=
  (commonDimensionUnion.{u, v} X).common_isColimit

example : IsQuotientMap (commonDimensionUnion.{u, v} X).commonSigmaQuotient :=
  (commonDimensionUnion.{u, v} X).commonSigmaQuotient_isQuotientMap

example : CWComplex (Set.univ : Set (commonDimensionUnion.{u, v} X).commonCocone.pt) :=
  (commonDimensionUnion.{u, v} X).commonCW

example : T2Space (commonDimensionUnion.{u, v} X).commonCocone.pt :=
  (commonDimensionUnion.{u, v} X).commonT2

example {Y : Type v} [TopologicalSpace Y]
    (f : (commonDimensionUnion.{u, v} X).commonCocone.pt → Y)
    (h : ∀ n, Continuous (f ∘ (commonDimensionUnion.{u, v} X).commonCocone.ι.app n)) :
    Continuous f :=
  ((commonDimensionUnion.{u, v} X).common_continuous_iff f).mpr h

example {Y : Type v} [TopologicalSpace Y]
    (f : (commonDimensionUnion.{u, v} X).polyhedron.Realization → Y)
    (h : ∀ n, Continuous (f ∘ (commonDimensionUnion.{u, v} X).polyhedralStageInclusion n)) :
    Continuous f :=
  ((commonDimensionUnion.{u, v} X).polyhedron_continuous_iff f).mpr h

example (n m : ℕ) :
    let d := commonDimensionUnion.{u, v} X
    letI := d.commonCW
    letI := ((commonSuccessorSystem X).stages n).cw
    (d.commonStageSubcomplex n : Set d.commonCocone.pt) = Set.range (d.commonCocone.ι.app n) ∧
      (d.commonStageSubcomplex n).I m = Set.range (d.commonStageLabels n m) ∧
      ∀ a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).space) m,
        characteristicDiskMap (X := ((commonSuccessorSystem X).stages n).space) m a ≫
          d.commonCocone.ι.app n =
          characteristicDiskMap (X := d.commonCocone.pt) m (d.commonStageLabels n m a) :=
  ⟨(commonDimensionUnion.{u, v} X).commonStageSubcomplex_carrier n,
    (commonDimensionUnion.{u, v} X).commonStageSubcomplex_labels n m,
    (commonDimensionUnion.{u, v} X).commonStage_characteristicDiskMap n m⟩

-- The returned labels are embeddings in every original dimension.
example (n m : ℕ) :
    let d := commonDimensionUnion.{u, v} X
    letI := d.commonCW
    letI := ((commonSuccessorSystem X).stages n).cw
    Function.Injective (d.commonStageLabels n m) :=
  ((commonDimensionUnion.{u, v} X).commonStageLabels n m).injective

-- The whole public cell-label system agrees across each actual successor.
example (n m : ℕ) :
    let d := commonDimensionUnion.{u, v} X
    letI := d.commonCW
    letI := ((commonSuccessorSystem X).stages n).cw
    letI := ((commonSuccessorSystem X).stages (n + 1)).cw
    ∀ a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).space) m,
      d.commonStageLabels (n + 1) m ((commonSuccessorSystem X).oldStageLabels n m a) =
        d.commonStageLabels n m a :=
  (commonDimensionUnion.{u, v} X).commonStageLabels_step n m

-- A polyhedral stage label enters the common end through the same old-stage label.
example (n m : ℕ) :
    let d := commonDimensionUnion.{u, v} X
    letI := d.commonCW
    letI := ((commonSuccessorSystem X).stages n).cw
    ∀ a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m,
      d.polyhedralEndLabels m (d.polyhedralStageCellLabels n m a) =
        d.commonStageLabels n m (((commonSuccessorSystem X).stages n).polyhedralLabels m a) :=
  (commonDimensionUnion.{u, v} X).polyhedralEndLabels_stage n m

example (n : ℕ) (a : Finset ((commonSuccessorSystem X).stages n).vertices)
    (ha : a ∈ ((commonSuccessorSystem X).stages n).polyhedron) :
    a.map ((commonDimensionUnion.{u, v} X).stageVertexEmbedding n) ∈
      (commonDimensionUnion.{u, v} X).polyhedron :=
  ((commonDimensionUnion.{u, v} X).polyhedron_faces _).mpr ⟨n, a, ha, rfl⟩

example (n : ℕ) (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization) :
    let d := commonDimensionUnion.{u, v} X
    (d.polyhedralStageInclusion n p).point = p.point.map (d.stageVertexEmbedding n) ∧
      d.polyhedralColimitHomeomorph.symm (d.polyhedralStageInclusion n p) =
        colimit.ι (Functor.ofSequence
          (X := fun n => TopCat.of (((commonSuccessorSystem X).stages n).polyhedron.Realization))
          (fun n => TopCat.ofHom ((commonSuccessorSystem X).polyhedralTransition n))) n p :=
  ⟨(commonDimensionUnion.{u, v} X).polyhedralStageInclusion_point n p,
    (commonDimensionUnion.{u, v} X).polyhedralColimitHomeomorph_inverse_leg n p⟩

example (n : ℕ) (z : skeletonTop X (n + 1))
    (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization) :
    let d := commonDimensionUnion.{u, v} X
    d.originalEnd (skeletonInclusion X (n + 1) z) =
        d.commonCocone.ι.app n (((commonSuccessorSystem X).stages n).original z) ∧
      d.polyhedralEnd (d.polyhedralStageInclusion n p) =
        d.commonCocone.ι.app n (((commonSuccessorSystem X).stages n).polyhedral p) :=
  ⟨(commonDimensionUnion.{u, v} X).originalEnd_stage n z,
    (commonDimensionUnion.{u, v} X).polyhedralEnd_stage n p⟩

example (m : ℕ) :
    let d := commonDimensionUnion.{u, v} X
    letI := d.commonCW
    (d.polyhedralEndSubcomplex : Set d.commonCocone.pt) = Set.range d.polyhedralEnd ∧
      d.polyhedralEndSubcomplex.I m = Set.range (d.polyhedralEndLabels m) ∧
      ∀ b : cell (Set.univ : Set d.polyhedron.Realization) m,
        characteristicDiskMap (X := TopCat.of d.polyhedron.Realization) m b ≫
          TopCat.ofHom d.polyhedralEnd =
          characteristicDiskMap (X := d.commonCocone.pt) m (d.polyhedralEndLabels m b) :=
  ⟨(commonDimensionUnion.{u, v} X).polyhedralEndSubcomplex_carrier,
    (commonDimensionUnion.{u, v} X).polyhedralEndSubcomplex_labels m,
    (commonDimensionUnion.{u, v} X).polyhedralEnd_characteristicDiskMap m⟩

example (m : ℕ) (b : cell (Set.univ : Set (commonDimensionUnion.{u, v} X).polyhedron.Realization) m) :
    ∃ n a, (commonDimensionUnion.{u, v} X).polyhedralStageCellLabels n m a = b :=
  (commonDimensionUnion.{u, v} X).polyhedralStageCell_covered m b

example (j : cell (Set.univ : Set X) 0) :
    let d := commonDimensionUnion.{u, v} X
    Set.range d.originalEnd ∩ Set.range d.polyhedralEnd =
        Set.range (fun z : skeletonTop X 1 => d.originalEnd (skeletonInclusion X 1 z)) ∧
      d.polyhedralEnd (d.zeroPolyhedral j) = d.originalEnd (map (C := (Set.univ : Set X)) 0 j 0) :=
  ⟨(commonDimensionUnion.{u, v} X).global_zero_intersection,
    (commonDimensionUnion.{u, v} X).zero_ends_value j⟩

end
