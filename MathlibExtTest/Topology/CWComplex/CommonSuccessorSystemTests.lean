/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.CommonSuccessorSystem

/-!
Importing source-only consumers of the actual X-only constructor. Every
input is the original Hausdorff CW space or a point/time/cell in the returned
objects. No CW, inverse, retraction, attaching or intersection packet is supplied.
-/

public section

noncomputable section

open CategoryTheory Topology Topology.CWComplex PreAbstractSimplicialComplex
open scoped unitInterval

universe u

#check Topology.CWComplex.CommonSuccessorStageData
#print axioms Topology.CWComplex.CommonSuccessorStageData
#check Topology.CWComplex.CommonSuccessorSystemData
#print axioms Topology.CWComplex.CommonSuccessorSystemData
#check Topology.CWComplex.commonSuccessorSystem
#print axioms Topology.CWComplex.commonSuccessorSystem

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

-- Both actual end inverse identities at every point of both full ends.
example (n : ℕ) (x : skeletonTop X (n + 1))
    (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization) :
    ((commonSuccessorSystem X).stages n).retractOriginal
        (((commonSuccessorSystem X).stages n).original x) = x ∧
      ((commonSuccessorSystem X).stages n).retractPolyhedral
        (((commonSuccessorSystem X).stages n).polyhedral p) = p :=
  ⟨((commonSuccessorSystem X).stages n).original_retraction x,
    ((commonSuccessorSystem X).stages n).polyhedral_retraction p⟩

-- The entire original closed characteristic disk uses the selected returned CW instance.
example (n m : ℕ) (hm : m < n + 1) (j : cell (Set.univ : Set X) m) :
    let D := (commonSuccessorSystem X).stages n
    letI := D.cw
    D.originalDiskLift m hm j ≫ TopCat.ofHom D.original =
      characteristicDiskMap (X := D.space) m (D.originalLabels m hm j) := by
  exact ((commonSuccessorSystem X).stages n).original_characteristicDiskMap m hm j

-- Intermediate old cells, with both source and target CW instances selected by the result.
example (n m : ℕ) :
    let S := commonSuccessorSystem X
    letI := (S.stages n).cw
    letI := S.intermediateCW n
    ∀ j : cell (Set.univ : Set (S.stages n).space) m,
      characteristicDiskMap (X := (S.stages n).space) m j ≫ TopCat.ofHom (S.oldToIntermediate n) =
        characteristicDiskMap (X := S.intermediate n) m (S.intermediateOldLabels n m j) := by
  exact (commonSuccessorSystem X).intermediateOld_characteristicDiskMap n m

-- Intermediate family cells retain the complete actual disk map, not only a vertex law.
example (n m : ℕ) :
    let S := commonSuccessorSystem X
    letI := S.intermediateCW n
    ∀ j : cell (Set.univ : Set (S.family n).Realization) m,
      characteristicDiskMap (X := TopCat.of (S.family n).Realization) m j ≫
          TopCat.ofHom (S.familyToIntermediate n) =
        characteristicDiskMap (X := S.intermediate n) m (S.intermediateFamilyLabels n m j) := by
  exact (commonSuccessorSystem X).intermediateFamily_characteristicDiskMap n m

-- Actual transition cells preserve every point of their original closed characteristic disks.
example (n m : ℕ) :
    let S := commonSuccessorSystem X
    letI := (S.stages n).cw
    letI := (S.stages (n + 1)).cw
    ∀ j : cell (Set.univ : Set (S.stages n).space) m,
      characteristicDiskMap (X := (S.stages n).space) m j ≫ TopCat.ofHom (S.transition n) =
        characteristicDiskMap (X := (S.stages (n + 1)).space) m (S.oldStageLabels n m j) := by
  exact (commonSuccessorSystem X).oldStage_characteristicDiskMap n m

-- Both intermediate closed CW subcomplex carriers are the actual pushout leg ranges.
example (n : ℕ) :
    let S := commonSuccessorSystem X
    letI := S.intermediateCW n
    (S.intermediateOld n : Set (S.intermediate n)) = Set.range (S.oldToIntermediate n) ∧
      (S.intermediateFamily n : Set (S.intermediate n)) = Set.range (S.familyToIntermediate n) := by
  exact ⟨(commonSuccessorSystem X).intermediateOld_carrier n,
    (commonSuccessorSystem X).intermediateFamily_carrier n⟩

-- The two exact preimages and their complete range intersection belong to the actual transition.
example (n : ℕ) :
    let S := commonSuccessorSystem X
    (S.transition n) ⁻¹' Set.range (S.stages (n + 1)).original = Set.range (S.stages n).original ∧
      (S.transition n) ⁻¹' Set.range (S.stages (n + 1)).polyhedral = Set.range (S.stages n).polyhedral ∧
        Set.range (S.stages (n + 1)).original ∩ Set.range (S.stages (n + 1)).polyhedral =
          (S.transition n) '' (Set.range (S.stages n).original ∩ Set.range (S.stages n).polyhedral) := by
  exact ⟨(commonSuccessorSystem X).original_preimage n,
    (commonSuccessorSystem X).polyhedral_preimage n, (commonSuccessorSystem X).end_intersection n⟩

-- Each elementary deformation fixes the whole intermediate A at every time.
example (top : Bool) (n : ℕ) (t : unitInterval) (a : (commonSuccessorSystem X).intermediate n) :
    (commonSuccessorSystem X).elementaryHomotopy top n
        (t, (commonSuccessorSystem X).intermediateToCommon n a) =
      (commonSuccessorSystem X).intermediateToCommon n a :=
  (commonSuccessorSystem X).elementary_fixed_intermediate top n t a

-- Both finite families fix the same independently specified original zero-cell image.
example (j : cell (Set.univ : Set X) 0) (n : ℕ) (t : unitInterval) :
    let S := commonSuccessorSystem X
    (S.stages n).originalDeformation (t, (S.stages n).original (S.zeroOriginal j n)) =
        (S.stages n).original (S.zeroOriginal j n) ∧
      (S.stages n).polyhedralDeformation (t, (S.stages n).original (S.zeroOriginal j n)) =
        (S.stages n).original (S.zeroOriginal j n) ∧
      (S.zeroOriginal j n).val = map (C := (Set.univ : Set X)) 0 j (0 : Fin 0 → ℝ) := by
  exact ⟨(commonSuccessorSystem X).original_zero_fixed j n t,
    (commonSuccessorSystem X).polyhedral_zero_fixed j n t, (commonSuccessorSystem X).zero_value j n⟩

-- The actual attaching map starts at the original sphere, and its whole original disk is at height0.
example (n : ℕ) (i : cell (Set.univ : Set X) (n + 1))
    (s : (classicalCellDiskPair.{u} (n + 1)).snd)
    (q : (classicalCellDiskPair.{u} (n + 1)).fst) :
    let S := commonSuccessorSystem X
    S.attaching n ⟨i, (s, 0)⟩ = S.oldToIntermediate n
        ((S.stages n).original (characteristicSphereToSkeleton (n + 1) i s)) ∧
      (S.stages (n + 1)).original (characteristicDiskToSkeleton (n + 1) i q) =
        S.cylinders n ⟨i, (q, 0)⟩ := by
  exact ⟨(commonSuccessorSystem X).attaching_zero n i s,
    (commonSuccessorSystem X).original_disk_end n i q⟩

-- The actual copied ordinary cone, at every cone point, has the exact top-disk coordinate.
example (n : ℕ) (i : cell (Set.univ : Set X) (n + 1))
    (q : TopCat.cone (TopCat.of (MappingCylinder.domainComplex
      (subdivisionIter (SphereTriangulation.complex (n + 1)) ((commonSuccessorSystem X).subdivisions n i))
      ((commonSuccessorSystem X).stages n).vertices).Realization)) :
    ((commonSuccessorSystem X).stages (n + 1)).polyhedral
        ((commonSuccessorSystem X).conesToNext n ⟨i, q⟩) =
      (commonSuccessorSystem X).cylinders n
        ⟨i, ((commonSuccessorSystem X).coneDiskComparison n i q, 1)⟩ :=
  (commonSuccessorSystem X).polyhedral_cone_end n i q

-- The elementary target is the actual retained endpoint attachment over the whole intermediate.
example (top : Bool) (n : ℕ) :
    let S := commonSuccessorSystem X
    CategoryTheory.IsPushout (TopCat.ofHom (S.elementaryBoundary top n))
      (sphereSumToDiskSum X (n + 1)) (TopCat.ofHom (S.elementaryOld top n))
      (TopCat.ofHom (S.elementaryDisks top n)) := by
  exact (commonSuccessorSystem X).elementary_isPushout top n

-- Old and full selected-disk inclusion/retraction equations use literal tube coordinates.
example (top : Bool) (n : ℕ) (a : (commonSuccessorSystem X).intermediate n)
    (i : cell (Set.univ : Set X) (n + 1)) (q : (classicalCellDiskPair.{u} (n + 1)).fst) :
    let S := commonSuccessorSystem X
    S.elementaryInclude top n (S.elementaryOld top n a) = S.intermediateToCommon n a ∧
      S.elementaryInclude top n (S.elementaryDisks top n ⟨i, q⟩) =
        S.cylinders n ⟨i, (q, if top then 1 else 0)⟩ ∧
      S.elementaryRetraction top n (S.cylinders n ⟨i, (q, if top then 1 else 0)⟩) =
        S.elementaryDisks top n ⟨i, q⟩ := by
  exact ⟨(commonSuccessorSystem X).elementaryInclude_old top n a,
    (commonSuccessorSystem X).elementaryInclude_disk top n i q,
    (commonSuccessorSystem X).elementaryRetraction_disk top n i q⟩

-- Every selected-disk point is stationary at every time; the retained image is exact.
example (top : Bool) (n : ℕ) (t : unitInterval)
    (i : cell (Set.univ : Set X) (n + 1)) (q : (classicalCellDiskPair.{u} (n + 1)).fst) :
    let S := commonSuccessorSystem X
    S.elementaryHomotopy top n (t, S.cylinders n ⟨i, (q, if top then 1 else 0)⟩) =
        S.cylinders n ⟨i, (q, if top then 1 else 0)⟩ ∧
      Set.range (S.elementaryInclude top n) = Set.range (S.intermediateToCommon n) ∪
        Set.range (fun z : (Σ _ : cell (Set.univ : Set X) (n + 1),
          (classicalCellDiskPair.{u} (n + 1)).fst) =>
          S.cylinders n ⟨z.1, (z.2, if top then 1 else 0)⟩) := by
  exact ⟨(commonSuccessorSystem X).elementary_fixed_disk top n t i q,
    (commonSuccessorSystem X).elementary_image top n⟩

end
