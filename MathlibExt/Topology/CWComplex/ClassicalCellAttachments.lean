/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import MathlibExt.Topology.CWComplex.CharacteristicDiskMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import MathlibExt.Topology.Category.TopPair.ClosedBall.NDR
public import MathlibExt.Topology.Category.TopCat.QuotientPushout
public import Mathlib.Topology.CompactOpen

/-!
# Actual classical CW characteristic quotients and attachments

The characteristic maps below are the given classical maps restricted to
their actual max-norm closed disks and spheres. Hausdorffness belongs to the
ordinary CW model and is explicit whenever a compact characteristic image is
used as a closed quotient. No categorical attachment presentation is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Topology

universe u v

namespace Topology.CWComplex

variable {X : TopCat.{u}} [CWComplex (Set.univ : Set X)]


/-- The target of an original characteristic partial equivalence is its actual open cell. -/
theorem characteristicCell_target (n : ℕ) (j : cell (Set.univ : Set X) n) :
    (map n j).target = openCell (C := (Set.univ : Set X)) n j := by
  rw [openCell, ← source_eq n j]
  exact (map n j).image_source_eq_target.symm

instance compactSpaceClassicalCellDisk (n : ℕ) :
    CompactSpace (classicalCellDiskPair.{u} n).fst := by
  change CompactSpace (ULift.{u} (Metric.closedBall (0 : Fin n → ℝ) 1))
  infer_instance

/-- The actual characteristic map on its boundary sphere. -/
def characteristicSphereMap (n : ℕ) (j : cell (Set.univ : Set X) n) :
    (classicalCellDiskPair.{u} n).snd ⟶ X :=
  (classicalCellDiskPair.{u} n).map ≫ characteristicDiskMap n j

@[simp]
theorem characteristicSphereMap_apply (n : ℕ) (j : cell (Set.univ : Set X) n)
    (x : (classicalCellDiskPair.{u} n).snd) :
    characteristicSphereMap n j x = map n j x.down.val := rfl

/-- The image is the literal closed characteristic cell. -/
theorem range_characteristicDiskMap (n : ℕ) (j : cell (Set.univ : Set X) n) :
    Set.range (characteristicDiskMap n j) = closedCell n j := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.down.val, y.down.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ULift.up ⟨y, hy⟩, rfl⟩

/-- The boundary image is the literal classical frontier of the cell. -/
theorem range_characteristicSphereMap (n : ℕ) (j : cell (Set.univ : Set X) n) :
    Set.range (characteristicSphereMap n j) = cellFrontier n j := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.down.val, y.down.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ULift.up ⟨y, hy⟩, rfl⟩

/-- The characteristic disk map corestricted to its actual image. -/
def characteristicDiskToCell (n : ℕ) (j : cell (Set.univ : Set X) n) :
    (classicalCellDiskPair.{u} n).fst ⟶ TopCat.of (closedCell n j) :=
  TopCat.ofHom
    ⟨fun x => ⟨characteristicDiskMap n j x, x.down.val, x.down.property, rfl⟩,
      (characteristicDiskMap n j).hom.continuous.subtype_mk _⟩

/-- The compact-to-Hausdorff characteristic map is an actual quotient map. -/
theorem isQuotientMap_characteristicDiskToCell [T2Space X]
    (n : ℕ) (j : cell (Set.univ : Set X) n) :
    IsQuotientMap (characteristicDiskToCell n j) :=
  IsQuotientMap.of_surjective_continuous (by
    intro x
    obtain ⟨y, hy, hxy⟩ := x.property
    exact ⟨ULift.up ⟨y, hy⟩, Subtype.ext hxy⟩)
    (characteristicDiskToCell n j).hom.continuous

/-- The cell index contains its actual dimension and classical cell identifier. -/
abbrev CellIndex (X : TopCat.{u}) [CWComplex (Set.univ : Set X)] :=
  Σ n : ℕ, cell (Set.univ : Set X) n

/-- The actual disjoint sum of all characteristic closed disks. -/
abbrev CharacteristicDisks (X : TopCat.{u}) [CWComplex (Set.univ : Set X)] :=
  Σ j : CellIndex X, (classicalCellDiskPair.{u} j.1).fst

/-- The characteristic quotient map onto the original space. -/
def characteristicQuotient (X : TopCat.{u}) [CWComplex (Set.univ : Set X)] :
    TopCat.of (CharacteristicDisks X) ⟶ X :=
  TopCat.ofHom
    ⟨fun x => characteristicDiskMap x.1.1 x.1.2 x.2,
      continuous_sigma (fun j => (characteristicDiskMap j.1 j.2).hom.continuous)⟩

/-- Every original point belongs to a characteristic closed disk. -/
theorem characteristicQuotient_surjective (X : TopCat.{u}) [CWComplex (Set.univ : Set X)] :
    Function.Surjective (characteristicQuotient X) := by
  intro x
  have hx : x ∈ ⋃ (n : ℕ) (j : cell (Set.univ : Set X) n), closedCell n j := by
    rw [CWComplex.union]
    exact Set.mem_univ _
  simp only [Set.mem_iUnion] at hx
  obtain ⟨n, j, y, hy, hxy⟩ := hx
  exact ⟨⟨⟨n, j⟩, ULift.up ⟨y, hy⟩⟩, hxy⟩

/-- The classical weak topology is the actual characteristic quotient topology
of the given original Hausdorff space. -/
theorem isQuotientMap_characteristicQuotient (X : TopCat.{u})
    [T2Space X] [CWComplex (Set.univ : Set X)] :
    IsQuotientMap (characteristicQuotient X) := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨characteristicQuotient_surjective X, ?_⟩
  intro A
  constructor
  · intro hA
    exact hA.preimage (characteristicQuotient X).hom.continuous
  · intro hA
    apply CWComplex.closed' A (Set.subset_univ _)
    intro n j
    have hj : IsClosed ((characteristicDiskMap n j) ⁻¹' A) :=
      (isClosed_sigma_iff.mp hA) ⟨n, j⟩
    have hcompact := hj.isCompact.image (characteristicDiskMap n j).hom.continuous
    have heq : characteristicDiskMap n j '' ((characteristicDiskMap n j) ⁻¹' A) =
        A ∩ closedCell (C := (Set.univ : Set X)) n j := by
      rw [Set.image_preimage_eq_inter_range, range_characteristicDiskMap]
    rw [heq] at hcompact
    exact hcompact.isClosed

/-- The actual subspace of cells of dimension strictly below `n`. The zero
stage is empty; stage `n+1` adds exactly the given `n`-cells. -/
abbrev skeletonTop (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
    (n : ℕ) : TopCat.{u} :=
  TopCat.of {x : X // x ∈ (skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X)}

/-- The actual inclusion of a skeleton in the original space. -/
def skeletonInclusion (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    skeletonTop X n ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- A classical skeleton is genuinely a closed subspace of the Hausdorff model. -/
theorem isClosedEmbedding_skeletonInclusion (X : TopCat.{u})
    [T2Space X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    IsClosedEmbedding (skeletonInclusion X n) :=
  IsClosedEmbedding.subtypeVal (skeletonLT (Set.univ : Set X) (n : ℕ∞)).closed

/-- The actual stage transition, given by inclusion of the original skeleta. -/
def skeletonTransition (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    skeletonTop X n ⟶ skeletonTop X (n + 1) :=
  TopCat.ofHom
    ⟨Set.inclusion (skeletonLT_mono (C := (Set.univ : Set X))
        (n := ((n + 1 : ℕ) : ℕ∞)) (m := (n : ℕ∞)) (by exact_mod_cast Nat.le_succ n)),
      continuous_subtype_val.subtype_mk _⟩

@[simp]
theorem skeletonTransition_comp_inclusion (X : TopCat.{u})
    [T2Space X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    skeletonTransition X n ≫ skeletonInclusion X (n + 1) = skeletonInclusion X n := rfl

/-- The actual disk-to-successor-skeleton map. -/
def characteristicDiskToSkeleton [T2Space X] (n : ℕ) (j : cell (Set.univ : Set X) n) :
    (classicalCellDiskPair.{u} n).fst ⟶ skeletonTop X (n + 1) :=
  TopCat.ofHom
    ⟨fun x => ⟨characteristicDiskMap n j x,
        closedCell_subset_skeletonLT n j ⟨x.down.val, x.down.property, rfl⟩⟩,
      (characteristicDiskMap n j).hom.continuous.subtype_mk _⟩

/-- The actual attaching map of the boundary to the preceding skeleton. -/
def characteristicSphereToSkeleton [T2Space X] (n : ℕ) (j : cell (Set.univ : Set X) n) :
    (classicalCellDiskPair.{u} n).snd ⟶ skeletonTop X n :=
  TopCat.ofHom
    ⟨fun x => ⟨characteristicSphereMap n j x,
        cellFrontier_subset_skeletonLT n j ⟨x.down.val, x.down.property, rfl⟩⟩,
      (characteristicSphereMap n j).hom.continuous.subtype_mk _⟩

/-- The square uses exactly the given characteristic boundary maps. -/
theorem characteristic_attachment_square [T2Space X] (n : ℕ) (j : cell (Set.univ : Set X) n) :
    characteristicSphereToSkeleton n j ≫ skeletonTransition X n =
      (classicalCellDiskPair.{u} n).map ≫ characteristicDiskToSkeleton n j := rfl

/-- The actual disjoint sum of all disks of one dimension. -/
abbrev CellDisksAt (X : TopCat.{u}) [CWComplex (Set.univ : Set X)] (n : ℕ) :=
  Σ _ : cell (Set.univ : Set X) n, (classicalCellDiskPair.{u} n).fst

/-- The actual disjoint sum of their attaching spheres. -/
abbrev CellSpheresAt (X : TopCat.{u}) [CWComplex (Set.univ : Set X)] (n : ℕ) :=
  Σ _ : cell (Set.univ : Set X) n, (classicalCellDiskPair.{u} n).snd

/-- All characteristic disk maps of one dimension, on the actual coproduct. -/
def diskSumToSkeleton (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    TopCat.of (CellDisksAt X n) ⟶ skeletonTop X (n + 1) :=
  TopCat.ofHom
    ⟨fun x => characteristicDiskToSkeleton n x.1 x.2,
      continuous_sigma (fun j => (characteristicDiskToSkeleton n j).hom.continuous)⟩

/-- All attaching maps of one dimension, on the actual coproduct. -/
def sphereSumToSkeleton (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    TopCat.of (CellSpheresAt X n) ⟶ skeletonTop X n :=
  TopCat.ofHom
    ⟨fun x => characteristicSphereToSkeleton n x.1 x.2,
      continuous_sigma (fun j => (characteristicSphereToSkeleton n j).hom.continuous)⟩

/-- The actual coproduct of sphere-to-disk inclusions. -/
def sphereSumToDiskSum (X : TopCat.{u}) [CWComplex (Set.univ : Set X)] (n : ℕ) :
    TopCat.of (CellSpheresAt X n) ⟶ TopCat.of (CellDisksAt X n) :=
  TopCat.ofHom
    ⟨fun x => ⟨x.1, (classicalCellDiskPair.{u} n).map x.2⟩,
      continuous_sigma (fun j => (continuous_sigmaMk (i := j)).comp
        (classicalCellDiskPair.{u} n).map.hom.continuous)⟩

/-- The actual successor skeleton is covered by the preceding skeleton and its
new characteristic disks. -/
def skeletonAttachmentQuotient (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] (n : ℕ) :
    TopCat.of (skeletonTop X n ⊕ CellDisksAt X n) ⟶ skeletonTop X (n + 1) :=
  TopCat.ofHom
    ⟨Sum.elim (skeletonTransition X n) (diskSumToSkeleton X n),
      (skeletonTransition X n).hom.continuous.sumElim (diskSumToSkeleton X n).hom.continuous⟩

/-- The covering is onto the literal successor subspace of the original model. -/
theorem skeletonAttachmentQuotient_surjective (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] (n : ℕ) :
    Function.Surjective (skeletonAttachmentQuotient X n) := by
  intro x
  let y : X := x.val
  have hx : y ∈ (skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) ∪
      ⋃ j : cell (Set.univ : Set X) n, closedCell n j := by
    rw [skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ]
    simpa only [Nat.cast_add, Nat.cast_one] using x.property
  rcases hx with hx | hx
  · exact ⟨Sum.inl ⟨x.val, hx⟩, rfl⟩
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨j, y, hy, hyx⟩ := hx
    exact ⟨Sum.inr ⟨j, ULift.up ⟨y, hy⟩⟩, Subtype.ext hyx⟩

/-- The old-stage image of a pulled-back set is its intersection with the old
skeletal subspace in the original model. -/
theorem skeleton_image_preimage_transition (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] (n : ℕ) (A : Set (skeletonTop X (n + 1))) :
    skeletonInclusion X n '' ((skeletonTransition X n) ⁻¹' A) =
      skeletonInclusion X (n + 1) '' A ∩ (skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨skeletonTransition X n y, hy, rfl⟩, y.property⟩
  · rintro ⟨⟨y, hy, hxy⟩, hx⟩
    let z : skeletonTop X n := ⟨x, hx⟩
    have hz : skeletonTransition X n z = y := Subtype.ext hxy.symm
    refine ⟨z, ?_, rfl⟩
    change skeletonTransition X n z ∈ A
    rw [hz]
    exact hy

/-- The image of a new disk's pulled-back set is its intersection with the
actual characteristic closed cell. -/
theorem characteristic_image_preimage_skeleton (n : ℕ) (j : cell (Set.univ : Set X) n)
    [T2Space X] (A : Set (skeletonTop X (n + 1))) :
    characteristicDiskMap n j '' ((characteristicDiskToSkeleton n j) ⁻¹' A) =
      skeletonInclusion X (n + 1) '' A ∩ closedCell n j := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨characteristicDiskToSkeleton n j y, hy, rfl⟩,
      y.down.val, y.down.property, rfl⟩
  · rintro ⟨⟨y, hy, hyx⟩, hx⟩
    obtain ⟨z, hz⟩ := (range_characteristicDiskMap n j).symm ▸ hx
    have hzy : characteristicDiskToSkeleton n j z = y := Subtype.ext (hz.trans hyx.symm)
    refine ⟨z, ?_, hz⟩
    change characteristicDiskToSkeleton n j z ∈ A
    rw [hzy]
    exact hy

/-- Hatcher's characteristic-quotient argument on the actual successor skeleton.
Higher-dimensional cell intersections are closed by the finite lower frontier
induction; no quotient presentation is supplied as an input. -/
theorem isQuotientMap_skeletonAttachmentQuotient (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] (n : ℕ) :
    IsQuotientMap (skeletonAttachmentQuotient X n) := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨skeletonAttachmentQuotient_surjective X n, ?_⟩
  intro A
  constructor
  · intro hA
    exact hA.preimage (skeletonAttachmentQuotient X n).hom.continuous
  · intro hA
    let B := skeletonInclusion X (n + 1) '' A
    have hB : B ⊆ (skeletonLT (Set.univ : Set X) ((n + 1 : ℕ) : ℕ∞) : Set X) := by
      rintro x ⟨y, _, rfl⟩
      exact y.property
    have hold : IsClosed (B ∩ (skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X)) := by
      rw [← skeleton_image_preimage_transition]
      exact (isClosedEmbedding_skeletonInclusion X n).isClosedMap _
        (hA.preimage continuous_inl)
    have hnew (j : cell (Set.univ : Set X) n) : IsClosed (B ∩ closedCell n j) := by
      rw [← characteristic_image_preimage_skeleton]
      have hj : IsClosed ((characteristicDiskToSkeleton n j) ⁻¹' A) :=
        (hA.preimage continuous_inr).preimage continuous_sigmaMk
      exact (hj.isCompact.image (characteristicDiskMap n j).hom.continuous).isClosed
    have hcells : ∀ m : ℕ, ∀ j : cell (Set.univ : Set X) m, IsClosed (B ∩ closedCell m j) := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro j
        by_cases hmn : m < n
        · have hsub : closedCell m j ⊆ (skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) :=
            (closedCell_subset_skeletonLT m j).trans
              (skeletonLT_mono (by exact_mod_cast Nat.succ_le_of_lt hmn))
          have heq : B ∩ closedCell m j =
              (B ∩ (skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X)) ∩ closedCell m j := by
            rw [Set.inter_assoc, Set.inter_eq_right.mpr hsub]
          rw [heq]
          exact hold.inter isClosed_closedCell
        · by_cases hmn' : m = n
          · subst m
            exact hnew j
          · have hnm : n + 1 ≤ m := by omega
            have heq : B ∩ closedCell m j = B ∩ cellFrontier m j := by
              apply Set.Subset.antisymm
              · rintro x ⟨hxB, hx⟩
                have hx' : x ∈ (skeletonLT (Set.univ : Set X) ((n + 1 : ℕ) : ℕ∞) : Set X) ∩
                    closedCell m j := ⟨hB hxB, hx⟩
                rw [skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier
                  (by exact_mod_cast hnm)] at hx'
                exact ⟨hxB, hx'.2⟩
              · exact Set.inter_subset_inter_right _ (cellFrontier_subset_closedCell m j)
            rw [heq]
            cases m with
            | zero => omega
            | succ m =>
              exact isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
                (fun k hk i => ih k (Nat.lt_succ_of_le hk) i) j
    have hclosedB : IsClosed B := CWComplex.closed' B (Set.subset_univ _) hcells
    have heq : (skeletonInclusion X (n + 1)) ⁻¹' B = A :=
      Set.preimage_image_eq A (isClosedEmbedding_skeletonInclusion X (n + 1)).injective
    rw [← heq]
    exact hclosedB.preimage (skeletonInclusion X (n + 1)).hom.continuous

/-- A characteristic disk point landing in the old skeleton belongs to its
boundary; its actual sphere preimage is retained. -/
theorem exists_sphere_preimage_of_disk_mem_skeleton [T2Space X]
    (n : ℕ) (j : cell (Set.univ : Set X) n) (d : (classicalCellDiskPair.{u} n).fst)
    (hd : characteristicDiskMap n j d ∈ (skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X)) :
    ∃ b : (classicalCellDiskPair.{u} n).snd, (classicalCellDiskPair.{u} n).map b = d := by
  have hnot : d.down.val ∉ Metric.ball (0 : Fin n → ℝ) 1 := by
    intro hball
    exact Set.disjoint_left.mp (disjoint_skeletonLT_openCell (C := Set.univ) (n := (n : ℕ∞))
      (m := n) le_rfl) hd ⟨d.down.val, hball, rfl⟩
  have hs : d.down.val ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    rw [Metric.mem_ball] at hnot
    rw [Metric.mem_sphere]
    exact le_antisymm (Metric.mem_closedBall.mp d.down.property) (le_of_not_gt hnot)
  exact ⟨ULift.up ⟨d.down.val, hs⟩, rfl⟩

/-- If a disk image does not lie in the old skeleton, its coordinate is in
the genuine characteristic interior. -/
theorem disk_interior_of_image_not_mem_skeleton [T2Space X]
    (n : ℕ) (j : cell (Set.univ : Set X) n) (d : (classicalCellDiskPair.{u} n).fst)
    (hd : characteristicDiskMap n j d ∉ (skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X)) :
    d.down.val ∈ Metric.ball (0 : Fin n → ℝ) 1 := by
  by_contra hball
  have hs : d.down.val ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    rw [Metric.mem_ball] at hball
    rw [Metric.mem_sphere]
    exact le_antisymm (Metric.mem_closedBall.mp d.down.property) (le_of_not_gt hball)
  exact hd (cellFrontier_subset_skeletonLT n j ⟨d.down.val, hs, rfl⟩)

section Descent

variable {Y : Type*} [TopologicalSpace Y] [T2Space X]

/-- Compatibility identifies an old-stage value with any disk value above
the same original point. -/
theorem compatible_old_disk (n : ℕ) (f : C(skeletonTop X n, Y))
    (g : C(CellDisksAt X n, Y))
    (h : ∀ b : CellSpheresAt X n, f (sphereSumToSkeleton X n b) = g (sphereSumToDiskSum X n b))
    (j : cell (Set.univ : Set X) n) (d : (classicalCellDiskPair.{u} n).fst)
    (x : skeletonTop X n)
    (hx : skeletonAttachmentQuotient X n (Sum.inl x) =
      skeletonAttachmentQuotient X n (Sum.inr ⟨j, d⟩)) : f x = g ⟨j, d⟩ := by
  have hxv : x.val = characteristicDiskMap n j d := congrArg Subtype.val hx
  have hd : characteristicDiskMap n j d ∈ (skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) := by
    rw [← hxv]
    exact x.property
  obtain ⟨b, hb⟩ := exists_sphere_preimage_of_disk_mem_skeleton n j d hd
  have hbv : b.down.val = d.down.val :=
    congrArg (fun z : (classicalCellDiskPair.{u} n).fst => z.down.val) hb
  have hsource : sphereSumToSkeleton X n ⟨j, b⟩ = x := by
    apply Subtype.ext
    change map n j b.down.val = x.val
    rw [hbv]
    exact hxv.symm
  calc
    f x = f (sphereSumToSkeleton X n ⟨j, b⟩) := congrArg f hsource.symm
    _ = g (sphereSumToDiskSum X n ⟨j, b⟩) := h ⟨j, b⟩
    _ = g ⟨j, d⟩ := congrArg (fun z : (classicalCellDiskPair.{u} n).fst => g ⟨j, z⟩) hb

/-- Compatibility identifies two actual disk values with the same original
image. Outside the old skeleton, disjoint interiors and the classical partial
equivalence prove equality of their cell identifiers and coordinates. -/
theorem compatible_disk_disk (n : ℕ) (f : C(skeletonTop X n, Y))
    (g : C(CellDisksAt X n, Y))
    (h : ∀ b : CellSpheresAt X n, f (sphereSumToSkeleton X n b) = g (sphereSumToDiskSum X n b))
    (j k : cell (Set.univ : Set X) n) (d e : (classicalCellDiskPair.{u} n).fst)
    (hx : skeletonAttachmentQuotient X n (Sum.inr ⟨j, d⟩) =
      skeletonAttachmentQuotient X n (Sum.inr ⟨k, e⟩)) : g ⟨j, d⟩ = g ⟨k, e⟩ := by
  have hv : characteristicDiskMap n j d = characteristicDiskMap n k e := congrArg Subtype.val hx
  by_cases hd : characteristicDiskMap n j d ∈ (skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X)
  · let x : skeletonTop X n := ⟨characteristicDiskMap n j d, hd⟩
    have hxj : skeletonAttachmentQuotient X n (Sum.inl x) =
        skeletonAttachmentQuotient X n (Sum.inr ⟨j, d⟩) := rfl
    have hxk : skeletonAttachmentQuotient X n (Sum.inl x) =
        skeletonAttachmentQuotient X n (Sum.inr ⟨k, e⟩) := hxj.trans hx
    exact (compatible_old_disk n f g h j d x hxj).symm.trans
      (compatible_old_disk n f g h k e x hxk)
  · have he : characteristicDiskMap n k e ∉
        (skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) := fun he => hd (hv.symm ▸ he)
    have hd' := disk_interior_of_image_not_mem_skeleton n j d hd
    have he' := disk_interior_of_image_not_mem_skeleton n k e he
    have hcells : ¬ Disjoint (openCell (C := (Set.univ : Set X)) n j) (openCell n k) := by
      intro hdis
      exact Set.disjoint_left.mp hdis ⟨d.down.val, hd', rfl⟩ ⟨e.down.val, he', hv.symm⟩
    have hjk : j = k := by simpa using eq_of_not_disjoint_openCell hcells
    subst k
    have hde : d.down.val = e.down.val := (map n j).injOn
      (by rw [source_eq]; exact hd') (by rw [source_eq]; exact he') hv
    have hde' : d = e := ULift.down_injective (Subtype.ext hde)
    rw [hde']

/-- Every compatible family is constant on the fibres of the actual
old-stage/disks quotient, in an independent target universe. -/
theorem skeleton_family_factors (n : ℕ) (f : C(skeletonTop X n, Y))
    (g : C(CellDisksAt X n, Y))
    (h : ∀ b : CellSpheresAt X n, f (sphereSumToSkeleton X n b) = g (sphereSumToDiskSum X n b)) :
    Function.FactorsThrough (Sum.elim f g) (skeletonAttachmentQuotient X n) := by
  intro a b hab
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      have hxy : x = y := Subtype.ext (congrArg (fun z : skeletonTop X (n + 1) => z.val) hab)
      exact congrArg f hxy
    | inr y => exact compatible_old_disk n f g h y.1 y.2 x hab
  | inr x =>
    cases b with
    | inl y => exact (compatible_old_disk n f g h x.1 x.2 y hab.symm).symm
    | inr y => exact compatible_disk_disk n f g h x.1 y.1 x.2 y.2 hab

/-- Descend the actual compatible maps along the proved successor quotient. -/
def skeletonGlue (n : ℕ) (f : C(skeletonTop X n, Y)) (g : C(CellDisksAt X n, Y))
    (h : ∀ b : CellSpheresAt X n, f (sphereSumToSkeleton X n b) = g (sphereSumToDiskSum X n b)) :
    C(skeletonTop X (n + 1), Y) :=
  (isQuotientMap_skeletonAttachmentQuotient X n).lift
    ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩ (skeleton_family_factors n f g h)

theorem skeletonGlue_left (n : ℕ) (f : C(skeletonTop X n, Y)) (g : C(CellDisksAt X n, Y))
    (h : ∀ b : CellSpheresAt X n, f (sphereSumToSkeleton X n b) = g (sphereSumToDiskSum X n b))
    (x : skeletonTop X n) : skeletonGlue n f g h (skeletonTransition X n x) = f x := by
  exact DFunLike.congr_fun ((isQuotientMap_skeletonAttachmentQuotient X n).lift_comp
    ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩ (skeleton_family_factors n f g h)) (Sum.inl x)

theorem skeletonGlue_right (n : ℕ) (f : C(skeletonTop X n, Y)) (g : C(CellDisksAt X n, Y))
    (h : ∀ b : CellSpheresAt X n, f (sphereSumToSkeleton X n b) = g (sphereSumToDiskSum X n b))
    (x : CellDisksAt X n) : skeletonGlue n f g h (diskSumToSkeleton X n x) = g x := by
  exact DFunLike.congr_fun ((isQuotientMap_skeletonAttachmentQuotient X n).lift_comp
    ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩ (skeleton_family_factors n f g h)) (Sum.inr x)

end Descent

/-- The actual characteristic attaching cocone of a successor skeleton. -/
def skeletonPushoutCocone (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    PushoutCocone (sphereSumToSkeleton X n) (sphereSumToDiskSum X n) :=
  PushoutCocone.mk (skeletonTransition X n) (diskSumToSkeleton X n) rfl

/-- The ordinary successor skeleton satisfies the full pushout universal
property through the actual characteristic quotient. -/
def skeletonPushoutIsColimit (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    IsColimit (skeletonPushoutCocone X n) := by
  apply PushoutCocone.isColimitAux'
  intro s
  have h (b : CellSpheresAt X n) : s.inl (sphereSumToSkeleton X n b) =
      s.inr (sphereSumToDiskSum X n b) := ConcreteCategory.congr_hom s.condition b
  let l : skeletonTop X (n + 1) ⟶ s.pt :=
    TopCat.ofHom (skeletonGlue n s.inl.hom s.inr.hom h)
  have hl : skeletonTransition X n ≫ l = s.inl := by
    apply TopCat.ext
    intro x
    exact skeletonGlue_left n s.inl.hom s.inr.hom h x
  have hr : diskSumToSkeleton X n ≫ l = s.inr := by
    apply TopCat.ext
    intro x
    exact skeletonGlue_right n s.inl.hom s.inr.hom h x
  refine ⟨l, hl, hr, ?_⟩
  intro m hmleft hmright
  apply TopCat.ext
  intro x
  obtain ⟨z, rfl⟩ := skeletonAttachmentQuotient_surjective X n x
  cases z with
  | inl y =>
    exact (ConcreteCategory.congr_hom hmleft y).trans (ConcreteCategory.congr_hom hl y).symm
  | inr y =>
    exact (ConcreteCategory.congr_hom hmright y).trans (ConcreteCategory.congr_hom hr y).symm

/-- The actual old-skeleton/new-disks square is a categorical pushout. -/
theorem isPushout_skeletonAttachment (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] (n : ℕ) :
    IsPushout (sphereSumToSkeleton X n) (sphereSumToDiskSum X n)
      (skeletonTransition X n) (diskSumToSkeleton X n) :=
  IsPushout.of_isColimit (skeletonPushoutIsColimit X n)

/-- The actual disjoint sum of original skeletal subspaces. -/
abbrev SkeletalUnion (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] :=
  Σ n : ℕ, skeletonTop X n

/-- The dimension-union map has the original CW model as its literal target. -/
def skeletalUnionQuotient (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] :
    TopCat.of (SkeletalUnion X) ⟶ X :=
  TopCat.ofHom ⟨fun x => skeletonInclusion X x.1 x.2,
    continuous_sigma (fun n => (skeletonInclusion X n).hom.continuous)⟩

theorem skeletalUnionQuotient_surjective (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] : Function.Surjective (skeletalUnionQuotient X) := by
  intro x
  obtain ⟨⟨⟨n, j⟩, d⟩, rfl⟩ := characteristicQuotient_surjective X x
  exact ⟨⟨n + 1, characteristicDiskToSkeleton n j d⟩, rfl⟩

/-- The classical weak topology is also the quotient topology of the actual
dimension union, with no asserted replacement of the original space. -/
theorem isQuotientMap_skeletalUnionQuotient (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] : IsQuotientMap (skeletalUnionQuotient X) := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨skeletalUnionQuotient_surjective X, ?_⟩
  intro A
  constructor
  · intro hA
    exact hA.preimage (skeletalUnionQuotient X).hom.continuous
  · intro hA
    apply CWComplex.closed' A (Set.subset_univ _)
    intro n j
    have hn : IsClosed ((skeletonInclusion X (n + 1)) ⁻¹' A) := (isClosed_sigma_iff.mp hA) (n + 1)
    have hj : IsClosed ((characteristicDiskMap n j) ⁻¹' A) :=
      hn.preimage (characteristicDiskToSkeleton n j).hom.continuous
    have hc := hj.isCompact.image (characteristicDiskMap n j).hom.continuous
    have heq : characteristicDiskMap n j '' ((characteristicDiskMap n j) ⁻¹' A) =
        A ∩ closedCell (C := (Set.univ : Set X)) n j := by
      rw [Set.image_preimage_eq_inter_range, range_characteristicDiskMap]
    rw [heq] at hc
    exact hc.isClosed

/-- Boundary HEP is constructed from the actual classical disk-cylinder retraction,
with an independent universe for the target space. -/
def classicalDiskHomotopyExtension (n : ℕ) {Y : Type*} [TopologicalSpace Y]
    (f : C((classicalCellDiskPair.{u} n).fst, Y))
    (H : C(unitInterval × (classicalCellDiskPair.{u} n).snd, Y))
    (h0 : ∀ b, H (0, b) = f ((classicalCellDiskPair.{u} n).map b)) :
    Topology.HomotopyExtensionData (classicalCellDiskPair.{u} n).map.hom f H h0 :=
  ((classicalCellDiskPairNDRData.{u} n).toStandard.hurewiczCofibrationData).homotopyExtension f H h0

section SubcomplexExtension

variable [T2Space X] {Y : Type*} [TopologicalSpace Y]

/-- The literal inclusion of a classical subcomplex in the original model. -/
def subcomplexInclusion (A : Subcomplex (Set.univ : Set X)) : TopCat.of (A : Set X) ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

omit [T2Space X] in
theorem isClosedEmbedding_subcomplexInclusion (A : Subcomplex (Set.univ : Set X)) :
    IsClosedEmbedding (subcomplexInclusion A) := IsClosedEmbedding.subtypeVal A.closed

/-- A homotopy already constructed on one actual skeleton, with both its
initial map and its prescribed restriction to the original subcomplex. -/
structure SkeletonHomotopyData (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) (n : ℕ) where
  /-- The jointly continuous homotopy on this original skeletal subspace. -/
  homotopy : C(unitInterval × skeletonTop X n, Y)
  at_zero (x : skeletonTop X n) : homotopy (0, x) = f x.val
  on_subcomplex (t : unitInterval) (x : skeletonTop X n) (hx : x.val ∈ A) :
    homotopy (t, x) = H (t, ⟨x.val, hx⟩)

/-- A characteristic disk of a cell in the subcomplex lands there literally. -/
def diskToSubcomplexOfMem (A : Subcomplex (Set.univ : Set X)) (n : ℕ)
    (j : cell (Set.univ : Set X) n) (hj : j ∈ A.I n) :
    C((classicalCellDiskPair.{u} n).fst, (A : Set X)) :=
  ⟨fun d => ⟨characteristicDiskMap n j d,
      A.closedCell_subset_of_mem hj ⟨d.down.val, d.down.property, rfl⟩⟩,
    (characteristicDiskMap n j).hom.continuous.subtype_mk _⟩

omit [T2Space X] in
/-- A cell outside a subcomplex meets that subcomplex only on its actual
attaching sphere, whose point is retained. -/
theorem exists_sphere_preimage_of_disk_mem_subcomplex (A : Subcomplex (Set.univ : Set X))
    (n : ℕ) (j : cell (Set.univ : Set X) n) (hj : j ∉ A.I n)
    (d : (classicalCellDiskPair.{u} n).fst) (hd : characteristicDiskMap n j d ∈ A) :
    ∃ b : (classicalCellDiskPair.{u} n).snd, (classicalCellDiskPair.{u} n).map b = d := by
  have hnot : d.down.val ∉ Metric.ball (0 : Fin n → ℝ) 1 := by
    intro hball
    exact Set.disjoint_left.mp (A.disjoint_openCell_subcomplex_of_notMem hj)
      ⟨d.down.val, hball, rfl⟩ hd
  have hs : d.down.val ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    rw [Metric.mem_ball] at hnot
    rw [Metric.mem_sphere]
    exact le_antisymm (Metric.mem_closedBall.mp d.down.property) (le_of_not_gt hnot)
  exact ⟨ULift.up ⟨d.down.val, hs⟩, rfl⟩

/-- Actual homotopy data on one new disk, compatible with the old skeleton
and with the prescribed entire subcomplex. -/
structure CellHomotopyData (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) (n : ℕ) (j : cell (Set.univ : Set X) n)
    (s : SkeletonHomotopyData A f H n) where
  /-- The jointly continuous homotopy on this actual characteristic disk. -/
  homotopy : C(unitInterval × (classicalCellDiskPair.{u} n).fst, Y)
  at_zero (d : (classicalCellDiskPair.{u} n).fst) :
    homotopy (0, d) = f (characteristicDiskMap n j d)
  on_boundary (t : unitInterval) (b : (classicalCellDiskPair.{u} n).snd) :
    homotopy (t, (classicalCellDiskPair.{u} n).map b) =
      s.homotopy (t, characteristicSphereToSkeleton n j b)
  on_subcomplex (t : unitInterval) (d : (classicalCellDiskPair.{u} n).fst)
      (hd : characteristicDiskMap n j d ∈ A) :
    homotopy (t, d) = H (t, ⟨characteristicDiskMap n j d, hd⟩)

/-- Construct a new cell's homotopy: preserve the supplied subcomplex
homotopy on its cells, and use actual disk-cylinder HEP on all other cells. -/
def extendCellHomotopy (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) (h0 : ∀ a : (A : Set X), H (0, a) = f a.val)
    (n : ℕ) (j : cell (Set.univ : Set X) n) (s : SkeletonHomotopyData A f H n) :
    CellHomotopyData A f H n j s := by
  classical
  by_cases hj : j ∈ A.I n
  · let dA := diskToSubcomplexOfMem A n j hj
    let Hd : C(unitInterval × (classicalCellDiskPair.{u} n).fst, Y) :=
      H.comp (ContinuousMap.fst.prodMk (dA.comp ContinuousMap.snd))
    refine ⟨Hd, ?_, ?_, ?_⟩
    · intro d
      exact h0 (dA d)
    · intro t b
      have hb : (characteristicSphereToSkeleton n j b).val ∈ A :=
        A.closedCell_subset_of_mem hj
          ⟨b.down.val, Metric.sphere_subset_closedBall b.down.property, rfl⟩
      exact (s.on_subcomplex t (characteristicSphereToSkeleton n j b) hb).symm
    · intro t d hd
      rfl
  · let fb := f.comp (characteristicDiskMap n j).hom
    let Hb : C(unitInterval × (classicalCellDiskPair.{u} n).snd, Y) :=
      s.homotopy.comp (ContinuousMap.fst.prodMk
        ((characteristicSphereToSkeleton n j).hom.comp ContinuousMap.snd))
    have hb0 (b : (classicalCellDiskPair.{u} n).snd) :
        Hb (0, b) = fb ((classicalCellDiskPair.{u} n).map b) :=
      s.at_zero (characteristicSphereToSkeleton n j b)
    let E := classicalDiskHomotopyExtension n fb Hb hb0
    refine ⟨E.extension, E.extension_zero, E.extension_subspace, ?_⟩
    intro t d hd
    obtain ⟨b, hb⟩ := exists_sphere_preimage_of_disk_mem_subcomplex A n j hj d hd
    have hbd : characteristicDiskMap n j ((classicalCellDiskPair.{u} n).map b) =
        characteristicDiskMap n j d :=
      congrArg (characteristicDiskMap n j) hb
    have hAb : (characteristicSphereToSkeleton n j b).val ∈ A := by
      change characteristicDiskMap n j ((classicalCellDiskPair.{u} n).map b) ∈ A
      rw [hbd]
      exact hd
    calc
      E.extension (t, d) = E.extension (t, (classicalCellDiskPair.{u} n).map b) :=
        congrArg (fun z => E.extension (t, z)) hb.symm
      _ = Hb (t, b) := E.extension_subspace t b
      _ = H (t, ⟨(characteristicSphereToSkeleton n j b).val, hAb⟩) :=
        s.on_subcomplex t (characteristicSphereToSkeleton n j b) hAb
      _ = H (t, ⟨characteristicDiskMap n j d, hd⟩) :=
        congrArg (fun a : (A : Set X) => H (t, a)) (Subtype.ext hbd)

/-- Joint homotopies on the old skeleton and all new disks glue through the
proved characteristic quotient. Currying uses the actual compact interval,
so the resulting homotopy is continuous in the ordinary product topology. -/
def glueSkeletonHomotopy (n : ℕ) (L : C(unitInterval × skeletonTop X n, Y))
    (R : cell (Set.univ : Set X) n → C(unitInterval × (classicalCellDiskPair.{u} n).fst, Y))
    (h : ∀ (t : unitInterval) (b : CellSpheresAt X n),
      L (t, sphereSumToSkeleton X n b) = R b.1 (t, (classicalCellDiskPair.{u} n).map b.2)) :
    C(unitInterval × skeletonTop X (n + 1), Y) := by
  let f := (L.comp ContinuousMap.prodSwap).curry
  let g : C(CellDisksAt X n, C(unitInterval, Y)) :=
    ⟨fun x => (R x.1).comp ContinuousMap.prodSwap |>.curry x.2,
      continuous_sigma (fun j => ((R j).comp ContinuousMap.prodSwap).curry.continuous)⟩
  have hb (b : CellSpheresAt X n) :
      f (sphereSumToSkeleton X n b) = g (sphereSumToDiskSum X n b) := by
    apply ContinuousMap.ext
    intro t
    exact h t b
  exact (skeletonGlue n f g hb).uncurry.comp ContinuousMap.prodSwap

theorem glueSkeletonHomotopy_left (n : ℕ) (L : C(unitInterval × skeletonTop X n, Y))
    (R : cell (Set.univ : Set X) n → C(unitInterval × (classicalCellDiskPair.{u} n).fst, Y))
    (h : ∀ (t : unitInterval) (b : CellSpheresAt X n),
      L (t, sphereSumToSkeleton X n b) = R b.1 (t, (classicalCellDiskPair.{u} n).map b.2))
    (t : unitInterval) (x : skeletonTop X n) :
    glueSkeletonHomotopy n L R h (t, skeletonTransition X n x) = L (t, x) := by
  let f := (L.comp ContinuousMap.prodSwap).curry
  let g : C(CellDisksAt X n, C(unitInterval, Y)) :=
    ⟨fun y => ((R y.1).comp ContinuousMap.prodSwap).curry y.2,
      continuous_sigma (fun j => ((R j).comp ContinuousMap.prodSwap).curry.continuous)⟩
  have hb (b : CellSpheresAt X n) :
      f (sphereSumToSkeleton X n b) = g (sphereSumToDiskSum X n b) := by
    apply ContinuousMap.ext
    intro t
    exact h t b
  change (skeletonGlue n f g hb (skeletonTransition X n x)) t = L (t, x)
  rw [skeletonGlue_left]
  rfl

theorem glueSkeletonHomotopy_right (n : ℕ) (L : C(unitInterval × skeletonTop X n, Y))
    (R : cell (Set.univ : Set X) n → C(unitInterval × (classicalCellDiskPair.{u} n).fst, Y))
    (h : ∀ (t : unitInterval) (b : CellSpheresAt X n),
      L (t, sphereSumToSkeleton X n b) = R b.1 (t, (classicalCellDiskPair.{u} n).map b.2))
    (t : unitInterval) (j : cell (Set.univ : Set X) n) (d : (classicalCellDiskPair.{u} n).fst) :
    glueSkeletonHomotopy n L R h (t, characteristicDiskToSkeleton n j d) = R j (t, d) := by
  let f := (L.comp ContinuousMap.prodSwap).curry
  let g : C(CellDisksAt X n, C(unitInterval, Y)) :=
    ⟨fun y => ((R y.1).comp ContinuousMap.prodSwap).curry y.2,
      continuous_sigma (fun j => ((R j).comp ContinuousMap.prodSwap).curry.continuous)⟩
  have hb (b : CellSpheresAt X n) :
      f (sphereSumToSkeleton X n b) = g (sphereSumToDiskSum X n b) := by
    apply ContinuousMap.ext
    intro t
    exact h t b
  change (skeletonGlue n f g hb (diskSumToSkeleton X n ⟨j, d⟩)) t = _
  rw [skeletonGlue_right]
  rfl

/-- The constructed successor homotopy has the prescribed initial map and
agrees with the homotopy on the entire original subcomplex. -/
def extendSkeletonHomotopy (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) (h0 : ∀ a : (A : Set X), H (0, a) = f a.val)
    (n : ℕ) (s : SkeletonHomotopyData A f H n) : SkeletonHomotopyData A f H (n + 1) := by
  let E (j : cell (Set.univ : Set X) n) := extendCellHomotopy A f H h0 n j s
  let R := fun j => (E j).homotopy
  have h (t : unitInterval) (b : CellSpheresAt X n) :
      s.homotopy (t, sphereSumToSkeleton X n b) =
        R b.1 (t, (classicalCellDiskPair.{u} n).map b.2) :=
    ((E b.1).on_boundary t b.2).symm
  refine ⟨glueSkeletonHomotopy n s.homotopy R h, ?_, ?_⟩
  · intro x
    obtain ⟨z, rfl⟩ := skeletonAttachmentQuotient_surjective X n x
    cases z with
    | inl y =>
      change glueSkeletonHomotopy n s.homotopy R h (0, skeletonTransition X n y) = _
      rw [glueSkeletonHomotopy_left]
      exact s.at_zero y
    | inr y =>
      change glueSkeletonHomotopy n s.homotopy R h (0, characteristicDiskToSkeleton n y.1 y.2) = _
      rw [glueSkeletonHomotopy_right]
      exact (E y.1).at_zero y.2
  · intro t x hx
    obtain ⟨z, rfl⟩ := skeletonAttachmentQuotient_surjective X n x
    cases z with
    | inl y =>
      change glueSkeletonHomotopy n s.homotopy R h (t, skeletonTransition X n y) = _
      rw [glueSkeletonHomotopy_left]
      exact s.on_subcomplex t y hx
    | inr y =>
      change glueSkeletonHomotopy n s.homotopy R h (t, characteristicDiskToSkeleton n y.1 y.2) = _
      rw [glueSkeletonHomotopy_right]
      exact (E y.1).on_subcomplex t y.2 hx

/-- Each successor extension fixes the entire preceding constructed homotopy. -/
theorem extendSkeletonHomotopy_restrict (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) (h0 : ∀ a : (A : Set X), H (0, a) = f a.val)
    (n : ℕ) (s : SkeletonHomotopyData A f H n) (t : unitInterval) (x : skeletonTop X n) :
    (extendSkeletonHomotopy A f H h0 n s).homotopy (t, skeletonTransition X n x) =
      s.homotopy (t, x) := by
  dsimp [extendSkeletonHomotopy]
  exact glueSkeletonHomotopy_left n _ _ _ t x

/-- The empty initial skeleton has its literal initial homotopy. -/
def initialSkeletonHomotopy (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) : SkeletonHomotopyData A f H 0 where
  homotopy := (f.comp (skeletonInclusion X 0).hom).comp ContinuousMap.snd
  at_zero _ := rfl
  on_subcomplex t x hx := by
    let y : X := x.val
    have hy : y ∈ (skeletonLT (Set.univ : Set X) (0 : ℕ∞) : Set X) := x.property
    rw [skeletonLT_zero_eq_empty] at hy
    exact hy.elim

/-- The actual sequence of compatible cellwise extensions on original skeleta. -/
def skeletalHomotopies (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) (h0 : ∀ a : (A : Set X), H (0, a) = f a.val) :
    (n : ℕ) → SkeletonHomotopyData A f H n
  | 0 => initialSkeletonHomotopy A f H
  | n + 1 => extendSkeletonHomotopy A f H h0 n (skeletalHomotopies A f H h0 n)

theorem skeletalHomotopies_succ_restrict (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) (h0 : ∀ a : (A : Set X), H (0, a) = f a.val)
    (n : ℕ) (t : unitInterval) (x : skeletonTop X n) :
    (skeletalHomotopies A f H h0 (n + 1)).homotopy (t, skeletonTransition X n x) =
      (skeletalHomotopies A f H h0 n).homotopy (t, x) :=
  extendSkeletonHomotopy_restrict A f H h0 n _ t x

/-- Inclusion between any two ordered actual skeletal subspaces. -/
def skeletonMapOfLE (n m : ℕ) (h : n ≤ m) : skeletonTop X n ⟶ skeletonTop X m :=
  TopCat.ofHom
    ⟨Set.inclusion (skeletonLT_mono (C := (Set.univ : Set X)) (by exact_mod_cast h)),
      continuous_subtype_val.subtype_mk _⟩

/-- All constructed skeletal homotopies have the same value after every
skeletal inclusion, not only after adjacent steps. -/
theorem skeletalHomotopies_le_restrict (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) (h0 : ∀ a : (A : Set X), H (0, a) = f a.val)
    (n m : ℕ) (hnm : n ≤ m) (t : unitInterval) (x : skeletonTop X n) :
    (skeletalHomotopies A f H h0 m).homotopy (t, skeletonMapOfLE n m hnm x) =
      (skeletalHomotopies A f H h0 n).homotopy (t, x) := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst n
      rfl
    · have hnm' : n ≤ m := by omega
      have hmap : skeletonMapOfLE n (m + 1) hnm x =
          skeletonTransition X m (skeletonMapOfLE n m hnm' x) := rfl
      rw [hmap, skeletalHomotopies_succ_restrict]
      exact ih hnm'

/-- The curried compatible homotopy on the actual disjoint dimension union. -/
def skeletalHomotopyFamily (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) (h0 : ∀ a : (A : Set X), H (0, a) = f a.val) :
    C(SkeletalUnion X, C(unitInterval, Y)) :=
  ⟨fun x => ((skeletalHomotopies A f H h0 x.1).homotopy.comp ContinuousMap.prodSwap).curry x.2,
    continuous_sigma (fun n =>
      ((skeletalHomotopies A f H h0 n).homotopy.comp ContinuousMap.prodSwap).curry.continuous)⟩

/-- Compatibility makes the entire constructed homotopy constant on fibres
of the actual dimension-union quotient onto the original space. -/
theorem skeletalHomotopyFamily_factors (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) (h0 : ∀ a : (A : Set X), H (0, a) = f a.val) :
    Function.FactorsThrough (skeletalHomotopyFamily A f H h0) (skeletalUnionQuotient X) := by
  rintro ⟨n, x⟩ ⟨m, y⟩ hxy
  apply ContinuousMap.ext
  intro t
  let k := max n m
  have hx := skeletalHomotopies_le_restrict A f H h0 n k (Nat.le_max_left n m) t x
  have hy := skeletalHomotopies_le_restrict A f H h0 m k (Nat.le_max_right n m) t y
  have hz : skeletonMapOfLE n k (Nat.le_max_left n m) x =
      skeletonMapOfLE m k (Nat.le_max_right n m) y := Subtype.ext hxy
  change (skeletalHomotopies A f H h0 n).homotopy (t, x) =
    (skeletalHomotopies A f H h0 m).homotopy (t, y)
  exact hx.symm.trans ((congrArg (fun z : skeletonTop X k =>
    (skeletalHomotopies A f H h0 k).homotopy (t, z)) hz).trans hy)

/-- The actual globally continuous extension on `I × X`, obtained by descending
the compatible skeletal family through the proved original-space quotient. -/
def subcomplexExtendedHomotopy (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) (h0 : ∀ a : (A : Set X), H (0, a) = f a.val) :
    C(unitInterval × X, Y) :=
  ((isQuotientMap_skeletalUnionQuotient X).lift (skeletalHomotopyFamily A f H h0)
    (skeletalHomotopyFamily_factors A f H h0)).uncurry.comp ContinuousMap.prodSwap

/-- The descended global homotopy retains every original skeletal value. -/
theorem subcomplexExtendedHomotopy_skeleton (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) (h0 : ∀ a : (A : Set X), H (0, a) = f a.val)
    (n : ℕ) (t : unitInterval) (x : skeletonTop X n) :
    subcomplexExtendedHomotopy A f H h0 (t, skeletonInclusion X n x) =
      (skeletalHomotopies A f H h0 n).homotopy (t, x) := by
  have h := DFunLike.congr_fun ((isQuotientMap_skeletalUnionQuotient X).lift_comp
    (skeletalHomotopyFamily A f H h0) (skeletalHomotopyFamily_factors A f H h0))
      (⟨n, x⟩ : SkeletalUnion X)
  exact DFunLike.congr_fun h t

/-- Chosen actual homotopy-extension data for every classical subcomplex of
the ordinary Hausdorff CW model, with an independent target universe. -/
def subcomplexHomotopyExtension (A : Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (H : C(unitInterval × (A : Set X), Y)) (h0 : ∀ a : (A : Set X), H (0, a) = f a.val) :
    Topology.HomotopyExtensionData (subcomplexInclusion A).hom f H h0 where
  extension := subcomplexExtendedHomotopy A f H h0
  extension_zero x := by
    obtain ⟨⟨n, y⟩, hxy⟩ := skeletalUnionQuotient_surjective X x
    change skeletonInclusion X n y = x at hxy
    rw [← hxy, subcomplexExtendedHomotopy_skeleton]
    exact (skeletalHomotopies A f H h0 n).at_zero y
  extension_subspace t a := by
    obtain ⟨⟨n, x⟩, hxa⟩ := skeletalUnionQuotient_surjective X a.val
    change skeletonInclusion X n x = a.val at hxa
    have hA : x.val ∈ A := by
      change skeletonInclusion X n x ∈ A
      rw [hxa]
      exact a.property
    change subcomplexExtendedHomotopy A f H h0 (t, a.val) = H (t, a)
    rw [← hxa, subcomplexExtendedHomotopy_skeleton]
    exact ((skeletalHomotopies A f H h0 n).on_subcomplex t x hA).trans
      (congrArg (fun z : (A : Set X) => H (t, z)) (Subtype.ext hxa))

/-- Every actual classical subcomplex inclusion has cross-universe HEP,
derived from its actual characteristic attachments and dimension quotient. -/
theorem subcomplexInclusion_hasHomotopyExtensionProperty
    (A : Subcomplex (Set.univ : Set X)) :
    Topology.HasHomotopyExtensionProperty.{u, v} (subcomplexInclusion A).hom := by
  intro Y instY f H h0
  exact ⟨subcomplexHomotopyExtension A f H h0⟩

/-- The corresponding actual subcomplex inclusion is a Hurewicz cofibration. -/
theorem subcomplexInclusion_isHurewiczCofibration (A : Subcomplex (Set.univ : Set X)) :
    TopCat.IsHurewiczCofibration (subcomplexInclusion A) :=
  subcomplexInclusion_hasHomotopyExtensionProperty A

end SubcomplexExtension

end Topology.CWComplex

end
