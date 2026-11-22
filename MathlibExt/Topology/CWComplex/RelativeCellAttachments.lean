/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.RelativeSkeletalFiltration

/-!
# Characteristic attachments of an actual relative CW filtration

The literal relative stage `A ∪ X^{n}` is the pushout that attaches the
original `n`-cells outside `A` to `A ∪ X^{n-1}`. The pushout is proved from
the original weak topology, the subcomplex cell condition, and the original
characteristic maps. This includes arbitrary cell families and rank zero.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace Topology.CWComplex

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
variable (A : Subcomplex (Set.univ : Set X))

/-- The actual disjoint family of relative characteristic disks. -/
abbrev relativeCellDisksAt (n : ℕ) :=
  Σ _ : relativeCells X A n, (classicalCellDiskPair.{u} n).fst

/-- The actual disjoint family of relative attaching spheres. -/
abbrev relativeCellSpheresAt (n : ℕ) :=
  Σ _ : relativeCells X A n, (classicalCellDiskPair.{u} n).snd

/-- The original characteristic family lands in the literal successor relative stage. -/
def relativeDiskSumToSkeleton (n : ℕ) :
    TopCat.of (relativeCellDisksAt X A n) ⟶ relativeSkeletonTop X A (n + 1) :=
  TopCat.ofHom
    ⟨fun x => characteristicRelativeDiskToSkeleton X A n x.1 x.2,
      continuous_sigma fun j => (characteristicRelativeDiskToSkeleton X A n j).hom.continuous⟩

/-- The original boundary family lands in the complete preceding relative stage. -/
def relativeSphereSumToSkeleton (n : ℕ) :
    TopCat.of (relativeCellSpheresAt X A n) ⟶ relativeSkeletonTop X A n :=
  TopCat.ofHom
    ⟨fun x => characteristicRelativeSphereToSkeleton X A n x.1 x.2,
      continuous_sigma fun j => (characteristicRelativeSphereToSkeleton X A n j).hom.continuous⟩

/-- The literal disjoint family of relative sphere-to-disk inclusions. -/
def relativeSphereSumToDiskSum (n : ℕ) :
    TopCat.of (relativeCellSpheresAt X A n) ⟶ TopCat.of (relativeCellDisksAt X A n) :=
  TopCat.ofHom
    ⟨fun x => ⟨x.1, (classicalCellDiskPair.{u} n).map x.2⟩,
      continuous_sigma fun j => (continuous_sigmaMk (i := j)).comp
        (classicalCellDiskPair.{u} n).map.hom.continuous⟩

/-- The old relative stage and the new original disks cover the successor. -/
def relativeSkeletonAttachmentQuotient (n : ℕ) :
    TopCat.of (relativeSkeletonTop X A n ⊕ relativeCellDisksAt X A n) ⟶
      relativeSkeletonTop X A (n + 1) :=
  TopCat.ofHom
    ⟨Sum.elim (relativeSkeletonTransition X A n) (relativeDiskSumToSkeleton X A n),
      (relativeSkeletonTransition X A n).hom.continuous.sumElim
        (relativeDiskSumToSkeleton X A n).hom.continuous⟩

/-- Coverage uses precisely the cells outside the given subcomplex. -/
theorem relativeSkeletonAttachmentQuotient_surjective (n : ℕ) :
    Function.Surjective (relativeSkeletonAttachmentQuotient X A n) := by
  intro x
  have hx : x.val ∈ (relativeSkeleton X A n : Set X) ∪
      ⋃ j : relativeCells X A n, closedCell n j.val := by
    rw [relativeSkeleton_union_iUnion_closedCell_eq_succ]
    exact x.property
  rcases hx with hx | hx
  · exact ⟨Sum.inl ⟨x.val, hx⟩, rfl⟩
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨j, y, hy, hyx⟩ := hx
    exact ⟨Sum.inr ⟨j, ULift.up ⟨y, hy⟩⟩, Subtype.ext hyx⟩

/-- The old relative stage retains the intersection of an ambient subset
with its original relative skeletal carrier. -/
theorem relativeSkeleton_image_preimage_transition (n : ℕ)
    (B : Set (relativeSkeletonTop X A (n + 1))) :
    relativeSkeletonInclusion X A n '' ((relativeSkeletonTransition X A n) ⁻¹' B) =
      relativeSkeletonInclusion X A (n + 1) '' B ∩ (relativeSkeleton X A n : Set X) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨relativeSkeletonTransition X A n y, hy, rfl⟩, y.property⟩
  · rintro ⟨⟨y, hy, hxy⟩, hx⟩
    let z : relativeSkeletonTop X A n := ⟨x, hx⟩
    have hz : relativeSkeletonTransition X A n z = y := Subtype.ext hxy.symm
    refine ⟨z, ?_, rfl⟩
    change relativeSkeletonTransition X A n z ∈ B
    rw [hz]
    exact hy

/-- A relative characteristic disk retains the intersection with its
original closed characteristic cell. -/
theorem characteristic_image_preimage_relativeSkeleton (n : ℕ)
    (j : relativeCells X A n) (B : Set (relativeSkeletonTop X A (n + 1))) :
    characteristicDiskMap n j.val '' ((characteristicRelativeDiskToSkeleton X A n j) ⁻¹' B) =
      relativeSkeletonInclusion X A (n + 1) '' B ∩ closedCell n j.val := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨characteristicRelativeDiskToSkeleton X A n j y, hy, rfl⟩,
      y.down.val, y.down.property, rfl⟩
  · rintro ⟨⟨y, hy, hyx⟩, hx⟩
    obtain ⟨z, hz⟩ := (range_characteristicDiskMap n j.val).symm ▸ hx
    have hzy : characteristicRelativeDiskToSkeleton X A n j z = y :=
      Subtype.ext (hz.trans hyx.symm)
    refine ⟨z, ?_, hz⟩
    change characteristicRelativeDiskToSkeleton X A n j z ∈ B
    rw [hzy]
    exact hy

/-- The original weak topology proves the relative attachment quotient.
Cells of `A` are already controlled by the complete old relative stage;
higher cells outside `A` meet the successor only on their finite frontiers. -/
theorem isQuotientMap_relativeSkeletonAttachmentQuotient (n : ℕ) :
    IsQuotientMap (relativeSkeletonAttachmentQuotient X A n) := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨relativeSkeletonAttachmentQuotient_surjective X A n, ?_⟩
  intro B
  constructor
  · intro hB
    exact hB.preimage (relativeSkeletonAttachmentQuotient X A n).hom.continuous
  · intro hB
    let S := relativeSkeletonInclusion X A (n + 1) '' B
    have hS : S ⊆ (relativeSkeleton X A ((n + 1 : ℕ) : ℕ∞) : Set X) := by
      rintro x ⟨y, _, rfl⟩
      exact y.property
    have hold : IsClosed (S ∩ (relativeSkeleton X A n : Set X)) := by
      rw [← relativeSkeleton_image_preimage_transition]
      exact (isClosedEmbedding_relativeSkeletonInclusion X A n).isClosedMap _
        (hB.preimage continuous_inl)
    have hnew (j : relativeCells X A n) : IsClosed (S ∩ closedCell n j.val) := by
      rw [← characteristic_image_preimage_relativeSkeleton]
      have hj : IsClosed ((characteristicRelativeDiskToSkeleton X A n j) ⁻¹' B) :=
        (hB.preimage continuous_inr).preimage continuous_sigmaMk
      exact (hj.isCompact.image (characteristicDiskMap n j.val).hom.continuous).isClosed
    have hcells : ∀ m : ℕ, ∀ j : cell (Set.univ : Set X) m, IsClosed (S ∩ closedCell m j) := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro j
        by_cases hj : j ∈ A.I m
        · have hsub := closedCell_subset_relativeSkeleton_of_mem X A n m j hj
          have heq : S ∩ closedCell m j =
              (S ∩ (relativeSkeleton X A n : Set X)) ∩ closedCell m j := by
            rw [Set.inter_assoc, Set.inter_eq_right.mpr hsub]
          rw [heq]
          exact hold.inter isClosed_closedCell
        · by_cases hmn : m < n
          · have hsub : closedCell m j ⊆ (relativeSkeleton X A n : Set X) :=
              ((closedCell_subset_skeletonLT m j).trans
                (skeletonLT_mono (by exact_mod_cast Nat.succ_le_of_lt hmn))).trans
                  (skeleton_subset_relativeSkeleton X A n)
            have heq : S ∩ closedCell m j =
                (S ∩ (relativeSkeleton X A n : Set X)) ∩ closedCell m j := by
              rw [Set.inter_assoc, Set.inter_eq_right.mpr hsub]
            rw [heq]
            exact hold.inter isClosed_closedCell
          · by_cases hmn' : m = n
            · subst m
              exact hnew ⟨j, hj⟩
            · have hnm : n + 1 ≤ m := by omega
              have hdis : Disjoint S (openCell m j) :=
                (disjoint_relativeSkeleton_openCell X A (⟨j, hj⟩ : relativeCells X A m)
                  (by exact_mod_cast hnm)).mono_left hS
              have heq : S ∩ closedCell m j = S ∩ cellFrontier m j := by
                rw [← cellFrontier_union_openCell_eq_closedCell,
                  Set.inter_union_distrib_left, hdis.inter_eq, Set.union_empty]
              rw [heq]
              cases m with
              | zero => omega
              | succ m =>
                exact isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
                  (fun k hk i => ih k (Nat.lt_succ_of_le hk) i) j
    have hclosedS : IsClosed S := CWComplex.closed' S (Set.subset_univ _) hcells
    have heq : (relativeSkeletonInclusion X A (n + 1)) ⁻¹' S = B :=
      Set.preimage_image_eq B (isClosedEmbedding_relativeSkeletonInclusion X A (n + 1)).injective
    rw [← heq]
    exact hclosedS.preimage (relativeSkeletonInclusion X A (n + 1)).hom.continuous

/-- A relative disk point in the old relative stage lies on its original
attaching sphere, including when it lies in the complete subcomplex. -/
theorem exists_sphere_preimage_of_disk_mem_relativeSkeleton (n : ℕ)
    (j : relativeCells X A n) (d : (classicalCellDiskPair.{u} n).fst)
    (hd : characteristicDiskMap n j.val d ∈ (relativeSkeleton X A n : Set X)) :
    ∃ b : (classicalCellDiskPair.{u} n).snd, (classicalCellDiskPair.{u} n).map b = d := by
  have hnot : d.down.val ∉ Metric.ball (0 : Fin n → ℝ) 1 := by
    intro hball
    exact Set.disjoint_left.mp
      (disjoint_relativeSkeleton_openCell X A j (n := (n : ℕ∞)) le_rfl)
      hd ⟨d.down.val, hball, rfl⟩
  have hs : d.down.val ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    rw [Metric.mem_ball] at hnot
    rw [Metric.mem_sphere]
    exact le_antisymm (Metric.mem_closedBall.mp d.down.property) (le_of_not_gt hnot)
  exact ⟨ULift.up ⟨d.down.val, hs⟩, rfl⟩

section Descent

variable {Y : Type*} [TopologicalSpace Y]

/-- Boundary compatibility equates the value on an old relative point
with the value on any original disk point representing it. -/
theorem relative_compatible_old_disk (n : ℕ) (f : C(relativeSkeletonTop X A n, Y))
    (g : C(relativeCellDisksAt X A n, Y))
    (h : ∀ b : relativeCellSpheresAt X A n,
      f (relativeSphereSumToSkeleton X A n b) = g (relativeSphereSumToDiskSum X A n b))
    (j : relativeCells X A n) (d : (classicalCellDiskPair.{u} n).fst)
    (x : relativeSkeletonTop X A n)
    (hx : relativeSkeletonAttachmentQuotient X A n (Sum.inl x) =
      relativeSkeletonAttachmentQuotient X A n (Sum.inr ⟨j, d⟩)) : f x = g ⟨j, d⟩ := by
  have hxv : x.val = characteristicDiskMap n j.val d := congrArg Subtype.val hx
  have hd : characteristicDiskMap n j.val d ∈ (relativeSkeleton X A n : Set X) := by
    rw [← hxv]
    exact x.property
  obtain ⟨b, hb⟩ := exists_sphere_preimage_of_disk_mem_relativeSkeleton X A n j d hd
  have hbv : b.down.val = d.down.val :=
    congrArg (fun z : (classicalCellDiskPair.{u} n).fst => z.down.val) hb
  have hsource : relativeSphereSumToSkeleton X A n ⟨j, b⟩ = x := by
    apply Subtype.ext
    change map n j.val b.down.val = x.val
    rw [hbv]
    exact hxv.symm
  calc
    f x = f (relativeSphereSumToSkeleton X A n ⟨j, b⟩) := congrArg f hsource.symm
    _ = g (relativeSphereSumToDiskSum X A n ⟨j, b⟩) := h ⟨j, b⟩
    _ = g ⟨j, d⟩ := congrArg (fun z : (classicalCellDiskPair.{u} n).fst => g ⟨j, z⟩) hb

/-- Equal original images give equal compatible relative disk values.
Outside the preceding stage the original disjoint interiors identify both
the original cell and its original disk coordinate. -/
theorem relative_compatible_disk_disk (n : ℕ) (f : C(relativeSkeletonTop X A n, Y))
    (g : C(relativeCellDisksAt X A n, Y))
    (h : ∀ b : relativeCellSpheresAt X A n,
      f (relativeSphereSumToSkeleton X A n b) = g (relativeSphereSumToDiskSum X A n b))
    (j k : relativeCells X A n) (d e : (classicalCellDiskPair.{u} n).fst)
    (hx : relativeSkeletonAttachmentQuotient X A n (Sum.inr ⟨j, d⟩) =
      relativeSkeletonAttachmentQuotient X A n (Sum.inr ⟨k, e⟩)) : g ⟨j, d⟩ = g ⟨k, e⟩ := by
  have hv : characteristicDiskMap n j.val d = characteristicDiskMap n k.val e :=
    congrArg Subtype.val hx
  by_cases hd : characteristicDiskMap n j.val d ∈ (relativeSkeleton X A n : Set X)
  · let x : relativeSkeletonTop X A n := ⟨characteristicDiskMap n j.val d, hd⟩
    have hxj : relativeSkeletonAttachmentQuotient X A n (Sum.inl x) =
        relativeSkeletonAttachmentQuotient X A n (Sum.inr ⟨j, d⟩) := rfl
    have hxk : relativeSkeletonAttachmentQuotient X A n (Sum.inl x) =
        relativeSkeletonAttachmentQuotient X A n (Sum.inr ⟨k, e⟩) := hxj.trans hx
    exact (relative_compatible_old_disk X A n f g h j d x hxj).symm.trans
      (relative_compatible_old_disk X A n f g h k e x hxk)
  · have he : characteristicDiskMap n k.val e ∉ (relativeSkeleton X A n : Set X) :=
      fun he => hd (hv.symm ▸ he)
    have hd' := disk_interior_of_image_not_mem_skeleton n j.val d
      (fun hs => hd (skeleton_subset_relativeSkeleton X A n hs))
    have he' := disk_interior_of_image_not_mem_skeleton n k.val e
      (fun hs => he (skeleton_subset_relativeSkeleton X A n hs))
    have hcells : ¬ Disjoint (openCell (C := (Set.univ : Set X)) n j.val) (openCell n k.val) := by
      intro hdis
      exact Set.disjoint_left.mp hdis ⟨d.down.val, hd', rfl⟩ ⟨e.down.val, he', hv.symm⟩
    have hjkval : j.val = k.val := by simpa using eq_of_not_disjoint_openCell hcells
    have hjk : j = k := Subtype.ext hjkval
    subst k
    have hde : d.down.val = e.down.val := (map n j.val).injOn
      (by rw [source_eq]; exact hd') (by rw [source_eq]; exact he') hv
    have hde' : d = e := ULift.down_injective (Subtype.ext hde)
    rw [hde']

/-- Any compatible relative family is constant on the actual attachment fibres. -/
theorem relative_skeleton_family_factors (n : ℕ) (f : C(relativeSkeletonTop X A n, Y))
    (g : C(relativeCellDisksAt X A n, Y))
    (h : ∀ b : relativeCellSpheresAt X A n,
      f (relativeSphereSumToSkeleton X A n b) = g (relativeSphereSumToDiskSum X A n b)) :
    Function.FactorsThrough (Sum.elim f g) (relativeSkeletonAttachmentQuotient X A n) := by
  intro a b hab
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      have hxy : x = y := Subtype.ext
        (congrArg (fun z : relativeSkeletonTop X A (n + 1) => z.val) hab)
      exact congrArg f hxy
    | inr y => exact relative_compatible_old_disk X A n f g h y.1 y.2 x hab
  | inr x =>
    cases b with
    | inl y => exact (relative_compatible_old_disk X A n f g h x.1 x.2 y hab.symm).symm
    | inr y => exact relative_compatible_disk_disk X A n f g h x.1 y.1 x.2 y.2 hab

/-- Compatible maps descend through the proved relative attachment quotient. -/
def relativeSkeletonGlue (n : ℕ) (f : C(relativeSkeletonTop X A n, Y))
    (g : C(relativeCellDisksAt X A n, Y))
    (h : ∀ b : relativeCellSpheresAt X A n,
      f (relativeSphereSumToSkeleton X A n b) = g (relativeSphereSumToDiskSum X A n b)) :
    C(relativeSkeletonTop X A (n + 1), Y) :=
  (isQuotientMap_relativeSkeletonAttachmentQuotient X A n).lift
    ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩ (relative_skeleton_family_factors X A n f g h)

/-- The descended map retains the complete old relative stage. -/
theorem relativeSkeletonGlue_left (n : ℕ) (f : C(relativeSkeletonTop X A n, Y))
    (g : C(relativeCellDisksAt X A n, Y))
    (h : ∀ b : relativeCellSpheresAt X A n,
      f (relativeSphereSumToSkeleton X A n b) = g (relativeSphereSumToDiskSum X A n b))
    (x : relativeSkeletonTop X A n) :
    relativeSkeletonGlue X A n f g h (relativeSkeletonTransition X A n x) = f x :=
  DFunLike.congr_fun ((isQuotientMap_relativeSkeletonAttachmentQuotient X A n).lift_comp
    ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩
    (relative_skeleton_family_factors X A n f g h)) (Sum.inl x)

/-- The descended map retains every original relative characteristic disk. -/
theorem relativeSkeletonGlue_right (n : ℕ) (f : C(relativeSkeletonTop X A n, Y))
    (g : C(relativeCellDisksAt X A n, Y))
    (h : ∀ b : relativeCellSpheresAt X A n,
      f (relativeSphereSumToSkeleton X A n b) = g (relativeSphereSumToDiskSum X A n b))
    (x : relativeCellDisksAt X A n) :
    relativeSkeletonGlue X A n f g h (relativeDiskSumToSkeleton X A n x) = g x :=
  DFunLike.congr_fun ((isQuotientMap_relativeSkeletonAttachmentQuotient X A n).lift_comp
    ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩
    (relative_skeleton_family_factors X A n f g h)) (Sum.inr x)

end Descent

/-- The literal relative attachment cocone. -/
def relativeSkeletonPushoutCocone (n : ℕ) :
    PushoutCocone (relativeSphereSumToSkeleton X A n) (relativeSphereSumToDiskSum X A n) :=
  PushoutCocone.mk (relativeSkeletonTransition X A n) (relativeDiskSumToSkeleton X A n) rfl

/-- The pointwise boundary condition of a competing relative attachment cocone. -/
theorem relativeSkeletonPushoutCocone_condition (n : ℕ)
    (s : PushoutCocone (relativeSphereSumToSkeleton X A n) (relativeSphereSumToDiskSum X A n))
    (b : relativeCellSpheresAt X A n) :
    s.inl (relativeSphereSumToSkeleton X A n b) =
      s.inr (relativeSphereSumToDiskSum X A n b) := by
  change (relativeSphereSumToSkeleton X A n ≫ s.inl) b =
    (relativeSphereSumToDiskSum X A n ≫ s.inr) b
  rw [s.condition]

/-- The actual relative successor stage has the complete characteristic
pushout universal property. -/
def relativeSkeletonPushoutIsColimit (n : ℕ) :
    IsColimit (relativeSkeletonPushoutCocone X A n) := by
  apply PushoutCocone.isColimitAux'
  intro s
  have h (b : relativeCellSpheresAt X A n) :
      s.inl (relativeSphereSumToSkeleton X A n b) =
        s.inr (relativeSphereSumToDiskSum X A n b) :=
    relativeSkeletonPushoutCocone_condition X A n s b
  let l : relativeSkeletonTop X A (n + 1) ⟶ s.pt :=
    TopCat.ofHom (relativeSkeletonGlue X A n s.inl.hom s.inr.hom h)
  have hl : relativeSkeletonTransition X A n ≫ l = s.inl := by
    apply TopCat.ext
    intro x
    exact relativeSkeletonGlue_left X A n s.inl.hom s.inr.hom h x
  have hr : relativeDiskSumToSkeleton X A n ≫ l = s.inr := by
    apply TopCat.ext
    intro x
    exact relativeSkeletonGlue_right X A n s.inl.hom s.inr.hom h x
  refine ⟨l, hl, hr, ?_⟩
  intro m hmleft hmright
  apply TopCat.ext
  intro x
  obtain ⟨z, rfl⟩ := relativeSkeletonAttachmentQuotient_surjective X A n x
  cases z with
  | inl y =>
    exact (ConcreteCategory.congr_hom hmleft y).trans (ConcreteCategory.congr_hom hl y).symm
  | inr y =>
    exact (ConcreteCategory.congr_hom hmright y).trans (ConcreteCategory.congr_hom hr y).symm

/-- The original relative characteristic square is a pushout. -/
theorem isPushout_relativeSkeletonAttachment (n : ℕ) :
    IsPushout (relativeSphereSumToSkeleton X A n) (relativeSphereSumToDiskSum X A n)
      (relativeSkeletonTransition X A n) (relativeDiskSumToSkeleton X A n) :=
  IsPushout.of_isColimit (relativeSkeletonPushoutIsColimit X A n)

/-- The actual disjoint union of all finite relative skeletal stages. -/
abbrev RelativeSkeletalUnion := Σ n : ℕ, relativeSkeletonTop X A n

/-- The relative dimension union has the original CW space as its target. -/
def relativeSkeletalUnionQuotient : TopCat.of (RelativeSkeletalUnion X A) ⟶ X :=
  TopCat.ofHom
    ⟨fun x => relativeSkeletonInclusion X A x.1 x.2,
      continuous_sigma fun n => (relativeSkeletonInclusion X A n).hom.continuous⟩

/-- The original absolute dimension union includes in the relative one. -/
def skeletalUnionToRelativeUnion :
    TopCat.of (SkeletalUnion X) ⟶ TopCat.of (RelativeSkeletalUnion X A) :=
  TopCat.ofHom
    ⟨fun x => ⟨x.1, ⟨x.2.val, skeleton_subset_relativeSkeleton X A x.1 x.2.property⟩⟩,
      continuous_sigma fun n => by
        let f : C(skeletonTop X n, relativeSkeletonTop X A n) :=
          ⟨Set.inclusion (skeleton_subset_relativeSkeleton X A n),
            continuous_subtype_val.subtype_mk _⟩
        exact continuous_sigmaMk.comp f.continuous⟩

@[simp]
theorem skeletalUnionToRelativeUnion_comp_quotient :
    skeletalUnionToRelativeUnion X A ≫ relativeSkeletalUnionQuotient X A =
      skeletalUnionQuotient X := rfl

/-- The relative dimension union has the original weak quotient topology,
by the already proved original absolute dimension quotient. -/
theorem isQuotientMap_relativeSkeletalUnionQuotient :
    IsQuotientMap (relativeSkeletalUnionQuotient X A) :=
  IsQuotientMap.of_comp (skeletalUnionToRelativeUnion X A).hom.continuous
    (relativeSkeletalUnionQuotient X A).hom.continuous
    (show IsQuotientMap
      ((relativeSkeletalUnionQuotient X A) ∘ (skeletalUnionToRelativeUnion X A)) from
        isQuotientMap_skeletalUnionQuotient X)

end Topology.CWComplex

end
