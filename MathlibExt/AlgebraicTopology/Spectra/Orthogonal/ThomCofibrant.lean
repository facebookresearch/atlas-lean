/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.CoendThom
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ComplementBundleColumnCells
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHCompactificationCofibration
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSmashModel
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantTensorPowers
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SpherePowerComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSpherePowers

/-!
# The actual native Thom pushout and original Hom cofibrancy

The complete inherited functions and topology are retained.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Filter
open TopologicalSpace Topology
open Matrix
open scoped InnerProductSpace
open CategoryTheory.Spectra


namespace CategoryTheory.Spectra.OrthogonalCoendThom

open CategoryTheory.Spectra.OrthogonalComplementBundle

/-- The actual one-point disk family for the full smaller complement bundle. -/
def thomDisk (n k : ℕ) : PointedCGWH.{u, v} :=
  PointedCGWH.onePointOf (LiftedDisk.{v} k × LiftedBundle.{v} n k)

/-- The actual one-point boundary family for the full smaller complement bundle. -/
def thomBoundary (n k : ℕ) : PointedCGWH.{u, v} :=
  PointedCGWH.onePointOf (LiftedBoundary.{v} k × LiftedBundle.{v} n k)

/-- The actual negative-pole inclusion in the original independent ambient universe. -/
def liftedPoleBundle (n k : ℕ) : LiftedBundle.{v} n k → LiftedBundle.{v} (n + 1) (k + 1) :=
  fun p => ULift.up (poleBundle p.down)

/-- The lifted negative-pole insertion is continuous in its original topology. -/
theorem liftedPoleBundle_continuous (n k : ℕ) : Continuous (liftedPoleBundle.{v} n k) :=
  continuous_uliftUp.comp ((poleBundle_continuous n k).comp continuous_uliftDown)

/-- The lifted negative-pole insertion retains the proved properness of the actual finite map. -/
theorem liftedPoleBundle_proper (n k : ℕ) : IsProperMap (liftedPoleBundle.{v} n k) :=
  (Homeomorph.ulift (X := ComplementBundle (n + 1) (k + 1))).symm.isProperMap.comp
    ((poleBundle_proper n k).comp (Homeomorph.ulift (X := ComplementBundle n k)).isProperMap)

/-- The complete lifted disk characteristic function on the original matrix/vector carrier. -/
def liftedDiskBundleAttachment (n k : ℕ) :
    LiftedDisk.{v} k × LiftedBundle.{v} n k → LiftedBundle.{v} (n + 1) (k + 1) :=
  fun p => ULift.up (diskBundleAttachment n k (p.1.down, p.2.down))

/-- The lifted disk characteristic is jointly continuous on its whole original domain. -/
theorem liftedDiskBundleAttachment_continuous (n k : ℕ) :
    Continuous (liftedDiskBundleAttachment.{v} n k) :=
  continuous_uliftUp.comp ((diskBundleAttachment_continuous n k).comp
    ((continuous_uliftDown.comp continuous_fst).prodMk
      (continuous_uliftDown.comp continuous_snd)))

/-- Both lift homeomorphisms retain the actual properness of the full disk characteristic. -/
theorem liftedDiskBundleAttachment_proper (n k : ℕ) :
    IsProperMap (liftedDiskBundleAttachment.{v} n k) :=
  (Homeomorph.ulift (X := ComplementBundle (n + 1) (k + 1))).symm.isProperMap.comp
    ((diskBundleAttachment_proper n k).comp
      ((Homeomorph.ulift (X := ClosedDisk k)).prodCongr
        (Homeomorph.ulift (X := ComplementBundle n k))).isProperMap)

/-- The original smaller reflection is the lifted full boundary attaching function. -/
def liftedBoundaryClutch (n k : ℕ) :
    LiftedBoundary.{v} k × LiftedBundle.{v} n k → LiftedBundle.{v} n k :=
  fun p => ULift.up (boundaryClutch n k (p.1.down, p.2.down))

/-- The full lifted boundary attaching function is jointly continuous. -/
theorem liftedBoundaryClutch_continuous (n k : ℕ) :
    Continuous (liftedBoundaryClutch.{v} n k) :=
  continuous_uliftUp.comp ((boundaryClutch_continuous n k).comp
    ((continuous_uliftDown.comp continuous_fst).prodMk
      (continuous_uliftDown.comp continuous_snd)))

/-- The original proper boundary attaching function remains proper under both actual lifts. -/
theorem liftedBoundaryClutch_proper (n k : ℕ) : IsProperMap (liftedBoundaryClutch.{v} n k) :=
  (Homeomorph.ulift (X := ComplementBundle n k)).symm.isProperMap.comp
    ((boundaryClutch_proper n k).comp
      ((Homeomorph.ulift (X := DiskBoundary k)).prodCongr
        (Homeomorph.ulift (X := ComplementBundle n k))).isProperMap)

/-- The actual sphere-to-disk inclusion in the unchanged lifted characteristic coordinates. -/
def liftedBoundaryInclusion (k : ℕ) : LiftedBoundary.{v} k → LiftedDisk.{v} k :=
  fun x => ULift.up (coefficientSphereToDisk k x.down)

/-- The original finite sphere-to-disk inclusion is continuous in its inherited topology. -/
theorem coefficientSphereToDisk_continuous (k : ℕ) :
    Continuous (coefficientSphereToDisk k) :=
  continuous_subtype_val.subtype_mk _

/-- The actual finite sphere-to-disk inclusion is a genuine closed embedding. -/
theorem coefficientSphereToDisk_closedEmbedding (k : ℕ) :
    IsClosedEmbedding (coefficientSphereToDisk k) := by
  apply (coefficientSphereToDisk_continuous k).isClosedEmbedding
  intro x y h
  exact Subtype.ext (congrArg (fun z : ClosedDisk k => z.val) h)

/-- The original lifted sphere-to-disk inclusion is continuous. -/
theorem liftedBoundaryInclusion_continuous (k : ℕ) :
    Continuous (liftedBoundaryInclusion.{v} k) :=
  continuous_uliftUp.comp
    ((coefficientSphereToDisk_continuous k).comp continuous_uliftDown)

/-- The actual closed boundary inclusion is proper after the original ambient lifts. -/
theorem liftedBoundaryInclusion_proper (k : ℕ) :
    IsProperMap (liftedBoundaryInclusion.{v} k) :=
  (Homeomorph.ulift (X := ClosedDisk k)).symm.isProperMap.comp
    ((coefficientSphereToDisk_closedEmbedding k).isProperMap.comp
      (Homeomorph.ulift (X := DiskBoundary k)).isProperMap)

/-- The full lifted boundary inclusion retains every original smaller bundle point. -/
def liftedBoundaryDiskMap (n k : ℕ) :
    LiftedBoundary.{v} k × LiftedBundle.{v} n k → LiftedDisk.{v} k × LiftedBundle.{v} n k :=
  fun p => (liftedBoundaryInclusion k p.1, p.2)

/-- The full lifted disk-boundary inclusion is jointly continuous. -/
theorem liftedBoundaryDiskMap_continuous (n k : ℕ) :
    Continuous (liftedBoundaryDiskMap.{v} n k) :=
  ((liftedBoundaryInclusion_continuous k).comp continuous_fst).prodMk continuous_snd

/-- The boundary product inclusion is proper on the original full bundle carrier. -/
theorem liftedBoundaryDiskMap_proper (n k : ℕ) :
    IsProperMap (liftedBoundaryDiskMap.{v} n k) :=
  (liftedBoundaryInclusion_proper k).prodMap
    (isProperMap_id : IsProperMap (fun p : LiftedBundle.{v} n k => p))

/-- The original one-point negative-pole inclusion into the larger Thom space. -/
def thomPoleInclusion (n k : ℕ) : thom.{u, v} n k ⟶ thom.{u, v} (n + 1) (k + 1) :=
  PointedCGWH.onePointMapOfProper
    ⟨liftedPoleBundle n k, liftedPoleBundle_continuous n k⟩ (by
      have h := (isProperMap_iff_tendsto_cocompact.mp (liftedPoleBundle_proper.{v} n k)).2
      simpa only [ContinuousMap.coe_mk, coclosedCompact_eq_cocompact] using h)

/-- The actual one-point disk characteristic into the original larger Thom carrier. -/
def thomDiskAttachment (n k : ℕ) : thomDisk.{u, v} n k ⟶ thom.{u, v} (n + 1) (k + 1) :=
  PointedCGWH.onePointMapOfProper
    ⟨liftedDiskBundleAttachment n k, liftedDiskBundleAttachment_continuous n k⟩ (by
      have h := (isProperMap_iff_tendsto_cocompact.mp
        (liftedDiskBundleAttachment_proper.{v} n k)).2
      simpa only [ContinuousMap.coe_mk, coclosedCompact_eq_cocompact] using h)

/-- The actual full one-point clutching function into the original smaller Thom carrier. -/
def thomBoundaryClutch (n k : ℕ) : thomBoundary.{u, v} n k ⟶ thom.{u, v} n k :=
  PointedCGWH.onePointMapOfProper
    ⟨liftedBoundaryClutch n k, liftedBoundaryClutch_continuous n k⟩ (by
      have h := (isProperMap_iff_tendsto_cocompact.mp (liftedBoundaryClutch_proper.{v} n k)).2
      simpa only [ContinuousMap.coe_mk, coclosedCompact_eq_cocompact] using h)

/-- The original one-point disk-boundary inclusion of the full smaller Thom family. -/
def thomBoundaryInclusion (n k : ℕ) : thomBoundary.{u, v} n k ⟶ thomDisk.{u, v} n k :=
  PointedCGWH.onePointMapOfProper
    ⟨liftedBoundaryDiskMap n k, liftedBoundaryDiskMap_continuous n k⟩ (by
      have h := (isProperMap_iff_tendsto_cocompact.mp (liftedBoundaryDiskMap_proper.{v} n k)).2
      simpa only [ContinuousMap.coe_mk, coclosedCompact_eq_cocompact] using h)

/-- The actual negative-pole inclusion fixes the original Thom basepoint. -/
theorem thomPoleInclusion_infty (n k : ℕ) :
    (thomPoleInclusion.{u, v} n k).right OnePoint.infty = OnePoint.infty := rfl

/-- The actual negative-pole inclusion retains its complete finite original
matrix/vector formula. -/
theorem thomPoleInclusion_coe (n k : ℕ) (p : LiftedBundle.{v} n k) :
    (thomPoleInclusion.{u, v} n k).right (p : OnePoint (LiftedBundle.{v} n k)) =
      (liftedPoleBundle n k p : OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) := rfl

/-- The original one-point disk characteristic fixes its actual basepoint. -/
theorem thomDiskAttachment_infty (n k : ℕ) :
    (thomDiskAttachment.{u, v} n k).right OnePoint.infty = OnePoint.infty := rfl

/-- The entire finite disk characteristic survives the original proper-map compactification. -/
theorem thomDiskAttachment_coe (n k : ℕ) (x : LiftedDisk.{v} k) (p : LiftedBundle.{v} n k) :
    (thomDiskAttachment.{u, v} n k).right
        ((x, p) : OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k)) =
      (liftedDiskBundleAttachment n k (x, p) :
        OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) := rfl

/-- The actual full boundary clutching function fixes infinity. -/
theorem thomBoundaryClutch_infty (n k : ℕ) :
    (thomBoundaryClutch.{u, v} n k).right OnePoint.infty = OnePoint.infty := rfl

/-- Every original finite boundary point has the full original reflected bundle value. -/
theorem thomBoundaryClutch_coe (n k : ℕ) (x : LiftedBoundary.{v} k)
    (p : LiftedBundle.{v} n k) :
    (thomBoundaryClutch.{u, v} n k).right
        ((x, p) : OnePoint (LiftedBoundary.{v} k × LiftedBundle.{v} n k)) =
      (liftedBoundaryClutch n k (x, p) : OnePoint (LiftedBundle.{v} n k)) := rfl

/-- The original full disk-boundary inclusion fixes its actual basepoint. -/
theorem thomBoundaryInclusion_infty (n k : ℕ) :
    (thomBoundaryInclusion.{u, v} n k).right OnePoint.infty = OnePoint.infty := rfl

/-- The original full disk-boundary inclusion retains both finite factors exactly. -/
theorem thomBoundaryInclusion_coe (n k : ℕ) (x : LiftedBoundary.{v} k)
    (p : LiftedBundle.{v} n k) :
    (thomBoundaryInclusion.{u, v} n k).right
        ((x, p) : OnePoint (LiftedBoundary.{v} k × LiftedBundle.{v} n k)) =
      (liftedBoundaryDiskMap n k (x, p) :
        OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k)) := rfl

/-- The actual native pointed Thom attachment square satisfies the original full
boundary relation. -/
theorem thomAttachment_square (n k : ℕ) :
    thomBoundaryClutch.{u, v} n k ≫ thomPoleInclusion n k =
      thomBoundaryInclusion n k ≫ thomDiskAttachment n k := by
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro z
  simp only [Under.comp_right, ConcreteCategory.comp_apply]
  induction z using OnePoint.rec with
  | infty => rw [thomBoundaryClutch_infty, thomPoleInclusion_infty,
      thomBoundaryInclusion_infty, thomDiskAttachment_infty]
  | coe p =>
      rcases p with ⟨x, p⟩
      rw [thomBoundaryClutch_coe, thomPoleInclusion_coe,
        thomBoundaryInclusion_coe, thomDiskAttachment_coe]
      change (liftedPoleBundle n k (liftedBoundaryClutch n k (x, p)) :
          OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) =
        (liftedDiskBundleAttachment n k (liftedBoundaryDiskMap n k (x, p)) :
          OnePoint (LiftedBundle.{v} (n + 1) (k + 1)))
      rw [OnePoint.coe_eq_coe]
      apply ULift.ext
      exact (diskBundleAttachment_boundary_square n k x.down p.down).symm

/-- The actual compact lifted characteristic disk has a compactly generated compactification. -/
theorem liftedDiskOnePoint_generated (k : ℕ) :
    UCompactlyGeneratedSpace.{u} (OnePoint (LiftedDisk.{v} k)) := by
  let K := LiftedDisk.{v} k
  let e := PointedCGWH.compactFreePointRawHomeo K
  let _ : UCompactlyGeneratedSpace.{u} K := inferInstance
  let _ : UCompactlyGeneratedSpace.{u} PUnit.{v + 1} := inferInstance
  let _ : UCompactlyGeneratedSpace.{u} (PUnit.{v + 1} ⊕ K) := inferInstance
  exact uCompactlyGeneratedSpace_of_coinduced e.continuous e.isQuotientMap.eq_coinduced

/-- The actual compact lifted characteristic boundary has a generated compactification. -/
theorem liftedBoundaryOnePoint_generated (k : ℕ) :
    UCompactlyGeneratedSpace.{u} (OnePoint (LiftedBoundary.{v} k)) := by
  let K := LiftedBoundary.{v} k
  let e := PointedCGWH.compactFreePointRawHomeo K
  let _ : UCompactlyGeneratedSpace.{u} K := inferInstance
  let _ : UCompactlyGeneratedSpace.{u} PUnit.{v + 1} := inferInstance
  let _ : UCompactlyGeneratedSpace.{u} (PUnit.{v + 1} ⊕ K) := inferInstance
  exact uCompactlyGeneratedSpace_of_coinduced e.continuous e.isQuotientMap.eq_coinduced

/-- The complete disk/bundle product compactification is generated in the actual
ambient universe. -/
theorem liftedDiskBundleOnePoint_generated (n k : ℕ) :
    UCompactlyGeneratedSpace.{u} (OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k)) :=
  PointedCGWH.onePointProduct_generated _ _
    (liftedDiskOnePoint_generated k) (liftedBundleOnePoint_generated n k)

/-- The full sphere-boundary/bundle product compactification has its actual generated topology. -/
theorem liftedBoundaryBundleOnePoint_generated (n k : ℕ) :
    UCompactlyGeneratedSpace.{u}
      (OnePoint (LiftedBoundary.{v} k × LiftedBundle.{v} n k)) :=
  PointedCGWH.onePointProduct_generated _ _
    (liftedBoundaryOnePoint_generated k) (liftedBundleOnePoint_generated n k)

/-- The actual compactified negative-pole and disk families form the quotient source. -/
abbrev ThomAttachmentSource (n k : ℕ) :=
  OnePoint (LiftedBundle.{v} n k) ⊕
    OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k)

/-- The full actual compactified pole-and-disk function into the original larger Thom carrier. -/
def rawThomAttachmentMap (n k : ℕ) :
    ThomAttachmentSource.{v} n k → OnePoint (LiftedBundle.{v} (n + 1) (k + 1)) :=
  Sum.elim (OnePoint.map (liftedPoleBundle n k))
    (OnePoint.map (liftedDiskBundleAttachment n k))

/-- Both original proper arms give a jointly continuous actual compactified quotient map. -/
theorem rawThomAttachmentMap_continuous (n k : ℕ) :
    Continuous (rawThomAttachmentMap.{v} n k) := by
  have hp : Continuous (OnePoint.map (liftedPoleBundle.{v} n k)) :=
    OnePoint.continuous_map (liftedPoleBundle_continuous n k) (by
      have h := (isProperMap_iff_tendsto_cocompact.mp (liftedPoleBundle_proper.{v} n k)).2
      simpa only [coclosedCompact_eq_cocompact] using h)
  have hd : Continuous (OnePoint.map (liftedDiskBundleAttachment.{v} n k)) :=
    OnePoint.continuous_map (liftedDiskBundleAttachment_continuous n k) (by
      have h := (isProperMap_iff_tendsto_cocompact.mp
        (liftedDiskBundleAttachment_proper.{v} n k)).2
      simpa only [coclosedCompact_eq_cocompact] using h)
  exact hp.sumElim hd

/-- The full finite pole-and-disk cover also covers the actual one-point Thom compactification. -/
theorem rawThomAttachmentMap_surjective (n k : ℕ) :
    Function.Surjective (rawThomAttachmentMap.{v} n k) := by
  intro z
  induction z using OnePoint.rec with
  | infty => exact ⟨Sum.inl (OnePoint.infty : OnePoint (LiftedBundle.{v} n k)), rfl⟩
  | coe p =>
      obtain ⟨s, hs⟩ := poleDiskBundleMap_surjective n k p.down
      cases s with
      | inl q =>
          refine ⟨Sum.inl ((ULift.up q : LiftedBundle.{v} n k) :
            OnePoint (LiftedBundle.{v} n k)), ?_⟩
          rw [rawThomAttachmentMap, Sum.elim_inl, OnePoint.map_some, OnePoint.coe_eq_coe]
          exact ULift.ext hs
      | inr q =>
          rcases q with ⟨x, q⟩
          refine ⟨Sum.inr (((ULift.up x, ULift.up q) :
            LiftedDisk.{v} k × LiftedBundle.{v} n k) :
              OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k)), ?_⟩
          rw [rawThomAttachmentMap, Sum.elim_inr, OnePoint.map_some, OnePoint.coe_eq_coe]
          exact ULift.ext hs

/-- The full compactified pole-and-disk cover gives the actual quotient topology
on the Thom space. -/
theorem rawThomAttachmentMap_quotient (n k : ℕ) :
    IsQuotientMap (rawThomAttachmentMap.{v} n k) :=
  IsQuotientMap.of_surjective_continuous
    (rawThomAttachmentMap_surjective n k) (rawThomAttachmentMap_continuous n k)

/-- Infinity in the actual cover has exactly its two original based preimages. -/
theorem rawThomAttachmentMap_eq_infty_iff (n k : ℕ) (z : ThomAttachmentSource.{v} n k) :
    rawThomAttachmentMap n k z = OnePoint.infty ↔
      z = Sum.inl (OnePoint.infty : OnePoint (LiftedBundle.{v} n k)) ∨
        z = Sum.inr (OnePoint.infty :
          OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k)) := by
  cases z with
  | inl z =>
      induction z using OnePoint.rec with
      | infty => simp [rawThomAttachmentMap]
      | coe p => simp [rawThomAttachmentMap]
  | inr z =>
      induction z using OnePoint.rec with
      | infty => simp [rawThomAttachmentMap]
      | coe p => simp [rawThomAttachmentMap]

/-- Every nonbasepoint in the actual compactified cover has one original finite presentation. -/
theorem rawThomAttachmentSource_finite (n k : ℕ) (z : ThomAttachmentSource.{v} n k)
    (hz : rawThomAttachmentMap n k z ≠ OnePoint.infty) :
    (∃ p : LiftedBundle.{v} n k, z = Sum.inl (p : OnePoint (LiftedBundle.{v} n k))) ∨
      (∃ x : LiftedDisk.{v} k, ∃ p : LiftedBundle.{v} n k,
        z = Sum.inr ((x, p) : OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k))) := by
  cases z with
  | inl z =>
      induction z using OnePoint.rec with
      | infty => exact (hz rfl).elim
      | coe p => exact Or.inl ⟨p, rfl⟩
  | inr z =>
      induction z using OnePoint.rec with
      | infty => exact (hz rfl).elim
      | coe p => exact Or.inr ⟨p.1, p.2, rfl⟩

/-- Compatible native maps agree on every actual finite reflected boundary value. -/
theorem thomAttachment_boundary_values (n k : ℕ) {T : PointedCGWH.{u, v}}
    (a : thom.{u, v} n k ⟶ T) (b : thomDisk.{u, v} n k ⟶ T)
    (h : thomBoundaryClutch n k ≫ a = thomBoundaryInclusion n k ≫ b)
    (x : LiftedDisk.{v} k) (hx : ‖x.down.val‖ = 1) (p : LiftedBundle.{v} n k) :
    b.right ((x, p) : OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k)) =
      a.right ((ULift.up (targetMap (reflectionFrame x.down.val) p.down) :
        LiftedBundle.{v} n k) : OnePoint (LiftedBundle.{v} n k)) := by
  let s : LiftedBoundary.{v} k := ULift.up ⟨x.down.val, hx⟩
  have hs : liftedBoundaryInclusion k s = x := ULift.ext (Subtype.ext rfl)
  have hh := congrArg (fun f : thomBoundary.{u, v} n k ⟶ T =>
    f.right ((s, p) : OnePoint (LiftedBoundary.{v} k × LiftedBundle.{v} n k))) h
  simp only [Under.comp_right] at hh
  change a.right ((ULift.up (targetMap (reflectionFrame x.down.val) p.down) :
      LiftedBundle.{v} n k) : OnePoint (LiftedBundle.{v} n k)) =
    b.right ((liftedBoundaryInclusion k s, p) :
      OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k)) at hh
  rw [hs] at hh
  exact hh.symm

/-- Both actual based preimages of infinity have the original native target basepoint value. -/
theorem thomAttachment_values_infty (n k : ℕ) {T : PointedCGWH.{u, v}}
    (a : thom.{u, v} n k ⟶ T) (b : thomDisk.{u, v} n k ⟶ T)
    (z : ThomAttachmentSource.{v} n k) (hz : rawThomAttachmentMap n k z = OnePoint.infty) :
    Sum.elim (fun p : OnePoint (LiftedBundle.{v} n k) => a.right p)
      (fun p : OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k) => b.right p) z =
        T.hom PUnit.unit := by
  rcases (rawThomAttachmentMap_eq_infty_iff n k z).mp hz with rfl | rfl
  · exact PointedCGWH.mapOnePoint_infty a
  · exact PointedCGWH.mapOnePoint_infty b

/-- The actual disk/pole quotient kernel is precisely respected by compatible native arrows. -/
theorem thomAttachment_values_respect_kernel (n k : ℕ) {T : PointedCGWH.{u, v}}
    (a : thom.{u, v} n k ⟶ T) (b : thomDisk.{u, v} n k ⟶ T)
    (h : thomBoundaryClutch n k ≫ a = thomBoundaryInclusion n k ≫ b)
    (z w : ThomAttachmentSource.{v} n k)
    (hzw : rawThomAttachmentMap n k z = rawThomAttachmentMap n k w) :
    Sum.elim (fun p : OnePoint (LiftedBundle.{v} n k) => a.right p)
      (fun p : OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k) => b.right p) z =
    Sum.elim (fun p : OnePoint (LiftedBundle.{v} n k) => a.right p)
      (fun p : OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k) => b.right p) w := by
  by_cases hz : rawThomAttachmentMap n k z = OnePoint.infty
  · have hw : rawThomAttachmentMap n k w = OnePoint.infty := hzw.symm.trans hz
    exact (thomAttachment_values_infty n k a b z hz).trans
      (thomAttachment_values_infty n k a b w hw).symm
  have hw : rawThomAttachmentMap n k w ≠ OnePoint.infty := by
    intro hw
    exact hz (hzw.trans hw)
  rcases rawThomAttachmentSource_finite n k z hz with ⟨p, rfl⟩ | ⟨x, p, rfl⟩
  · rcases rawThomAttachmentSource_finite n k w hw with ⟨q, rfl⟩ | ⟨y, q, rfl⟩
    · change (liftedPoleBundle n k p : OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) =
        (liftedPoleBundle n k q : OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) at hzw
      rw [OnePoint.coe_eq_coe] at hzw
      have hpq : p = q := ULift.ext
        ((poleBundle_injective n k) (congrArg ULift.down hzw))
      rw [hpq]
    · change (liftedPoleBundle n k p : OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) =
        (liftedDiskBundleAttachment n k (y, q) :
          OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) at hzw
      rw [OnePoint.coe_eq_coe] at hzw
      have hr := congrArg ULift.down hzw
      have hk := (diskBundleAttachment_eq_poleBundle_iff n k y.down q.down p.down).mp hr.symm
      have hs : (ULift.up (targetMap (reflectionFrame y.down.val) q.down) :
          LiftedBundle.{v} n k) = p := ULift.ext hk.2
      simpa only [Sum.elim_inl, Sum.elim_inr, hs] using
        (thomAttachment_boundary_values n k a b h y hk.1 q).symm
  · rcases rawThomAttachmentSource_finite n k w hw with ⟨q, rfl⟩ | ⟨y, q, rfl⟩
    · change (liftedDiskBundleAttachment n k (x, p) :
          OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) =
        (liftedPoleBundle n k q : OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) at hzw
      rw [OnePoint.coe_eq_coe] at hzw
      have hr := congrArg ULift.down hzw
      have hk := (diskBundleAttachment_eq_poleBundle_iff n k x.down p.down q.down).mp hr
      have hs : (ULift.up (targetMap (reflectionFrame x.down.val) p.down) :
          LiftedBundle.{v} n k) = q := ULift.ext hk.2
      simpa only [Sum.elim_inl, Sum.elim_inr, hs] using
        thomAttachment_boundary_values n k a b h x hk.1 p
    · change (liftedDiskBundleAttachment n k (x, p) :
          OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) =
        (liftedDiskBundleAttachment n k (y, q) :
          OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) at hzw
      rw [OnePoint.coe_eq_coe] at hzw
      have hr := congrArg ULift.down hzw
      rcases (diskBundleAttachment_eq_iff n k x.down y.down p.down q.down).mp hr with
        ⟨hxy, hpq⟩ | ⟨hx, hy, hpq⟩
      · have hxy' : x = y := ULift.ext hxy
        have hpq' : p = q := ULift.ext hpq
        rw [hxy', hpq']
      · simp only [Sum.elim_inr]
        rw [thomAttachment_boundary_values n k a b h x hx p,
          thomAttachment_boundary_values n k a b h y hy q]
        apply congrArg a.right
        change ((ULift.up (targetMap (reflectionFrame x.down.val) p.down) :
            LiftedBundle.{v} n k) : OnePoint (LiftedBundle.{v} n k)) =
          ((ULift.up (targetMap (reflectionFrame y.down.val) q.down) :
            LiftedBundle.{v} n k) : OnePoint (LiftedBundle.{v} n k))
        rw [OnePoint.coe_eq_coe]
        exact ULift.ext hpq

/-- The genuine kernel setoid of the full original compactified attachment cover. -/
def thomAttachmentKernel (n k : ℕ) : Setoid (ThomAttachmentSource.{v} n k) :=
  Setoid.ker (rawThomAttachmentMap n k)

/-- The actual kernel quotient maps to the original larger Thom compactification. -/
def rawThomAttachmentQuotientMap (n k : ℕ) :
    _root_.Quotient (thomAttachmentKernel.{v} n k) →
      OnePoint (LiftedBundle.{v} (n + 1) (k + 1)) :=
  _root_.Quotient.lift (rawThomAttachmentMap n k) (fun _ _ h => h)

/-- Both continuous inverse functions of the actual full attachment-kernel quotient. -/
def rawThomAttachmentQuotientHomeomorph (n k : ℕ) :
    _root_.Quotient (thomAttachmentKernel.{v} n k) ≃ₜ
      OnePoint (LiftedBundle.{v} (n + 1) (k + 1)) := by
  have hc : Continuous (rawThomAttachmentQuotientMap.{v} n k) :=
    Continuous.quotient_lift (rawThomAttachmentMap_continuous n k) (fun _ _ h => h)
  have hb : Function.Bijective (rawThomAttachmentQuotientMap.{v} n k) := by
    constructor
    · intro p q h
      induction p using _root_.Quotient.inductionOn with
      | _ p =>
          induction q using _root_.Quotient.inductionOn with
          | _ q => exact _root_.Quotient.sound h
    · intro p
      obtain ⟨q, hq⟩ := rawThomAttachmentMap_surjective n k p
      exact ⟨_root_.Quotient.mk (thomAttachmentKernel n k) q, hq⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective
    (rawThomAttachmentQuotientMap n k) hb) hc

/-- Compatible native pole and disk maps descend continuously through the actual full quotient. -/
def rawThomAttachmentDesc (n k : ℕ) {T : PointedCGWH.{u, v}}
    (a : thom.{u, v} n k ⟶ T) (b : thomDisk.{u, v} n k ⟶ T)
    (h : thomBoundaryClutch n k ≫ a = thomBoundaryInclusion n k ≫ b) :
    C(OnePoint (LiftedBundle.{v} (n + 1) (k + 1)), T.right) := by
  let _ : UCompactlyGeneratedSpace.{u} (OnePoint (LiftedBundle.{v} n k)) :=
    liftedBundleOnePoint_generated n k
  let _ : UCompactlyGeneratedSpace.{u}
      (OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k)) :=
    liftedDiskBundleOnePoint_generated n k
  let f : ThomAttachmentSource.{v} n k → T.right :=
    Sum.elim (PointedCGWH.onePointArrowRaw a) (PointedCGWH.onePointArrowRaw b)
  have hf : Continuous f :=
    (PointedCGWH.onePointArrowRaw a).continuous.sumElim
      (PointedCGWH.onePointArrowRaw b).continuous
  have hr : ∀ s t, (thomAttachmentKernel n k).r s t → f s = f t := by
    intro s t hst
    have heq : f = Sum.elim (fun p : OnePoint (LiftedBundle.{v} n k) => a.right p)
        (fun p : OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k) => b.right p) := by
      funext z
      cases z with
      | inl z => exact PointedCGWH.onePointArrowRaw_apply a z
      | inr z => exact PointedCGWH.onePointArrowRaw_apply b z
    rw [heq]
    exact thomAttachment_values_respect_kernel n k a b h s t hst
  let e := rawThomAttachmentQuotientHomeomorph.{v} n k
  exact ⟨fun z => _root_.Quotient.lift f hr (e.symm z),
    (Continuous.quotient_lift hf hr).comp e.symm.continuous⟩

/-- The actual continuous quotient descent has every original pole and disk point value. -/
theorem rawThomAttachmentDesc_generator (n k : ℕ) {T : PointedCGWH.{u, v}}
    (a : thom.{u, v} n k ⟶ T) (b : thomDisk.{u, v} n k ⟶ T)
    (h : thomBoundaryClutch n k ≫ a = thomBoundaryInclusion n k ≫ b)
    (z : ThomAttachmentSource.{v} n k) :
    rawThomAttachmentDesc n k a b h (rawThomAttachmentMap n k z) =
      Sum.elim (fun p : OnePoint (LiftedBundle.{v} n k) => a.right p)
        (fun p : OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k) => b.right p) z := by
  let _ : UCompactlyGeneratedSpace.{u} (OnePoint (LiftedBundle.{v} n k)) :=
    liftedBundleOnePoint_generated n k
  let _ : UCompactlyGeneratedSpace.{u}
      (OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k)) :=
    liftedDiskBundleOnePoint_generated n k
  let e := rawThomAttachmentQuotientHomeomorph.{v} n k
  have he : e (_root_.Quotient.mk (thomAttachmentKernel n k) z) =
      rawThomAttachmentMap n k z := rfl
  have hi : e.symm (rawThomAttachmentMap n k z) =
      _root_.Quotient.mk (thomAttachmentKernel n k) z := by
    rw [← he, Homeomorph.symm_apply_apply]
  change _root_.Quotient.lift
    (Sum.elim (PointedCGWH.onePointArrowRaw a) (PointedCGWH.onePointArrowRaw b)) _
    (e.symm (rawThomAttachmentMap n k z)) = _
  rw [hi]
  cases z with
  | inl z => exact PointedCGWH.onePointArrowRaw_apply a z
  | inr z => exact PointedCGWH.onePointArrowRaw_apply b z

/-- The actual continuous quotient descent fixes the original native target basepoint. -/
theorem rawThomAttachmentDesc_infty (n k : ℕ) {T : PointedCGWH.{u, v}}
    (a : thom.{u, v} n k ⟶ T) (b : thomDisk.{u, v} n k ⟶ T)
    (h : thomBoundaryClutch n k ≫ a = thomBoundaryInclusion n k ≫ b) :
    rawThomAttachmentDesc n k a b h OnePoint.infty = T.hom PUnit.unit :=
  (rawThomAttachmentDesc_generator n k a b h
    (Sum.inl (OnePoint.infty : OnePoint (LiftedBundle.{v} n k)))).trans
      (PointedCGWH.mapOnePoint_infty a)

/-- The actual native pointed descent from the full pole-and-disk attachment quotient. -/
def thomAttachmentDesc (n k : ℕ) {T : PointedCGWH.{u, v}}
    (a : thom.{u, v} n k ⟶ T) (b : thomDisk.{u, v} n k ⟶ T)
    (h : thomBoundaryClutch n k ≫ a = thomBoundaryInclusion n k ≫ b) :
    thom.{u, v} (n + 1) (k + 1) ⟶ T := by
  let _ : UCompactlyGeneratedSpace.{u}
      (OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) :=
    liftedBundleOnePoint_generated (n + 1) (k + 1)
  let c := CompactlyGenerated.coreflectionCounitHomeoData.{u, v}
    (OnePoint (LiftedBundle.{v} (n + 1) (k + 1)))
  let f := rawThomAttachmentDesc n k a b h
  let m : (thom.{u, v} (n + 1) (k + 1)).right ⟶ T.right :=
    ConcreteCategory.ofHom ⟨f ∘ c.1, f.continuous.comp c.1.continuous⟩
  exact Under.homMk m (by
    apply ConcreteCategory.hom_ext
    intro t
    change f (c.1 OnePoint.infty) = T.hom t
    rw [c.2 OnePoint.infty, rawThomAttachmentDesc_infty]
    congr 1)

/-- The native pointed descent retains its entire actual raw quotient function. -/
theorem thomAttachmentDesc_eq_raw (n k : ℕ) {T : PointedCGWH.{u, v}}
    (a : thom.{u, v} n k ⟶ T) (b : thomDisk.{u, v} n k ⟶ T)
    (h : thomBoundaryClutch n k ≫ a = thomBoundaryInclusion n k ≫ b)
    (z : OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) :
    (thomAttachmentDesc n k a b h).right z = rawThomAttachmentDesc n k a b h z := by
  let _ : UCompactlyGeneratedSpace.{u}
      (OnePoint (LiftedBundle.{v} (n + 1) (k + 1))) :=
    liftedBundleOnePoint_generated (n + 1) (k + 1)
  let c := CompactlyGenerated.coreflectionCounitHomeoData.{u, v}
    (OnePoint (LiftedBundle.{v} (n + 1) (k + 1)))
  exact congrArg (rawThomAttachmentDesc n k a b h) (c.2 z)

/-- The actual quotient cover agrees with the original native negative-pole inclusion. -/
theorem rawThomAttachmentMap_inl (n k : ℕ) (z : OnePoint (LiftedBundle.{v} n k)) :
    rawThomAttachmentMap n k (Sum.inl z) = (thomPoleInclusion.{u, v} n k).right z := rfl

/-- The actual quotient cover agrees with the original native full disk attachment. -/
theorem rawThomAttachmentMap_inr (n k : ℕ)
    (z : OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k)) :
    rawThomAttachmentMap n k (Sum.inr z) = (thomDiskAttachment.{u, v} n k).right z := rfl

/-- The actual native descent factors every original negative-pole point and infinity. -/
theorem thomAttachmentDesc_fac_pole (n k : ℕ) {T : PointedCGWH.{u, v}}
    (a : thom.{u, v} n k ⟶ T) (b : thomDisk.{u, v} n k ⟶ T)
    (h : thomBoundaryClutch n k ≫ a = thomBoundaryInclusion n k ≫ b) :
    thomPoleInclusion n k ≫ thomAttachmentDesc n k a b h = a := by
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro z
  simp only [Under.comp_right, ConcreteCategory.comp_apply]
  let z0 : OnePoint (LiftedBundle.{v} n k) := z
  change (thomAttachmentDesc n k a b h).right
    ((thomPoleInclusion.{u, v} n k).right z0) = a.right z0
  have hf := thomAttachmentDesc_eq_raw n k a b h
    ((thomPoleInclusion.{u, v} n k).right z0)
  have hg := rawThomAttachmentDesc_generator n k a b h (Sum.inl z0)
  rw [rawThomAttachmentMap_inl.{u, v}, Sum.elim_inl] at hg
  exact hf.trans hg

/-- The actual native descent factors every original disk point and infinity. -/
theorem thomAttachmentDesc_fac_disk (n k : ℕ) {T : PointedCGWH.{u, v}}
    (a : thom.{u, v} n k ⟶ T) (b : thomDisk.{u, v} n k ⟶ T)
    (h : thomBoundaryClutch n k ≫ a = thomBoundaryInclusion n k ≫ b) :
    thomDiskAttachment n k ≫ thomAttachmentDesc n k a b h = b := by
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro z
  simp only [Under.comp_right, ConcreteCategory.comp_apply]
  let z0 : OnePoint (LiftedDisk.{v} k × LiftedBundle.{v} n k) := z
  change (thomAttachmentDesc n k a b h).right
    ((thomDiskAttachment.{u, v} n k).right z0) = b.right z0
  have hf := thomAttachmentDesc_eq_raw n k a b h
    ((thomDiskAttachment.{u, v} n k).right z0)
  have hg := rawThomAttachmentDesc_generator n k a b h (Sum.inr z0)
  rw [rawThomAttachmentMap_inr.{u, v}, Sum.elim_inr] at hg
  exact hf.trans hg

/-- The full actual pole and disk families jointly determine every native larger-Thom map. -/
theorem thomAttachment_hom_ext (n k : ℕ) {T : PointedCGWH.{u, v}}
    {f g : thom.{u, v} (n + 1) (k + 1) ⟶ T}
    (hp : thomPoleInclusion n k ≫ f = thomPoleInclusion n k ≫ g)
    (hd : thomDiskAttachment n k ≫ f = thomDiskAttachment n k ≫ g) : f = g := by
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro z
  obtain ⟨s, hs⟩ := rawThomAttachmentMap_surjective n k z
  rw [← hs]
  cases s with
  | inl s =>
      rw [rawThomAttachmentMap_inl.{u, v}]
      exact congrArg (fun m : thom.{u, v} n k ⟶ T => m.right s) hp
  | inr s =>
      rw [rawThomAttachmentMap_inr.{u, v}]
      exact congrArg (fun m : thomDisk.{u, v} n k ⟶ T => m.right s) hd

/-- The full actual pole/disk square is a colimit cocone in the original native pointed category. -/
def thomAttachmentIsColimit (n k : ℕ) :
    IsColimit (PushoutCocone.mk (thomPoleInclusion.{u, v} n k)
      (thomDiskAttachment n k) (thomAttachment_square n k)) :=
  PushoutCocone.IsColimit.mk (thomAttachment_square n k)
    (fun s => thomAttachmentDesc n k s.inl s.inr s.condition)
    (fun s => thomAttachmentDesc_fac_pole n k s.inl s.inr s.condition)
    (fun s => thomAttachmentDesc_fac_disk n k s.inl s.inr s.condition)
    (fun s m hp hd => thomAttachment_hom_ext n k (f := m)
      (hp.trans (thomAttachmentDesc_fac_pole n k s.inl s.inr s.condition).symm)
      (hd.trans (thomAttachmentDesc_fac_disk n k s.inl s.inr s.condition).symm))

/-- The full actual disk and pole arms form a pushout in the original native pointed category. -/
theorem thomAttachment_isPushout (n k : ℕ) :
    IsPushout (thomBoundaryClutch.{u, v} n k) (thomBoundaryInclusion n k)
      (thomPoleInclusion n k) (thomDiskAttachment n k) :=
  IsPushout.of_isColimit (thomAttachmentIsColimit n k)

/-- The zero-column Thom object is the original orthogonal representation sphere. -/
def thomZeroSphereIso (k : ℕ) :
    thom.{u, v} 0 k ≅ PointedCGWH.orthogonalSphere.{u, v} k :=
  PointedCGWH.onePointHomeomorphOfHomeomorph (liftedZeroColumnBundleHomeomorph k)

open scoped InnerProductSpace

/-- The actual disk family identifies with the native disk compactification
smash the original Thom. -/
def thomDiskTensorIso (n k : ℕ) :
    thomDisk.{u, v} n k ≅ PointedCGWH.onePointOf.{u, v} (LiftedDisk.{v} k) ⊗ thom.{u, v} n k :=
  PointedCGWH.onePointProdSmashIso _ _
    (liftedDiskOnePoint_generated k) (liftedBundleOnePoint_generated n k)

/-- The actual boundary family identifies with the native sphere compactification smash Thom. -/
def thomBoundaryTensorIso (n k : ℕ) :
    thomBoundary.{u, v} n k ≅
      PointedCGWH.onePointOf.{u, v} (LiftedBoundary.{v} k) ⊗ thom.{u, v} n k :=
  PointedCGWH.onePointProdSmashIso _ _
    (liftedBoundaryOnePoint_generated k) (liftedBundleOnePoint_generated n k)

/-- The original one-point compactification of the actual sphere-to-disk cell inclusion. -/
def onePointBoundaryInclusion (k : ℕ) :
    PointedCGWH.onePointOf.{u, v} (LiftedBoundary.{v} k) ⟶
      PointedCGWH.onePointOf.{u, v} (LiftedDisk.{v} k) :=
  PointedCGWH.onePointMapOfProper
    ⟨liftedBoundaryInclusion k, liftedBoundaryInclusion_continuous k⟩ (by
      have h := (isProperMap_iff_tendsto_cocompact.mp (liftedBoundaryInclusion_proper.{v} k)).2
      simpa only [ContinuousMap.coe_mk, coclosedCompact_eq_cocompact] using h)

/-- The actual full boundary product inclusion is exactly the native boundary smash Thom map. -/
theorem thomBoundaryInclusion_tensor_square (n k : ℕ) :
    thomBoundaryInclusion.{u, v} n k ≫ (thomDiskTensorIso n k).hom =
      (thomBoundaryTensorIso n k).hom ≫
        (onePointBoundaryInclusion k ⊗ₘ 𝟙 (thom.{u, v} n k)) := by
  let X := LiftedBoundary.{v} k
  let X' := LiftedDisk.{v} k
  let Y := LiftedBundle.{v} n k
  let f : C(X, X') := ⟨liftedBoundaryInclusion k, liftedBoundaryInclusion_continuous k⟩
  let g : C(Y, Y) := ContinuousMap.id Y
  have hf : Tendsto f (coclosedCompact X) (coclosedCompact X') := by
    have h := (isProperMap_iff_tendsto_cocompact.mp (liftedBoundaryInclusion_proper.{v} k)).2
    simpa only [f, ContinuousMap.coe_mk, coclosedCompact_eq_cocompact] using h
  have hg : Tendsto g (coclosedCompact Y) (coclosedCompact Y) := tendsto_id
  have hfg : Tendsto (f.prodMap g) (coclosedCompact (X × Y))
      (coclosedCompact (X' × Y)) := by
    change Tendsto (liftedBoundaryDiskMap.{v} n k)
      (coclosedCompact (X × Y)) (coclosedCompact (X' × Y))
    have h := (isProperMap_iff_tendsto_cocompact.mp (liftedBoundaryDiskMap_proper.{v} n k)).2
    simpa only [coclosedCompact_eq_cocompact] using h
  have hp : PointedCGWH.onePointMapOfProper.{u, v} (f.prodMap g) hfg =
      thomBoundaryInclusion n k := by
    apply Under.UnderMorphism.ext
    apply ConcreteCategory.hom_ext
    intro z
    induction z using OnePoint.rec with
    | infty => rfl
    | coe z => rfl
  have hfp : PointedCGWH.onePointMapOfProper.{u, v} f hf = onePointBoundaryInclusion k := rfl
  have hgp : PointedCGWH.onePointMapOfProper.{u, v} g hg = 𝟙 (thom.{u, v} n k) := by
    apply Under.UnderMorphism.ext
    apply ConcreteCategory.hom_ext
    intro z
    induction z using OnePoint.rec with
    | infty => rfl
    | coe z => rfl
  have hn := PointedCGWH.onePointProdSmashIso_naturality.{u, v} f g hf hg hfg
    (liftedBoundaryOnePoint_generated k) (liftedDiskOnePoint_generated k)
    (liftedBundleOnePoint_generated n k) (liftedBundleOnePoint_generated n k)
  rw [hp, hfp, hgp] at hn
  exact hn

/-- The actual native boundary-smash comparison identifies the complete two original cell arrows. -/
def thomBoundaryInclusionTensorArrowIso (n k : ℕ) :
    Arrow.mk (thomBoundaryInclusion.{u, v} n k) ≅
      Arrow.mk (onePointBoundaryInclusion k ⊗ₘ 𝟙 (thom.{u, v} n k)) :=
  Arrow.isoMk (thomBoundaryTensorIso n k) (thomDiskTensorIso n k)
    (thomBoundaryInclusion_tensor_square n k).symm

open HomotopicalAlgebra
open scoped CGWH.modelCategory

/-- The actual primitive disk-boundary cofibration gives the full native
boundary-smash cofibration. -/
theorem thomBoundaryInclusion_cofibration_of_cell (n k : ℕ)
    [IsCofibrant (thom.{u, v} n k)]
    (hi : cofibrations PointedCGWH.{u, v} (onePointBoundaryInclusion.{u, v} k)) :
    cofibrations PointedCGWH.{u, v} (thomBoundaryInclusion.{u, v} n k) := by
  let F := thom.{u, v} n k
  let A := PointedCGWH.onePointOf.{u, v} (LiftedBoundary.{v} k)
  let B := PointedCGWH.onePointOf.{u, v} (LiftedDisk.{v} k)
  let i : A ⟶ B := onePointBoundaryInclusion k
  have hl : cofibrations PointedCGWH.{u, v} (𝟙 F ⊗ₘ i) := by
    rw [MonoidalCategory.id_tensorHom]
    exact IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_cofibrations F i hi
  let e : Arrow.mk (𝟙 F ⊗ₘ i) ≅ Arrow.mk (i ⊗ₘ 𝟙 F) :=
    Arrow.isoMk (β_ F A) (β_ F B)
      (CategoryTheory.BraidedCategory.braiding_naturality (𝟙 F) i).symm
  have hr : cofibrations PointedCGWH.{u, v} (i ⊗ₘ 𝟙 F) :=
    ((cofibrations PointedCGWH.{u, v}).arrow_mk_iso_iff e).mp hl
  exact ((cofibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (thomBoundaryInclusionTensorArrowIso n k)).mpr hr

/-- The proved native pushout carries the actual primitive cell cofibration to
the pole inclusion. -/
theorem thomPoleInclusion_cofibration_of_cell (n k : ℕ)
    [IsCofibrant (thom.{u, v} n k)]
    (hi : cofibrations PointedCGWH.{u, v} (onePointBoundaryInclusion.{u, v} k)) :
    cofibrations PointedCGWH.{u, v} (thomPoleInclusion.{u, v} n k) :=
  MorphismProperty.of_isPushout (thomAttachment_isPushout n k)
    (thomBoundaryInclusion_cofibration_of_cell n k hi)

/-- The actual column attachment proves successor Thom cofibrancy from the smaller Thom and cell. -/
theorem thomSuccessor_isCofibrant_of_cell (n k : ℕ)
    [IsCofibrant (thom.{u, v} n k)]
    (hi : cofibrations PointedCGWH.{u, v} (onePointBoundaryInclusion.{u, v} k)) :
    IsCofibrant (thom.{u, v} (n + 1) (k + 1)) := by
  let _ : Cofibration (thomPoleInclusion.{u, v} n k) :=
    (cofibration_iff _).mpr (thomPoleInclusion_cofibration_of_cell n k hi)
  exact isCofibrant_of_cofibration (thomPoleInclusion.{u, v} n k)

/-- The actual below-source Thom object is cofibrant because its proved topology is initial. -/
theorem thomBelow_isCofibrant (n k : ℕ) (h : k < n) : IsCofibrant (thom.{u, v} n k) := by
  rw [isCofibrant_iff_of_isInitial (𝟙 (thom.{u, v} n k)) (thomInitialBelow n k h)]
  infer_instance

/-- The actual inherited lifted characteristic disk, as the native unbased CGWH object. -/
def diskCGWH (k : ℕ) : CGWH.{u, v} := CGWH.of (LiftedDisk.{v} k)

/-- The actual inherited lifted characteristic boundary, as the native unbased CGWH object. -/
def boundaryCGWH (k : ℕ) : CGWH.{u, v} := CGWH.of (LiftedBoundary.{v} k)

instance diskCGWH_compactSpace (k : ℕ) : CompactSpace (diskCGWH.{u, v} k) :=
  inferInstanceAs (CompactSpace (LiftedDisk.{v} k))

instance boundaryCGWH_compactSpace (k : ℕ) : CompactSpace (boundaryCGWH.{u, v} k) :=
  inferInstanceAs (CompactSpace (LiftedBoundary.{v} k))

instance diskCGWH_t2Space (k : ℕ) : T2Space (diskCGWH.{u, v} k) :=
  inferInstanceAs (T2Space (LiftedDisk.{v} k))

instance boundaryCGWH_t2Space (k : ℕ) : T2Space (boundaryCGWH.{u, v} k) :=
  inferInstanceAs (T2Space (LiftedBoundary.{v} k))

/-- The actual original sphere-to-disk inclusion as an unbased native continuous map. -/
def boundaryCGWHInclusion (k : ℕ) : boundaryCGWH.{u, v} k ⟶ diskCGWH.{u, v} k :=
  ConcreteCategory.ofHom ⟨liftedBoundaryInclusion k, liftedBoundaryInclusion_continuous k⟩

/-- The categorical disk carrier retains its actual Euclidean closed-ball topology. -/
def topDiskLiftedHomeomorph (k : ℕ) : TopCat.disk.{v} k ≃ₜ LiftedDisk.{v} k := by
  have heq : Metric.closedBall (0 : Euclidean k) 1 = {x : Euclidean k | ‖x‖ ≤ 1} := by
    ext x
    simp
  exact Homeomorph.ulift.trans
    ((Homeomorph.setCongr heq).trans Homeomorph.ulift.symm)

/-- The categorical disk boundary retains its actual Euclidean unit-sphere topology. -/
def topBoundaryLiftedHomeomorph (k : ℕ) : TopCat.diskBoundary.{v} k ≃ₜ LiftedBoundary.{v} k := by
  have heq : Metric.sphere (0 : Euclidean k) 1 = {x : Euclidean k | ‖x‖ = 1} := by
    ext x
    simp
  exact Homeomorph.ulift.trans
    ((Homeomorph.setCongr heq).trans Homeomorph.ulift.symm)

/-- The actual native boundary map is the canonical categorical disk-boundary cell arrow. -/
def topBoundaryNativeArrowIso (k : ℕ) :
    Arrow.mk (TopCat.diskBoundaryInclusion.{v} k) ≅
      Arrow.mk (CGWH.cgwhToTop.{u, v}.map (boundaryCGWHInclusion.{u, v} k)) :=
  Arrow.isoMk (TopCat.isoOfHomeo (topBoundaryLiftedHomeomorph k))
    (TopCat.isoOfHomeo (topDiskLiftedHomeomorph k)) (by
      apply TopCat.ext
      intro x
      rfl)

/-- The canonical realized-simplex cell proves cofibrancy of the actual
native boundary inclusion. -/
theorem boundaryCGWHInclusion_cofibration (k : ℕ) :
    Cofibration (boundaryCGWHInclusion.{u, v} k) := by
  rw [cofibration_iff]
  change CGWH.modelCofibrations.{u, v} (boundaryCGWHInclusion.{u, v} k)
  rw [CGWH.modelCofibrations_eq_inverseImage]
  have hs : TopCat.realizedBoundaryInclusions.{v}.rlp.llp
      (SSet.toTop.map (SSet.boundary.{v} k).ι) :=
    TopCat.realizedBoundaryInclusions.le_llp_rlp _
      (TopCat.boundary_mem_realizedBoundaryInclusions k)
  let e := SSet.boundary.toTopDiskArrowIso.{v} k ≪≫ topBoundaryNativeArrowIso.{u, v} k
  exact (TopCat.realizedBoundaryInclusions.{v}.rlp.llp.arrow_mk_iso_iff e).mp hs

/-- The actual based sphere-to-disk inclusion is a cofibration by the canonical cell source. -/
theorem onePointBoundaryInclusion_cofibration (k : ℕ) :
    Cofibration (onePointBoundaryInclusion.{u, v} k) := by
  let _ : Cofibration (boundaryCGWHInclusion.{u, v} k) := boundaryCGWHInclusion_cofibration k
  have hf : Tendsto (boundaryCGWHInclusion.{u, v} k)
      (coclosedCompact (boundaryCGWH.{u, v} k))
      (coclosedCompact (diskCGWH.{u, v} k)) := by
    change Tendsto (liftedBoundaryInclusion.{v} k)
      (coclosedCompact (LiftedBoundary.{v} k)) (coclosedCompact (LiftedDisk.{v} k))
    have h := (isProperMap_iff_tendsto_cocompact.mp (liftedBoundaryInclusion_proper.{v} k)).2
    simpa only [coclosedCompact_eq_cocompact] using h
  exact PointedCGWH.onePointMapOfProper_compact_cofibration (boundaryCGWHInclusion k) hf

/-- The actual original orthogonal representation spheres are cofibrant
via their original powers. -/
theorem originalOrthogonalSphere_isCofibrant (k : ℕ) :
    IsCofibrant (PointedCGWH.orthogonalSphere.{u, v} k) := by
  let _ : IsCofibrant (CategoryTheory.MonoidalCategory.TensorPower.tensorPowObj
      PointedCGWH.sphereOne.{u, v} k) :=
    PointedCGWH.modelCategory.tensorPowObj_sphereOne_isCofibrant k
  exact isCofibrant_of_cofibration
    (CategoryTheory.Spectra.originalSpherePowerComparisonIso k).hom

/-- The actual zero-column Thom sphere is cofibrant through the original
representation-sphere iso. -/
theorem thomZero_isCofibrant (k : ℕ) : IsCofibrant (thom.{u, v} 0 k) := by
  let _ : IsCofibrant (PointedCGWH.orthogonalSphere.{u, v} k) :=
    originalOrthogonalSphere_isCofibrant k
  exact isCofibrant_of_cofibration (thomZeroSphereIso.{u, v} k).inv

/-- Every actual complement-bundle Thom basepoint is a cofibration by
genuine native column cells. -/
theorem thom_isCofibrant (n k : ℕ) : IsCofibrant (thom.{u, v} n k) := by
  induction n generalizing k with
  | zero => exact thomZero_isCofibrant k
  | succ n ih =>
      cases k with
      | zero => exact thomBelow_isCofibrant (n + 1) 0 (by omega)
      | succ k =>
          let _ : IsCofibrant (thom.{u, v} n k) := ih k
          exact thomSuccessor_isCofibrant_of_cell n k
            ((cofibration_iff _).mp (onePointBoundaryInclusion_cofibration k))

/-- The original full weighted-coend Hom is cofibrant through its proved
actual Thom homeomorphism. -/
theorem nativeHom_isCofibrant (n k : ℕ) :
    IsCofibrant (OrthogonalOperatorIndex.hom.{u, v} n k) := by
  let _ : IsCofibrant (thom.{u, v} n k) := thom_isCofibrant n k
  exact isCofibrant_of_cofibration (nativeCoendThomIso.{u, v} n k).inv

end CategoryTheory.Spectra.OrthogonalCoendThom
