/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellCollarCover
public import MathlibExt.Topology.Category.TopPair.ClosedBall.Annulus

/-!
# Radial coordinates of the original indexed cell annuli

The actual annulus in the literal disk coproduct is homeomorphic to the
original boundary coproduct times the open radius interval. Each point
keeps its original index, and the component coordinates are those of the
existing closed-ball annulus homeomorphism. The inverse scales the same
original boundary vector by its radius.

Continuity and openness are assembled on the original summands. The
construction needs no topology or nonemptiness assumption on the index
type, and applies to every positive-dimensional classical cell family.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Topology Topology.CWComplex

universe u

namespace AlgebraicTopology.CellAnnulusCoordinates

variable {ι : Type u}

/-- The original annular disk point, with only its family index forgotten. -/
def component (ι : Type u) (n : ℕ) :
    C(CellCollarCover.annulus ι n,
      TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) where
  toFun z := ⟨z.1.2, by exact z.2⟩
  continuous_toFun := by
    have h : Continuous (fun z : CellFamilyAttachment.disks ι n => z.2) := by
      change Continuous (fun z : (Σ _ : ι, (classicalCellDiskPair.{u} (n + 1)).fst) => z.2)
      apply continuous_sigma
      intro i
      exact continuous_id
    exact (h.comp continuous_subtype_val).subtype_mk (fun z => by exact z.2)

/-- Forgetting the family index retains the same original lifted disk point. -/
theorem component_val (n : ℕ) (z : CellCollarCover.annulus ι n) :
    (component ι n z).1 = z.1.2 :=
  rfl

/-- An original component annulus included in its original indexed disk summand. -/
def componentInclusion (n : ℕ) (i : ι) :
    C(TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ),
      CellCollarCover.annulus ι n) where
  toFun z := ⟨⟨i, z.1⟩, by exact z.2⟩
  continuous_toFun := by
    have h : Continuous (fun z : TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ) =>
        (⟨i, z.1⟩ : CellFamilyAttachment.disks ι n)) :=
      (continuous_sigmaMk
        (σ := fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst) (i := i)).comp
          continuous_subtype_val
    exact h.subtype_mk (fun z => by exact z.2)

/-- The component inclusion retains its original index and lifted disk point. -/
theorem componentInclusion_val (n : ℕ) (i : ι)
    (z : TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) :
    (componentInclusion n i z).1 = (⟨i, z.1⟩ : CellFamilyAttachment.disks ι n) :=
  rfl

/-- Forgetting the index of an included component recovers the original annular point. -/
theorem component_componentInclusion (n : ℕ) (i : ι)
    (z : TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) :
    component ι n (componentInclusion n i z) = z :=
  rfl

/-- Including an annular point back into its own original summand recovers it. -/
theorem componentInclusion_component (n : ℕ) (z : CellCollarCover.annulus ι n) :
    componentInclusion n z.1.1 (component ι n z) = z :=
  rfl

/-- Each original component annulus is open in the literal family annulus. -/
theorem componentInclusion_isOpenMap (n : ℕ) (i : ι) :
    IsOpenMap (componentInclusion n i) := by
  have hι : Continuous (fun z : (classicalCellDiskPair.{u} (n + 1)).fst =>
      (⟨i, z⟩ : CellFamilyAttachment.disks ι n)) :=
    continuous_sigmaMk
      (σ := fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst) (i := i)
  have hAnnulus : IsOpen (TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) :=
    (CellCollarCover.annulus_isOpen ι n).preimage hι
  have hSigma : IsOpenMap (fun z : (classicalCellDiskPair.{u} (n + 1)).fst =>
      (⟨i, z⟩ : CellFamilyAttachment.disks ι n)) :=
    isOpenMap_sigmaMk
      (σ := fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst) (i := i)
  have h : IsOpenMap (fun z : TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ) =>
      (⟨i, z.1⟩ : CellFamilyAttachment.disks ι n)) :=
    hSigma.comp hAnnulus.isOpenMap_subtype_val
  exact h.codRestrict (s := CellCollarCover.annulus ι n) (fun z => by exact z.2)

/-- The inverse radial coordinates assembled on the original boundary summands. -/
def inverseSigma (ι : Type u) (n : ℕ) :
    C((Σ _ : ι, (classicalCellDiskPair.{u} (n + 1)).snd × TopPair.cellAnnulusRadii),
      CellCollarCover.annulus ι n) where
  toFun p := componentInclusion n p.1
    ((TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin (n + 1) → ℝ)).symm p.2)
  continuous_toFun := by
    apply continuous_sigma
    intro i
    exact (componentInclusion n i).continuous.comp
      (TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin (n + 1) → ℝ)).symm.continuous

/-- The component inverse coordinates are open on every original summand. -/
theorem inverseSigma_isOpenMap (ι : Type u) (n : ℕ) :
    IsOpenMap (inverseSigma ι n) := by
  apply isOpenMap_sigma.mpr
  intro i
  exact (componentInclusion_isOpenMap n i).comp
    (TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin (n + 1) → ℝ)).symm.isOpenMap

/-- The actual inverse coordinates, from original boundary points and their radii. -/
def inverse (ι : Type u) (n : ℕ) :
    C(CellFamilyAttachment.boundaries ι n × TopPair.cellAnnulusRadii,
      CellCollarCover.annulus ι n) where
  toFun p := inverseSigma ι n
    (Homeomorph.sigmaProdDistrib
      (X := fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd)
      (Y := TopPair.cellAnnulusRadii) p)
  continuous_toFun := by
    exact (inverseSigma ι n).continuous.comp
      (Homeomorph.sigmaProdDistrib
        (X := fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd)
        (Y := TopPair.cellAnnulusRadii)).continuous

/-- The actual inverse coordinates are open in the original family annulus. -/
theorem inverse_isOpenMap (ι : Type u) (n : ℕ) : IsOpenMap (inverse ι n) :=
  (inverseSigma_isOpenMap ι n).comp
    (Homeomorph.sigmaProdDistrib
      (X := fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd)
      (Y := TopPair.cellAnnulusRadii)).isOpenMap

/-- The literal coordinate equivalence preserves the index and uses the existing
component annulus coordinates. -/
def coordinatesEquiv (ι : Type u) (n : ℕ) :
    CellCollarCover.annulus ι n ≃
      CellFamilyAttachment.boundaries ι n × TopPair.cellAnnulusRadii where
  toFun z :=
    let p := TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin (n + 1) → ℝ) (component ι n z)
    (⟨z.1.1, p.1⟩, p.2)
  invFun := inverse ι n
  left_inv z := by
    rcases z with ⟨⟨i, d⟩, hd⟩
    let H := TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin (n + 1) → ℝ)
    apply Subtype.ext
    change (⟨i, (H.symm (H ⟨d, hd⟩)).1⟩ : CellFamilyAttachment.disks ι n) = ⟨i, d⟩
    exact congrArg
      (fun z : TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ) =>
        (⟨i, z.1⟩ : CellFamilyAttachment.disks ι n))
      (H.symm_apply_apply ⟨d, hd⟩)
  right_inv p := by
    rcases p with ⟨⟨i, b⟩, r⟩
    let H := TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin (n + 1) → ℝ)
    change ((⟨i, (H (H.symm (b, r))).1⟩ : CellFamilyAttachment.boundaries ι n),
      (H (H.symm (b, r))).2) = (⟨i, b⟩, r)
    exact congrArg
      (fun q : (classicalCellDiskPair.{u} (n + 1)).snd × TopPair.cellAnnulusRadii =>
        ((⟨i, q.1⟩ : CellFamilyAttachment.boundaries ι n), q.2))
      (H.apply_symm_apply (b, r))

/-- The actual family annulus is homeomorphic to the original boundary sigma
times the actual open radius interval. -/
def homeomorph (ι : Type u) (n : ℕ) :
    CellCollarCover.annulus ι n ≃ₜ
      CellFamilyAttachment.boundaries ι n × TopPair.cellAnnulusRadii :=
  ((coordinatesEquiv ι n).symm.toHomeomorphOfContinuousOpen
    (inverse ι n).continuous (inverse_isOpenMap ι n)).symm

/-- The direction map takes values in the same original indexed boundary sigma. -/
def direction (ι : Type u) (n : ℕ) :
    C(CellCollarCover.annulus ι n, CellFamilyAttachment.boundaries ι n) where
  toFun z := (homeomorph ι n z).1
  continuous_toFun := continuous_fst.comp (homeomorph ι n).continuous

/-- The radius map takes values in the actual strict annulus radius interval. -/
def radius (ι : Type u) (n : ℕ) :
    C(CellCollarCover.annulus ι n, TopPair.cellAnnulusRadii) where
  toFun z := (homeomorph ι n z).2
  continuous_toFun := continuous_snd.comp (homeomorph ι n).continuous

/-- The homeomorphism consists of the public original direction and radius maps. -/
theorem homeomorph_apply (n : ℕ) (z : CellCollarCover.annulus ι n) :
    homeomorph ι n z = (direction ι n z, radius ι n z) :=
  rfl

/-- The inverse homeomorphism is the public original inverse coordinate map. -/
theorem homeomorph_symm_apply (n : ℕ)
    (p : CellFamilyAttachment.boundaries ι n × TopPair.cellAnnulusRadii) :
    (homeomorph ι n).symm p = inverse ι n p :=
  rfl

/-- The direction coordinate retains the exact original family index. -/
theorem direction_index (n : ℕ) (z : CellCollarCover.annulus ι n) :
    (direction ι n z).1 = z.1.1 :=
  rfl

/-- The direction coordinate is the normalized vector of the same original disk point. -/
theorem direction_val (n : ℕ) (z : CellCollarCover.annulus ι n) :
    (direction ι n z).2.down.val = ‖z.1.2.down.val‖⁻¹ • z.1.2.down.val := by
  exact TopPair.closedUnitBallAnnulusSphereProd_direction (component ι n z)

/-- The radius coordinate is exactly the original disk norm. -/
theorem radius_val (n : ℕ) (z : CellCollarCover.annulus ι n) :
    (radius ι n z : ℝ) = CellCollarCover.diskNorm n z.1 :=
  TopPair.closedUnitBallAnnulusSphereProd_radius (component ι n z)

/-- The inverse coordinates retain the exact original boundary family index. -/
theorem inverse_index (n : ℕ)
    (p : CellFamilyAttachment.boundaries ι n × TopPair.cellAnnulusRadii) :
    (inverse ι n p).1.1 = p.1.1 :=
  rfl

/-- The inverse coordinates scale the original lifted boundary vector by its original radius. -/
theorem inverse_val (n : ℕ)
    (p : CellFamilyAttachment.boundaries ι n × TopPair.cellAnnulusRadii) :
    (inverse ι n p).1.2.down.val = (p.2 : ℝ) • p.1.2.down.val :=
  TopPair.closedUnitBallAnnulusSphereProd_symm_val (p.1.2, p.2)

/-- On a given original annulus component, direction is its original boundary coordinate. -/
theorem direction_component (n : ℕ) (i : ι)
    (z : TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) :
    direction ι n (componentInclusion n i z) =
      (⟨i, (TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin (n + 1) → ℝ) z).1⟩ :
        CellFamilyAttachment.boundaries ι n) :=
  rfl

/-- On a given original annulus component, radius is its existing original radius coordinate. -/
theorem radius_component (n : ℕ) (i : ι)
    (z : TopPair.closedUnitBallAnnulus.{u} (Fin (n + 1) → ℝ)) :
    radius ι n (componentInclusion n i z) =
      (TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin (n + 1) → ℝ) z).2 :=
  rfl

/-- The inverse coordinates in a given summand are exactly the original component inverse. -/
theorem inverse_component (n : ℕ) (i : ι)
    (b : (classicalCellDiskPair.{u} (n + 1)).snd) (r : TopPair.cellAnnulusRadii) :
    inverse ι n ((⟨i, b⟩ : CellFamilyAttachment.boundaries ι n), r) =
      componentInclusion n i
        ((TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin (n + 1) → ℝ)).symm (b, r)) :=
  rfl

/-- Direction and radius reconstruct every original family-annulus point. -/
theorem inverse_direction_radius (n : ℕ) (z : CellCollarCover.annulus ι n) :
    inverse ι n (direction ι n z, radius ι n z) = z :=
  (homeomorph ι n).symm_apply_apply z

/-- Direction of inverse coordinates is the same original boundary point. -/
theorem direction_inverse (n : ℕ)
    (p : CellFamilyAttachment.boundaries ι n × TopPair.cellAnnulusRadii) :
    direction ι n (inverse ι n p) = p.1 :=
  congrArg Prod.fst ((homeomorph ι n).apply_symm_apply p)

/-- Radius of inverse coordinates is the same original radius. -/
theorem radius_inverse (n : ℕ)
    (p : CellFamilyAttachment.boundaries ι n × TopPair.cellAnnulusRadii) :
    radius ι n (inverse ι n p) = p.2 :=
  congrArg Prod.snd ((homeomorph ι n).apply_symm_apply p)

/-- The original disk norm of inverse coordinates is exactly the supplied annular radius. -/
theorem inverse_norm (n : ℕ)
    (p : CellFamilyAttachment.boundaries ι n × TopPair.cellAnnulusRadii) :
    CellCollarCover.diskNorm n (inverse ι n p).1 = (p.2 : ℝ) := by
  have h := congrArg (fun r : TopPair.cellAnnulusRadii => (r : ℝ)) (radius_inverse n p)
  exact (radius_val n (inverse ι n p)).symm.trans h

end AlgebraicTopology.CellAnnulusCoordinates

end

end
