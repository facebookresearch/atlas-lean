/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.SigmaSubtypeFullness
public import MathlibExt.AlgebraicTopology.PlusConstruction.CellAnnulusOverlap
public import Mathlib.Analysis.Convex.Contractible

/-!
# Components of the inner two-cell region

The open inner square in one classical two-cell is homeomorphic to the open
max-norm ball of radius `3 / 4`, and hence is contractible and simply
connected.  The corresponding square annulus is path connected.  These
component facts assemble over an arbitrary cell index.

The resulting sigma homeomorphisms identify the componentwise annulus
inclusion with the actual inclusion from the collar overlap into the inner
region of a cell-family attachment.  Consequently the induced actual
fundamental-groupoid functor is full and essentially surjective.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex

universe u

namespace AlgebraicTopology.CellInnerComponents

/-- The strict three-quarter-radius inner part of one original classical
two-cell. -/
abbrev InnerSquare : Type u :=
  {z : (classicalCellDiskPair.{u} 2).fst // ‖z.down.val‖ < (3 : ℝ) / 4}

/-- The original inner square is the lifted open max-norm ball of radius
`3 / 4`. -/
def innerSquareBallHomeomorph :
    InnerSquare.{u} ≃ₜ ULift.{u} (Metric.ball (0 : Fin 2 → ℝ) ((3 : ℝ) / 4)) where
  toFun z := ULift.up ⟨z.1.down.val, by
    simpa only [Metric.mem_ball, dist_zero_right] using z.2⟩
  invFun w := ⟨ULift.up ⟨w.down.val, by
      have hw : ‖w.down.val‖ < (3 : ℝ) / 4 := by
        simpa only [Metric.mem_ball, dist_zero_right] using w.down.property
      change w.down.val ∈ Metric.closedBall (0 : Fin 2 → ℝ) 1
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith⟩, by
        simpa only using (show ‖w.down.val‖ < (3 : ℝ) / 4 by
          simpa only [Metric.mem_ball, dist_zero_right] using w.down.property)⟩
  left_inv z := by rfl
  right_inv w := by rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Every original inner square is contractible. -/
noncomputable instance innerSquareContractibleSpace :
    ContractibleSpace InnerSquare.{u} := by
  let _ : ContractibleSpace (Metric.ball (0 : Fin 2 → ℝ) ((3 : ℝ) / 4)) :=
    Metric.contractibleSpace_ball (by norm_num : (0 : ℝ) < 3 / 4)
  let _ : ContractibleSpace (ULift.{u} (Metric.ball
      (0 : Fin 2 → ℝ) ((3 : ℝ) / 4))) :=
    (Homeomorph.ulift
      (X := Metric.ball (0 : Fin 2 → ℝ) ((3 : ℝ) / 4))).contractibleSpace
  exact innerSquareBallHomeomorph.{u}.contractibleSpace

/-- Every original inner square is simply connected. -/
theorem innerSquare_simplyConnectedSpace :
    SimplyConnectedSpace InnerSquare.{u} :=
  inferInstance

/-- The original square annulus is path connected, using its constructed
connector to the common original basepoint. -/
noncomputable instance classicalCellSquareAnnulusPathConnectedSpace :
    PathConnectedSpace classicalCellSquareAnnulus.{u} where
  nonempty := ⟨classicalCellSquareAnnulusBasepoint.{u}⟩
  joined a b := ⟨(classicalCellSquareAnnulusConnector a).symm.trans
    (classicalCellSquareAnnulusConnector b)⟩

/-- Include one original square annulus in the same original inner square. -/
def annulusToInnerSquare : C(classicalCellSquareAnnulus.{u}, InnerSquare.{u}) where
  toFun z := ⟨z.1, z.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk (fun z => z.2.2)

/-- The component inclusion retains the original lifted disk point. -/
@[simp]
theorem annulusToInnerSquare_val (z : classicalCellSquareAnnulus.{u}) :
    (annulusToInnerSquare z).val = z.val :=
  rfl

/-- The literal componentwise sigma map from square annuli to inner squares
is full on fundamental groupoids. -/
theorem annulusSigmaMap_full (ι : Type u) :
    (FundamentalGroupoid.map
      (FundamentalGroupoid.SigmaSubtype.map
        (fun _ : ι => classicalCellSquareAnnulus.{u})
        (fun _ : ι => InnerSquare.{u})
        (fun _ => annulusToInnerSquare))).Full :=
  FundamentalGroupoid.SigmaSubtype.mapFull _ _ _

/-- The literal componentwise sigma map from square annuli to inner squares
is essentially surjective on fundamental groupoids. -/
theorem annulusSigmaMap_essSurj (ι : Type u) :
    (FundamentalGroupoid.map
      (FundamentalGroupoid.SigmaSubtype.map
        (fun _ : ι => classicalCellSquareAnnulus.{u})
        (fun _ : ι => InnerSquare.{u})
        (fun _ => annulusToInnerSquare))).EssSurj :=
  FundamentalGroupoid.SigmaSubtype.mapEssSurj _ _ _

/-- Assemble the literal sigma of inner squares into the existing indexed
inner subset of the disk family. -/
def innerSigmaToFamily (ι : Type u) :
    (Σ _ : ι, InnerSquare.{u}) → CellCollarCover.inner ι 1 :=
  fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩

/-- The assembled inner-square map is a homeomorphism onto the existing
indexed inner subset. -/
theorem innerSigmaToFamily_isHomeomorph (ι : Type u) :
    IsHomeomorph (innerSigmaToFamily ι) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold innerSigmaToFamily
    apply continuous_sigma
    intro i
    change Continuous (fun z : InnerSquare.{u} =>
      (⟨⟨i, z.1⟩, z.2⟩ : CellCollarCover.inner ι 1))
    exact ((continuous_sigmaMk
      (σ := fun _ : ι => (classicalCellDiskPair.{u} 2).fst) (i := i)).comp
        continuous_subtype_val).subtype_mk (fun _ => _)
  · rw [isOpenMap_sigma]
    intro i
    let f : InnerSquare.{u} → CellFamilyAttachment.disks ι 1 :=
      fun z => ⟨i, z.1⟩
    have hf : IsOpenMap f := by
      have hsub : IsOpenMap (fun z : InnerSquare.{u} => z.1) :=
        (isOpen_lt (continuous_norm.comp
          (continuous_subtype_val.comp continuous_uliftDown))
            continuous_const).isOpenMap_subtype_val
      have hsigma : IsOpenMap (fun z : (classicalCellDiskPair.{u} 2).fst =>
          (Sigma.mk i z : CellFamilyAttachment.disks ι 1)) :=
        isOpenMap_sigmaMk
          (σ := fun _ : ι => (classicalCellDiskPair.{u} 2).fst) (i := i)
      exact hsigma.comp hsub
    exact hf.codRestrict (fun z => z.2)
  · rintro ⟨i, z⟩ ⟨j, w⟩ h
    have hij : i = j := congrArg (fun y => y.1.1) h
    subst j
    have hzw : z.1 = w.1 := congrArg (fun y => y.1.2) h
    cases z
    cases w
    simp_all
  · rintro ⟨⟨i, z⟩, hz⟩
    exact ⟨⟨i, ⟨z, hz⟩⟩, rfl⟩

/-- The existing indexed inner subset, in literal sigma coordinates. -/
def innerFamilySigmaHomeomorph (ι : Type u) :
    CellCollarCover.inner ι 1 ≃ₜ (Σ _ : ι, InnerSquare.{u}) :=
  (innerSigmaToFamily_isHomeomorph ι).homeomorph (innerSigmaToFamily ι) |>.symm

/-- The existing indexed inner subset maps homeomorphically to the actual
inner region of the cell-family attachment. -/
def innerFamilyVHomeomorph {ι : Type u} (X : TopCat.{u})
    (a : ι → ((classicalCellDiskPair.{u} 2).snd ⟶ X)) :
    CellCollarCover.inner ι 1 ≃ₜ CellCollarCover.V X 1 a :=
  (Homeomorph.setCongr
    (CellCollarCover.diskInclusion_preimage_V X 1 a).symm).trans
      (IsHomeomorph.homeomorph
        ((CellCollarCover.V X 1 a).restrictPreimage
          (CellFamilyAttachment.diskInclusion X 1 a))
        (CellCollarCover.isHomeomorph_V_diskRestriction X 1 a))

/-- The actual inner-region homeomorphism retains the characteristic value
of the same original disk point. -/
theorem innerFamilyVHomeomorph_val {ι : Type u} (X : TopCat.{u})
    (a : ι → ((classicalCellDiskPair.{u} 2).snd ⟶ X))
    (z : CellCollarCover.inner ι 1) :
    (innerFamilyVHomeomorph X a z).val =
      CellFamilyAttachment.diskInclusion X 1 a z.val :=
  rfl

/-- Literal sigma coordinates for the actual inner region. -/
def innerSigmaVHomeomorph {ι : Type u} (X : TopCat.{u})
    (a : ι → ((classicalCellDiskPair.{u} 2).snd ⟶ X)) :
    (Σ _ : ι, InnerSquare.{u}) ≃ₜ CellCollarCover.V X 1 a :=
  (innerFamilySigmaHomeomorph ι).symm.trans (innerFamilyVHomeomorph X a)

/-- Sigma coordinates for the inner region retain the characteristic value
of their original indexed disk point. -/
theorem innerSigmaVHomeomorph_val {ι : Type u} (X : TopCat.{u})
    (a : ι → ((classicalCellDiskPair.{u} 2).snd ⟶ X))
    (z : Σ _ : ι, InnerSquare.{u}) :
    (innerSigmaVHomeomorph X a z).val =
      CellFamilyAttachment.diskInclusion X 1 a ⟨z.1, z.2.1⟩ :=
  rfl

/-- Literal sigma coordinates for the actual collar overlap. -/
def annulusSigmaOverlapHomeomorph {ι : Type u} (X : TopCat.{u})
    (a : ι → ((classicalCellDiskPair.{u} 2).snd ⟶ X)) :
    (Σ _ : ι, classicalCellSquareAnnulus.{u}) ≃ₜ
      ↥(CellCollarCover.U X 1 a ∩ CellCollarCover.V X 1 a) :=
  (CellAnnulusComponents.sigmaToFamilyHomeomorph ι 1).trans
    (CellAnnulusOverlap.homeomorph X 1 a)

/-- Sigma coordinates for the overlap retain the characteristic value of
their original indexed annular disk point. -/
theorem annulusSigmaOverlapHomeomorph_val {ι : Type u} (X : TopCat.{u})
    (a : ι → ((classicalCellDiskPair.{u} 2).snd ⟶ X))
    (z : Σ _ : ι, classicalCellSquareAnnulus.{u}) :
    (annulusSigmaOverlapHomeomorph X a z).val =
      CellFamilyAttachment.diskInclusion X 1 a ⟨z.1, z.2.1⟩ := by
  rcases z with ⟨i, z⟩
  exact (CellAnnulusOverlap.homeomorph_val X 1 a
    (CellAnnulusComponents.sigmaToFamilyHomeomorph ι 1 ⟨i, z⟩)).trans
      (congrArg (CellFamilyAttachment.diskInclusion X 1 a)
        (congrArg Subtype.val
          (CellAnnulusComponents.sigmaToFamilyHomeomorph_apply ι 1 i z)))

/-- The actual overlap inclusion is the componentwise annulus inclusion,
transported through the two constructed sigma homeomorphisms. -/
theorem overlapInclusion_factorization {ι : Type u} (X : TopCat.{u})
    (a : ι → ((classicalCellDiskPair.{u} 2).snd ⟶ X)) :
    (innerSigmaVHomeomorph X a).toHomotopyEquiv.toFun.comp
        ((FundamentalGroupoid.SigmaSubtype.map
          (fun _ : ι => classicalCellSquareAnnulus.{u})
          (fun _ : ι => InnerSquare.{u})
          (fun _ => annulusToInnerSquare)).comp
            (annulusSigmaOverlapHomeomorph X a).symm.toHomotopyEquiv.toFun) =
      MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionInterRight
        (CellCollarCover.U X 1 a) (CellCollarCover.V X 1 a) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  let H := annulusSigmaOverlapHomeomorph X a
  let s := H.symm z
  change (innerSigmaVHomeomorph X a
      (FundamentalGroupoid.SigmaSubtype.map
        (fun _ : ι => classicalCellSquareAnnulus.{u})
        (fun _ : ι => InnerSquare.{u})
        (fun _ => annulusToInnerSquare) s)).val = z.val
  rw [innerSigmaVHomeomorph_val]
  exact (annulusSigmaOverlapHomeomorph_val X a s).symm.trans
    (congrArg Subtype.val (H.apply_symm_apply z))

/-- The actual overlap-to-inner fundamental-groupoid functor is full. -/
theorem overlapInclusion_full {ι : Type u} (X : TopCat.{u})
    (a : ι → ((classicalCellDiskPair.{u} 2).snd ⟶ X)) :
    (FundamentalGroupoid.map
      (MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionInterRight
        (CellCollarCover.U X 1 a) (CellCollarCover.V X 1 a))).Full := by
  rw [← overlapInclusion_factorization X a,
    FundamentalGroupoid.map_comp, FundamentalGroupoid.map_comp]
  let overlapEquiv := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (annulusSigmaOverlapHomeomorph X a).symm.toHomotopyEquiv
  let innerEquiv := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (innerSigmaVHomeomorph X a).toHomotopyEquiv
  let _ : (FundamentalGroupoid.map
      (annulusSigmaOverlapHomeomorph X a).symm.toHomotopyEquiv.toFun).IsEquivalence :=
    overlapEquiv.isEquivalence_functor
  let _ : (FundamentalGroupoid.map
      (FundamentalGroupoid.SigmaSubtype.map
        (fun _ : ι => classicalCellSquareAnnulus.{u})
        (fun _ : ι => InnerSquare.{u})
        (fun _ => annulusToInnerSquare))).Full :=
    FundamentalGroupoid.SigmaSubtype.mapFull _ _ _
  let _ : (FundamentalGroupoid.map
      (innerSigmaVHomeomorph X a).toHomotopyEquiv.toFun).IsEquivalence :=
    innerEquiv.isEquivalence_functor
  infer_instance

/-- The actual overlap-to-inner fundamental-groupoid functor is essentially
surjective. -/
theorem overlapInclusion_essSurj {ι : Type u} (X : TopCat.{u})
    (a : ι → ((classicalCellDiskPair.{u} 2).snd ⟶ X)) :
    (FundamentalGroupoid.map
      (MathlibExt.Topology.Homotopy.VanKampenWanted.inclusionInterRight
        (CellCollarCover.U X 1 a) (CellCollarCover.V X 1 a))).EssSurj := by
  rw [← overlapInclusion_factorization X a,
    FundamentalGroupoid.map_comp, FundamentalGroupoid.map_comp]
  let overlapEquiv := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (annulusSigmaOverlapHomeomorph X a).symm.toHomotopyEquiv
  let innerEquiv := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (innerSigmaVHomeomorph X a).toHomotopyEquiv
  let _ : (FundamentalGroupoid.map
      (annulusSigmaOverlapHomeomorph X a).symm.toHomotopyEquiv.toFun).IsEquivalence :=
    overlapEquiv.isEquivalence_functor
  let _ : (FundamentalGroupoid.map
      (FundamentalGroupoid.SigmaSubtype.map
        (fun _ : ι => classicalCellSquareAnnulus.{u})
        (fun _ : ι => InnerSquare.{u})
        (fun _ => annulusToInnerSquare))).EssSurj :=
    FundamentalGroupoid.SigmaSubtype.mapEssSurj _ _ _
  let _ : (FundamentalGroupoid.map
      (innerSigmaVHomeomorph X a).toHomotopyEquiv.toFun).IsEquivalence :=
    innerEquiv.isEquivalence_functor
  infer_instance

end AlgebraicTopology.CellInnerComponents

end

end
