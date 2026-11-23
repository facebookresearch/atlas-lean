/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellFamilyAttachment
public import MathlibExt.Topology.Category.TopPair.ClosedBall.NDR
public import MathlibExt.Topology.Category.TopPair.NDRCoproduct
public import MathlibExt.Topology.Category.TopPair.NDRIso

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Controlled collars of literal classical cell families

The actual sigma boundary-to-disk map is compared with the categorical
coproduct of the same classical pairs. Transport of their existing controlled
NDR data retains every indexed disk, boundary, control and radial deformation.
The controlled neighborhood is exactly the union of the disk collars with
norm greater than one half. Its retraction takes values in the original
literal boundary sigma, and its deformation fixes those boundaries.

The index type is arbitrary, including an empty type. These constructions
precede descent to the original-space collar in a cell-attachment pushout.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Topology Topology.CWComplex
open scoped unitInterval

universe u

namespace AlgebraicTopology.CellFamilyAttachment

/-- The pair given by the actual literal boundary-to-disk sigma map. -/
def literalPair (ι : Type u) (n : ℕ) : TopPair.{u} :=
  TopPair.of (boundaryToDisks ι n)
    (boundaryToDisks_isClosedEmbedding ι n).toIsEmbedding

/-- The ambient object of the literal pair is the original disk sigma. -/
theorem literalPair_fst (ι : Type u) (n : ℕ) : (literalPair ι n).fst = disks ι n :=
  rfl

/-- The subspace object of the literal pair is the original boundary sigma. -/
theorem literalPair_snd (ι : Type u) (n : ℕ) : (literalPair ι n).snd = boundaries ι n :=
  rfl

/-- The pair embedding is the original literal boundary-to-disk map. -/
theorem literalPair_map (ι : Type u) (n : ℕ) :
    (literalPair ι n).map = boundaryToDisks ι n :=
  rfl

/-- The categorical pair coproduct is compared with its original literal
sigma objects by the canonical TopCat coproduct comparisons. -/
def sigmaPairIso (ι : Type u) (n : ℕ) :
    TopPair.sigma (fun _ : ι => classicalCellDiskPair.{u} (n + 1)) ≅
      literalPair ι n :=
  CategoryTheory.MorphismProperty.Arrow.isoMk
    (TopCat.sigmaIsoSigma (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd))
    (TopCat.sigmaIsoSigma (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst)) (by
      change
        (TopCat.sigmaIsoSigma
          (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd)).hom ≫
            boundaryToDisks ι n =
          Limits.Sigma.map (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).map) ≫
            (TopCat.sigmaIsoSigma
              (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst)).hom
      apply Limits.Sigma.hom_ext
      intro i
      apply TopCat.ext
      intro z
      have hBoundary :
          (TopCat.sigmaIsoSigma
            (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd)).hom
              (Limits.Sigma.ι
                (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i z) =
          (⟨i, z⟩ : boundaries ι n) :=
        TopCat.sigmaIsoSigma_hom_ι_apply
          (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i z
      have hMap :
          Limits.Sigma.map (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).map)
              (Limits.Sigma.ι
                (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i z) =
          Limits.Sigma.ι (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst) i
            ((classicalCellDiskPair.{u} (n + 1)).map z) :=
        ConcreteCategory.congr_hom
          (Limits.Sigma.ι_map (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).map) i) z
      have hDisk :
          (TopCat.sigmaIsoSigma
            (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst)).hom
              (Limits.Sigma.ι (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst) i
                ((classicalCellDiskPair.{u} (n + 1)).map z)) =
          (⟨i, (classicalCellDiskPair.{u} (n + 1)).map z⟩ : disks ι n) :=
        TopCat.sigmaIsoSigma_hom_ι_apply
          (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst) i
          ((classicalCellDiskPair.{u} (n + 1)).map z)
      have hLeft :
          boundaryToDisks ι n
            ((TopCat.sigmaIsoSigma
              (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd)).hom
                (Limits.Sigma.ι
                  (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i z)) =
          (⟨i, (classicalCellDiskPair.{u} (n + 1)).map z⟩ : disks ι n) :=
        congrArg (boundaryToDisks ι n) hBoundary
      have hRight := (congrArg
        (TopCat.sigmaIsoSigma
          (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst)).hom hMap).trans hDisk
      change boundaryToDisks ι n
          ((TopCat.sigmaIsoSigma
            (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd)).hom
              (Limits.Sigma.ι
                (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i z)) =
        (TopCat.sigmaIsoSigma
          (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst)).hom
            (Limits.Sigma.map (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).map)
              (Limits.Sigma.ι
                (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i z))
      exact hLeft.trans hRight.symm)

/-- The forward ambient map is the canonical disk coproduct comparison. -/
theorem sigmaPairIso_hom_fst (ι : Type u) (n : ℕ) :
    TopPair.Hom.fst (sigmaPairIso ι n).hom =
      (TopCat.sigmaIsoSigma (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst)).hom :=
  rfl

/-- The forward subspace map is the canonical boundary coproduct comparison. -/
theorem sigmaPairIso_hom_snd (ι : Type u) (n : ℕ) :
    TopPair.Hom.snd (sigmaPairIso ι n).hom =
      (TopCat.sigmaIsoSigma (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd)).hom :=
  rfl

/-- The inverse ambient map is the inverse disk coproduct comparison. -/
theorem sigmaPairIso_inv_fst (ι : Type u) (n : ℕ) :
    TopPair.Hom.fst (sigmaPairIso ι n).inv =
      (TopCat.sigmaIsoSigma (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst)).inv :=
  rfl

/-- The inverse subspace map is the inverse boundary coproduct comparison. -/
theorem sigmaPairIso_inv_snd (ι : Type u) (n : ℕ) :
    TopPair.Hom.snd (sigmaPairIso ι n).inv =
      (TopCat.sigmaIsoSigma (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd)).inv :=
  rfl

variable {ι : Type u}

/-- A categorical disk component maps to the same literal indexed disk. -/
theorem sigmaPairIso_hom_fst_apply (n : ℕ) (i : ι)
    (z : (classicalCellDiskPair.{u} (n + 1)).fst) :
    TopPair.Hom.fst (sigmaPairIso ι n).hom
        (TopPair.Hom.fst
          (TopPair.sigmaι (fun _ : ι => classicalCellDiskPair.{u} (n + 1)) i) z) =
      (⟨i, z⟩ : disks ι n) := by
  rw [sigmaPairIso_hom_fst, TopPair.sigmaι_fst]
  exact TopCat.sigmaIsoSigma_hom_ι_apply
    (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst) i z

/-- A categorical boundary component maps to the same literal indexed boundary. -/
theorem sigmaPairIso_hom_snd_apply (n : ℕ) (i : ι)
    (z : (classicalCellDiskPair.{u} (n + 1)).snd) :
    TopPair.Hom.snd (sigmaPairIso ι n).hom
        (TopPair.Hom.snd
          (TopPair.sigmaι (fun _ : ι => classicalCellDiskPair.{u} (n + 1)) i) z) =
      (⟨i, z⟩ : boundaries ι n) := by
  rw [sigmaPairIso_hom_snd, TopPair.sigmaι_snd]
  exact TopCat.sigmaIsoSigma_hom_ι_apply
    (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i z

/-- Existing component NDR data transported to the actual literal family pair. -/
def ndrData (ι : Type u) (n : ℕ) : TopPair.NDRData (literalPair ι n) :=
  (TopPair.NDRData.sigma.{u, u}
    (P := fun _ : ι => classicalCellDiskPair.{u} (n + 1))
    (fun _ : ι => classicalCellDiskPairNDRData.{u} (n + 1))).ofIso (sigmaPairIso ι n)

/-- The literal control retains the original control on each disk. -/
theorem ndrData_control_component (n : ℕ) (i : ι)
    (z : (classicalCellDiskPair.{u} (n + 1)).fst) :
    (ndrData ι n).control ⟨i, z⟩ =
      (classicalCellDiskPairNDRData.{u} (n + 1)).control z := by
  let P : ι → TopPair.{u} := fun _ => classicalCellDiskPair.{u} (n + 1)
  let d : (i : ι) → TopPair.NDRData (P i) :=
    fun _ => classicalCellDiskPairNDRData.{u} (n + 1)
  have h := TopPair.NDRData.ofIso_control_hom
    (TopPair.NDRData.sigma.{u, u} d) (sigmaPairIso ι n)
    (TopPair.Hom.fst (TopPair.sigmaι P i) z)
  rw [sigmaPairIso_hom_fst_apply] at h
  change (ndrData ι n).control ⟨i, z⟩ =
    TopPair.NDRData.sigmaControl.{u, u} d (TopPair.Hom.fst (TopPair.sigmaι P i) z) at h
  rw [TopPair.NDRData.sigmaControl_ι] at h
  exact h

/-- The literal endpoint stays in the original component and uses its radial endpoint. -/
theorem ndrData_endpoint_component (n : ℕ) (i : ι)
    (z : (classicalCellDiskPair.{u} (n + 1)).fst) :
    (ndrData ι n).endpoint ⟨i, z⟩ =
      (⟨i, (classicalCellDiskPairNDRData.{u} (n + 1)).endpoint z⟩ : disks ι n) := by
  let P : ι → TopPair.{u} := fun _ => classicalCellDiskPair.{u} (n + 1)
  let d : (i : ι) → TopPair.NDRData (P i) :=
    fun _ => classicalCellDiskPairNDRData.{u} (n + 1)
  have h := TopPair.NDRData.ofIso_endpoint_hom
    (TopPair.NDRData.sigma.{u, u} d) (sigmaPairIso ι n)
    (TopPair.Hom.fst (TopPair.sigmaι P i) z)
  rw [sigmaPairIso_hom_fst_apply] at h
  change (ndrData ι n).endpoint ⟨i, z⟩ =
    TopPair.Hom.fst (sigmaPairIso ι n).hom
      (TopPair.NDRData.sigmaEndpoint.{u, u} d
        (TopPair.Hom.fst (TopPair.sigmaι P i) z)) at h
  rw [TopPair.NDRData.sigmaEndpoint_ι, sigmaPairIso_hom_fst_apply] at h
  exact h

/-- The literal joint deformation retains the same component and original radial map. -/
theorem ndrData_deformation_component (n : ℕ) (i : ι) (t : I)
    (z : (classicalCellDiskPair.{u} (n + 1)).fst) :
    (ndrData ι n).deformation (t, ⟨i, z⟩) =
      (⟨i, (classicalCellDiskPairNDRData.{u} (n + 1)).deformation (t, z)⟩ : disks ι n) := by
  let P : ι → TopPair.{u} := fun _ => classicalCellDiskPair.{u} (n + 1)
  let d : (i : ι) → TopPair.NDRData (P i) :=
    fun _ => classicalCellDiskPairNDRData.{u} (n + 1)
  have h := TopPair.NDRData.ofIso_deformation_hom
    (TopPair.NDRData.sigma.{u, u} d) (sigmaPairIso ι n) t
    (TopPair.Hom.fst (TopPair.sigmaι P i) z)
  rw [sigmaPairIso_hom_fst_apply] at h
  change (ndrData ι n).deformation (t, ⟨i, z⟩) =
    TopPair.Hom.fst (sigmaPairIso ι n).hom
      (TopPair.NDRData.sigmaDeformation.{u, u} d
        (t, TopPair.Hom.fst (TopPair.sigmaι P i) z)) at h
  rw [TopPair.NDRData.sigmaDeformation_ι, sigmaPairIso_hom_fst_apply] at h
  exact h

/-- The actual control is the clamped original disk-norm formula. -/
theorem ndrData_control_apply (n : ℕ) (i : ι)
    (z : (classicalCellDiskPair.{u} (n + 1)).fst) :
    (ndrData ι n).control ⟨i, z⟩ =
      Set.projIcc 0 1 zero_le_one (2 * (1 - ‖z.down.val‖)) := by
  exact (ndrData_control_component n i z).trans (by rfl)

/-- The controlled neighborhood is exactly the strict half-radius collar. -/
theorem ndrData_control_lt_one_iff (n : ℕ) (z : disks ι n) :
    (ndrData ι n).control z < 1 ↔ (1 : ℝ) / 2 < ‖z.2.down.val‖ := by
  obtain ⟨i, z⟩ := z
  change ((ndrData ι n).control ⟨i, z⟩ : ℝ) < 1 ↔
    (1 : ℝ) / 2 < ‖z.down.val‖
  rw [ndrData_control_apply, Set.coe_projIcc, max_lt_iff, min_lt_iff]
  constructor
  · rintro ⟨_, h | h⟩
    · exact (lt_irrefl (1 : ℝ) h).elim
    · linarith
  · intro h
    refine ⟨by norm_num, Or.inr ?_⟩
    linarith

/-- The canonical NDR neighborhood is the literal set of all indexed disk collars. -/
theorem ndrData_neighborhood (ι : Type u) (n : ℕ) :
    (ndrData ι n).neighborhood =
      {z : disks ι n | (1 : ℝ) / 2 < ‖z.2.down.val‖} := by
  ext z
  exact ndrData_control_lt_one_iff n z

/-- The radial endpoint reaches the original literal boundary sigma on the collar. -/
theorem ndrData_endpoint_mem_range (n : ℕ) (z : disks ι n)
    (hz : (1 : ℝ) / 2 < ‖z.2.down.val‖) :
    (ndrData ι n).endpoint z ∈ Set.range (boundaryToDisks ι n) :=
  (ndrData ι n).endpoint_mem_range z ((ndrData_control_lt_one_iff n z).mpr hz)

/-- The actual global deformation preserves the strict half-radius collar. -/
theorem ndrData_deformation_mem_collar (n : ℕ) (t : I) (z : disks ι n)
    (hz : (1 : ℝ) / 2 < ‖z.2.down.val‖) :
    (1 : ℝ) / 2 < ‖((ndrData ι n).deformation (t, z)).2.down.val‖ := by
  have hz' : z ∈ (ndrData ι n).neighborhood :=
    (ndrData_control_lt_one_iff n z).mpr hz
  have h := (ndrData ι n).deformation_mem_neighborhood t hz'
  exact (ndrData_control_lt_one_iff n ((ndrData ι n).deformation (t, z))).mp h

/-- The global radial deformation fixes every original literal boundary point. -/
theorem ndrData_deformation_boundary (n : ℕ) (t : I) (a : boundaries ι n) :
    (ndrData ι n).deformation (t, boundaryToDisks ι n a) = boundaryToDisks ι n a :=
  (ndrData ι n).deformation.eq_fst t ⟨a, rfl⟩

/-- The original literal boundaries included in their controlled collar. -/
def collarInclusion (ι : Type u) (n : ℕ) :
    boundaries ι n ⟶ TopCat.of (ndrData ι n).neighborhood :=
  TopPair.neighborhoodInclusion (literalPair ι n) (ndrData ι n).neighborhood
    (ndrData ι n).range_subset_neighborhood

/-- The collar inclusion has the original boundary-to-disk value. -/
theorem collarInclusion_val (n : ℕ) (a : boundaries ι n) :
    (collarInclusion ι n a).1 = boundaryToDisks ι n a :=
  rfl

/-- Retraction of the controlled collar to the original literal boundary sigma. -/
def collarRetraction (ι : Type u) (n : ℕ) :
    TopCat.of (ndrData ι n).neighborhood ⟶ boundaries ι n :=
  (ndrData ι n).retraction

private theorem component_mem_neighborhood (n : ℕ) (i : ι)
    (z : (classicalCellDiskPairNDRData.{u} (n + 1)).neighborhood) :
    (⟨i, z.1⟩ : disks ι n) ∈ (ndrData ι n).neighborhood := by
  change (ndrData ι n).control ⟨i, z.1⟩ < 1
  rw [ndrData_control_component]
  exact z.2

/-- The actual inclusion of one controlled disk collar into the literal family collar. -/
def collarι (n : ℕ) (i : ι) :
    TopCat.of (classicalCellDiskPairNDRData.{u} (n + 1)).neighborhood ⟶
      TopCat.of (ndrData ι n).neighborhood :=
  TopCat.ofHom
    { toFun := fun z => ⟨⟨i, z.1⟩, by exact component_mem_neighborhood n i z⟩
      continuous_toFun := by
        exact ((TopCat.sigmaι
          (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst) i).hom.continuous.comp
            continuous_subtype_val).subtype_mk
          (fun z => by exact component_mem_neighborhood n i z) }

/-- A component collar point retains its literal disk index and value. -/
theorem collarι_val (n : ℕ) (i : ι)
    (z : (classicalCellDiskPairNDRData.{u} (n + 1)).neighborhood) :
    (collarι n i z).1 = (⟨i, z.1⟩ : disks ι n) :=
  rfl

/-- The family collar retraction restricts to the original component retraction. -/
@[reassoc]
theorem collarRetraction_component (n : ℕ) (i : ι) :
    collarι n i ≫ collarRetraction ι n =
      (classicalCellDiskPairNDRData.{u} (n + 1)).retraction ≫
        TopCat.sigmaι (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i := by
  apply TopCat.ext
  intro z
  apply (boundaryToDisks_isClosedEmbedding ι n).injective
  change (literalPair ι n).map
      ((ndrData ι n).retraction (collarι n i z)) =
    boundaryToDisks ι n
      ⟨i, (classicalCellDiskPairNDRData.{u} (n + 1)).retraction z⟩
  rw [TopPair.NDRData.map_retraction, collarι_val,
    ndrData_endpoint_component, boundaryToDisks_apply]
  exact congrArg (fun w : (classicalCellDiskPair.{u} (n + 1)).fst =>
    (⟨i, w⟩ : disks ι n))
      ((classicalCellDiskPairNDRData.{u} (n + 1)).map_retraction z).symm

/-- The actual literal collar retraction is the identity on every boundary point. -/
@[reassoc]
theorem collarInclusion_retraction (ι : Type u) (n : ℕ) :
    collarInclusion ι n ≫ collarRetraction ι n = 𝟙 (boundaries ι n) := by
  apply TopCat.ext
  intro a
  apply (boundaryToDisks_isClosedEmbedding ι n).injective
  change (literalPair ι n).map
      ((ndrData ι n).retraction (collarInclusion ι n a)) = boundaryToDisks ι n a
  rw [TopPair.NDRData.map_retraction, collarInclusion_val]
  exact ((ndrData ι n).deformation.apply_one (boundaryToDisks ι n a)).symm.trans
    (ndrData_deformation_boundary n 1 a)

/-- The actual controlled collar deforms from identity to its boundary retraction,
fixing the original literal boundary sigma. -/
def collarDeformation (ι : Type u) (n : ℕ) :
    ContinuousMap.HomotopyRel
      ((𝟙 (TopCat.of (ndrData ι n).neighborhood)) :
        TopCat.of (ndrData ι n).neighborhood ⟶
          TopCat.of (ndrData ι n).neighborhood).hom
      (collarRetraction ι n ≫ collarInclusion ι n).hom
      (Set.range (collarInclusion ι n).hom) :=
  (ndrData ι n).neighborhoodDeformation

/-- The collar deformation is the same original global deformation on underlying points. -/
theorem collarDeformation_val (n : ℕ) (t : I) (z : (ndrData ι n).neighborhood) :
    (collarDeformation ι n (t, z)).1 = (ndrData ι n).deformation (t, z.1) :=
  rfl

/-- The collar deformation retains the original disk index and component deformation. -/
theorem collarDeformation_component (n : ℕ) (i : ι) (t : I)
    (z : (classicalCellDiskPairNDRData.{u} (n + 1)).neighborhood) :
    (collarDeformation ι n (t, collarι n i z)).1 =
      (⟨i, (classicalCellDiskPairNDRData.{u} (n + 1)).deformation (t, z.1)⟩ :
        disks ι n) := by
  rw [collarDeformation_val, collarι_val]
  exact ndrData_deformation_component n i t z.1

/-- Every original boundary point is fixed throughout the actual collar deformation. -/
theorem collarDeformation_boundary (n : ℕ) (t : I) (a : boundaries ι n) :
    collarDeformation ι n (t, collarInclusion ι n a) = collarInclusion ι n a :=
  (collarDeformation ι n).eq_fst t ⟨a, rfl⟩

end AlgebraicTopology.CellFamilyAttachment

end

end
