/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CellFamilyAttachment
public import MathlibExt.Topology.Category.TopCat.PushoutComplementImages
public import MathlibExt.Topology.Category.TopPair.ClosedBall.NDR
public import Mathlib.Topology.Order.OrderClosed

import Mathlib.Tactic.NormNum

/-!
# The actual radial open cover of a cell-family attachment

The closed cores have radius at most `1 / 2`, and the open inner disks have
radius less than `3 / 4`, in the original max-norm classical cells. Their
actual pushout images determine the open cover: the complement of the core
image contains the whole original space and its outer collars, while the
inner image retains the original disk points and has no original-space
preimage. The overlap is the actual annulus between the two radii.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Topology Topology.CWComplex

universe u

namespace AlgebraicTopology.CellCollarCover

variable {ι : Type u}

/-- The norm of the original vector in its literal indexed classical disk. -/
def diskNorm (n : ℕ) (z : CellFamilyAttachment.disks ι n) : ℝ :=
  ‖z.2.down.val‖

theorem diskNorm_apply (n : ℕ) (i : ι)
    (z : (classicalCellDiskPair.{u} (n + 1)).fst) :
    diskNorm n (⟨i, z⟩ : CellFamilyAttachment.disks ι n) = ‖z.down.val‖ :=
  rfl

theorem continuous_diskNorm (n : ℕ) : Continuous (diskNorm (ι := ι) n) := by
  apply continuous_sigma
  intro i
  exact continuous_norm.comp (continuous_subtype_val.comp continuous_uliftDown)

/-- Each actual attaching boundary maps to a disk point of radius one. -/
theorem diskNorm_boundaryToDisks (n : ℕ) (i : ι)
    (z : (classicalCellDiskPair.{u} (n + 1)).snd) :
    diskNorm n (CellFamilyAttachment.boundaryToDisks ι n ⟨i, z⟩) = 1 := by
  change ‖z.down.val‖ = 1
  simpa only [Metric.mem_sphere, dist_zero_right] using z.down.property

/-- The full original boundary image is exactly the radius-one locus. -/
theorem mem_range_boundaryToDisks_iff (n : ℕ) (z : CellFamilyAttachment.disks ι n) :
    z ∈ Set.range (CellFamilyAttachment.boundaryToDisks ι n) ↔ diskNorm n z = 1 := by
  obtain ⟨i, d⟩ := z
  constructor
  · rintro ⟨⟨j, b⟩, h⟩
    have hn := diskNorm_boundaryToDisks n j b
    rw [h] at hn
    exact hn
  · intro hd
    have hRange : d ∈ Set.range (classicalCellDiskPair.{u} (n + 1)).map :=
      (TopPair.mem_range_closedUnitBallPair_map_iff.{u, 0}
        (E := Fin (n + 1) → ℝ) d).mpr hd
    obtain ⟨b, hb⟩ := hRange
    refine ⟨⟨i, b⟩, ?_⟩
    change (⟨i, (classicalCellDiskPair.{u} (n + 1)).map b⟩ :
      Σ _ : ι, (classicalCellDiskPair.{u} (n + 1)).fst) = ⟨i, d⟩
    rw [hb]

/-- The actual closed half-radius cores in the original disk coproduct. -/
def core (ι : Type u) (n : ℕ) : Set (CellFamilyAttachment.disks ι n) :=
  {z | diskNorm n z ≤ (1 : ℝ) / 2}

/-- The actual open three-quarter-radius disks in the original disk coproduct. -/
def inner (ι : Type u) (n : ℕ) : Set (CellFamilyAttachment.disks ι n) :=
  {z | diskNorm n z < (3 : ℝ) / 4}

/-- The actual outer collar, still containing each original attaching boundary. -/
def collar (ι : Type u) (n : ℕ) : Set (CellFamilyAttachment.disks ι n) :=
  {z | (1 : ℝ) / 2 < diskNorm n z}

/-- The actual annuli between the two selected radii. -/
def annulus (ι : Type u) (n : ℕ) : Set (CellFamilyAttachment.disks ι n) :=
  {z | (1 : ℝ) / 2 < diskNorm n z ∧ diskNorm n z < (3 : ℝ) / 4}

theorem core_isClosed (ι : Type u) (n : ℕ) : IsClosed (core ι n) :=
  isClosed_le (continuous_diskNorm n) continuous_const

theorem inner_isOpen (ι : Type u) (n : ℕ) : IsOpen (inner ι n) :=
  isOpen_lt (continuous_diskNorm n) continuous_const

theorem collar_isOpen (ι : Type u) (n : ℕ) : IsOpen (collar ι n) :=
  isOpen_lt continuous_const (continuous_diskNorm n)

theorem annulus_isOpen (ι : Type u) (n : ℕ) : IsOpen (annulus ι n) :=
  (collar_isOpen ι n).inter (inner_isOpen ι n)

theorem compl_core (ι : Type u) (n : ℕ) : (core ι n)ᶜ = collar ι n := by
  ext z
  change ¬ diskNorm n z ≤ (1 : ℝ) / 2 ↔ (1 : ℝ) / 2 < diskNorm n z
  exact not_le

theorem core_avoids_boundary (ι : Type u) (n : ℕ) :
    core ι n ⊆ (Set.range (CellFamilyAttachment.boundaryToDisks ι n))ᶜ := by
  intro z hz hBoundary
  have hn := (mem_range_boundaryToDisks_iff n z).mp hBoundary
  change diskNorm n z ≤ (1 : ℝ) / 2 at hz
  rw [hn] at hz
  norm_num at hz

theorem inner_avoids_boundary (ι : Type u) (n : ℕ) :
    inner ι n ⊆ (Set.range (CellFamilyAttachment.boundaryToDisks ι n))ᶜ := by
  intro z hz hBoundary
  have hn := (mem_range_boundaryToDisks_iff n z).mp hBoundary
  change diskNorm n z < (3 : ℝ) / 4 at hz
  rw [hn] at hz
  norm_num at hz

theorem annulus_avoids_boundary (ι : Type u) (n : ℕ) :
    annulus ι n ⊆ (Set.range (CellFamilyAttachment.boundaryToDisks ι n))ᶜ :=
  fun _ hz => inner_avoids_boundary ι n hz.2

variable (X : TopCat.{u}) (n : ℕ)
variable (a : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X))

/-- The actual complement of the closed core image in the computed attachment. -/
def U : Set (CellFamilyAttachment.space X n a) :=
  (CellFamilyAttachment.diskInclusion X n a '' core ι n)ᶜ

/-- The actual image of the open inner disks in the computed attachment. -/
def V : Set (CellFamilyAttachment.space X n a) :=
  CellFamilyAttachment.diskInclusion X n a '' inner ι n

theorem isOpen_U : IsOpen (U X n a) :=
  (TopCat.isClosed_image_left_of_avoids_boundary (CellFamilyAttachment.isPushout X n a)
    (core_avoids_boundary ι n) (core_isClosed ι n)).isOpen_compl

theorem isOpen_V : IsOpen (V X n a) :=
  TopCat.isOpen_image_left_of_avoids_boundary (CellFamilyAttachment.isPushout X n a)
    (inner_avoids_boundary ι n) (inner_isOpen ι n)

/-- Every original point belongs to the actual outer region. -/
theorem inclusion_preimage_U :
    CellFamilyAttachment.inclusion X n a ⁻¹' U X n a = Set.univ :=
  TopCat.preimage_right_compl_image_left_of_avoids_boundary
    (CellFamilyAttachment.isPushout X n a) (core_avoids_boundary ι n)

/-- The actual inner region has no original-space preimage. -/
theorem inclusion_preimage_V :
    CellFamilyAttachment.inclusion X n a ⁻¹' V X n a = ∅ :=
  TopCat.preimage_right_image_left_of_avoids_boundary
    (CellFamilyAttachment.isPushout X n a) (inner_avoids_boundary ι n)

/-- The actual outer region has precisely the complement of the original disk cores as preimage. -/
theorem diskInclusion_preimage_U :
    CellFamilyAttachment.diskInclusion X n a ⁻¹' U X n a = (core ι n)ᶜ :=
  TopCat.preimage_left_compl_image_left_of_avoids_boundary
    (CellFamilyAttachment.isPushout X n a) (core_avoids_boundary ι n)

/-- The disk preimage of the actual outer region is the original strict outer collar. -/
theorem diskInclusion_preimage_U_collar :
    CellFamilyAttachment.diskInclusion X n a ⁻¹' U X n a = collar ι n :=
  (diskInclusion_preimage_U X n a).trans (compl_core ι n)

/-- The actual inner image has precisely the original open inner disks as preimage. -/
theorem diskInclusion_preimage_V :
    CellFamilyAttachment.diskInclusion X n a ⁻¹' V X n a = inner ι n :=
  TopCat.preimage_left_image_left_of_avoids_boundary
    (CellFamilyAttachment.isPushout X n a) (inner_avoids_boundary ι n)

/-- The outer region is the whole original-space image together with the actual outer collars. -/
theorem U_eq_range_inclusion_union_image_collar :
    U X n a = Set.range (CellFamilyAttachment.inclusion X n a) ∪
      CellFamilyAttachment.diskInclusion X n a '' collar ι n := by
  ext y
  constructor
  · intro hy
    rcases CellFamilyAttachment.exists_inclusion_or_cell X n a y with
      ⟨x, hx⟩ | ⟨i, d, hd⟩
    · exact Or.inl ⟨x, hx⟩
    · let b : CellFamilyAttachment.disks ι n := ⟨i, d⟩
      have hb : CellFamilyAttachment.diskInclusion X n a b = y := hd
      have hCollar : b ∈ collar ι n := by
        rw [← diskInclusion_preimage_U_collar X n a]
        change CellFamilyAttachment.diskInclusion X n a b ∈ U X n a
        rw [hb]
        exact hy
      exact Or.inr ⟨b, hCollar, hb⟩
  · rintro (⟨x, hx⟩ | ⟨b, hb, hby⟩)
    · have hxU : x ∈ CellFamilyAttachment.inclusion X n a ⁻¹' U X n a := by
        rw [inclusion_preimage_U]
        exact Set.mem_univ _
      change CellFamilyAttachment.inclusion X n a x ∈ U X n a at hxU
      rwa [hx] at hxU
    · have hbU : b ∈ CellFamilyAttachment.diskInclusion X n a ⁻¹' U X n a := by
        rw [diskInclusion_preimage_U_collar]
        exact hb
      change CellFamilyAttachment.diskInclusion X n a b ∈ U X n a at hbU
      rwa [hby] at hbU

/-- The two constructed open regions cover the entire original attachment, even for no cells. -/
theorem U_union_V : U X n a ∪ V X n a = Set.univ := by
  ext y
  constructor
  · intro _
    exact Set.mem_univ _
  · intro _
    rcases CellFamilyAttachment.exists_inclusion_or_cell X n a y with
      ⟨x, hx⟩ | ⟨i, d, hd⟩
    · apply Or.inl
      have hxU : x ∈ CellFamilyAttachment.inclusion X n a ⁻¹' U X n a := by
        rw [inclusion_preimage_U]
        exact Set.mem_univ _
      change CellFamilyAttachment.inclusion X n a x ∈ U X n a at hxU
      rwa [hx] at hxU
    · let b : CellFamilyAttachment.disks ι n := ⟨i, d⟩
      have hb : CellFamilyAttachment.diskInclusion X n a b = y := hd
      by_cases hCore : b ∈ core ι n
      · apply Or.inr
        have hInner : b ∈ inner ι n := by
          change diskNorm n b < (3 : ℝ) / 4
          exact lt_of_le_of_lt hCore (by norm_num)
        exact ⟨b, hInner, hb⟩
      · apply Or.inl
        have hbU : b ∈ CellFamilyAttachment.diskInclusion X n a ⁻¹' U X n a := by
          rw [diskInclusion_preimage_U]
          exact hCore
        change CellFamilyAttachment.diskInclusion X n a b ∈ U X n a at hbU
        rwa [hb] at hbU

theorem isOpen_intersection : IsOpen (U X n a ∩ V X n a) :=
  (isOpen_U X n a).inter (isOpen_V X n a)

/-- The overlap retains exactly the original annulus in the full disk coproduct. -/
theorem diskInclusion_preimage_intersection :
    CellFamilyAttachment.diskInclusion X n a ⁻¹' (U X n a ∩ V X n a) = annulus ι n := by
  rw [Set.preimage_inter, diskInclusion_preimage_U_collar, diskInclusion_preimage_V]
  rfl

/-- The overlap has no original-space preimage. -/
theorem inclusion_preimage_intersection :
    CellFamilyAttachment.inclusion X n a ⁻¹' (U X n a ∩ V X n a) = ∅ := by
  rw [Set.preimage_inter, inclusion_preimage_U, inclusion_preimage_V, Set.univ_inter]

/-- The actual image of the original annuli is exactly the open overlap. -/
theorem image_annulus_eq_intersection :
    CellFamilyAttachment.diskInclusion X n a '' annulus ι n = U X n a ∩ V X n a := by
  ext y
  constructor
  · rintro ⟨b, hb, hby⟩
    have hbUV : b ∈ CellFamilyAttachment.diskInclusion X n a ⁻¹' (U X n a ∩ V X n a) := by
      rw [diskInclusion_preimage_intersection]
      exact hb
    change CellFamilyAttachment.diskInclusion X n a b ∈ U X n a ∩ V X n a at hbUV
    rwa [hby] at hbUV
  · rintro ⟨hyU, b, hb, hby⟩
    refine ⟨b, ?_, hby⟩
    rw [← diskInclusion_preimage_intersection X n a]
    change CellFamilyAttachment.diskInclusion X n a b ∈ U X n a ∩ V X n a
    rw [hby]
    exact ⟨hyU, ⟨b, hb, hby⟩⟩

/-- Restricting the actual disk map to the inner image gives a homeomorphism. -/
theorem isHomeomorph_V_diskRestriction :
    IsHomeomorph ((V X n a).restrictPreimage (CellFamilyAttachment.diskInclusion X n a)) :=
  TopCat.isHomeomorph_restrictPreimage_left_image_of_avoids_boundary
    (CellFamilyAttachment.isPushout X n a) (inner_avoids_boundary ι n) (inner_isOpen ι n)

/-- Restricting the actual disk map to the overlap gives the original annular homeomorphism. -/
theorem isHomeomorph_intersection_diskRestriction :
    IsHomeomorph
      ((U X n a ∩ V X n a).restrictPreimage (CellFamilyAttachment.diskInclusion X n a)) := by
  apply TopCat.isHomeomorph_restrictPreimage_inr_of_isPushout
    (CellFamilyAttachment.isPushout X n a).flip
    (isOpen_intersection X n a) (inclusion_preimage_intersection X n a)
  rw [diskInclusion_preimage_intersection X n a]
  exact annulus_avoids_boundary ι n

end AlgebraicTopology.CellCollarCover

end

end
