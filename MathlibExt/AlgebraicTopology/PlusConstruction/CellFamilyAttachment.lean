/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.ClosedBall.Topology
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbedding
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbeddingColimits
public import MathlibExt.Topology.Category.TopCat.PushoutPathConnected
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

/-!
# Actual families of classical cell attachments

For a family of boundary maps into the original space, the literal sigma
coproducts of classical closed disks and their boundaries determine a
pushout. Its second inclusion is the original-space inclusion. The cells
have dimension `n + 1`, so their boundaries are nonempty; `n = 1` gives
the family of 2-cells used in the plus-construction frontier.

The file constructs the attachment presentation, gluing identities and
universal maps. The original-space inclusion is a closed embedding, and
the resulting space is connected whenever the original space is connected.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Topology Topology.CWComplex

universe u

namespace AlgebraicTopology.CellFamilyAttachment

/-- The literal disjoint sum of all positive-dimensional classical cell boundaries. -/
def boundaries (ι : Type u) (n : ℕ) : TopCat.{u} :=
  TopCat.of (Σ _ : ι, (classicalCellDiskPair.{u} (n + 1)).snd)

/-- The literal disjoint sum of the corresponding closed classical disks. -/
def disks (ι : Type u) (n : ℕ) : TopCat.{u} :=
  TopCat.of (Σ _ : ι, (classicalCellDiskPair.{u} (n + 1)).fst)

variable {ι : Type u}

/-- The actual descent of a family of boundary maps from its literal sigma cofan. -/
def boundaryDesc (n : ℕ) {Z : TopCat.{u}}
    (f : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ Z)) :
    boundaries ι n ⟶ Z :=
  (TopCat.sigmaCofanIsColimit.{u, u}
    (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd)).desc (Cofan.mk Z f)

/-- The actual descent of a family of disk maps from its literal sigma cofan. -/
def diskDesc (n : ℕ) {Z : TopCat.{u}}
    (f : ι → ((classicalCellDiskPair.{u} (n + 1)).fst ⟶ Z)) :
    disks ι n ⟶ Z :=
  (TopCat.sigmaCofanIsColimit.{u, u}
    (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst)).desc (Cofan.mk Z f)

theorem boundaryDesc_apply (n : ℕ) {Z : TopCat.{u}}
    (f : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ Z))
    (i : ι) (z : (classicalCellDiskPair.{u} (n + 1)).snd) :
    boundaryDesc n f ⟨i, z⟩ = f i z :=
  rfl

theorem diskDesc_apply (n : ℕ) {Z : TopCat.{u}}
    (f : ι → ((classicalCellDiskPair.{u} (n + 1)).fst ⟶ Z))
    (i : ι) (z : (classicalCellDiskPair.{u} (n + 1)).fst) :
    diskDesc n f ⟨i, z⟩ = f i z :=
  rfl

@[reassoc]
theorem boundaryι_desc (n : ℕ) {Z : TopCat.{u}}
    (f : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ Z)) (i : ι) :
    TopCat.sigmaι (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i ≫
      boundaryDesc n f = f i := by
  apply TopCat.ext
  intro z
  rfl

@[reassoc]
theorem diskι_desc (n : ℕ) {Z : TopCat.{u}}
    (f : ι → ((classicalCellDiskPair.{u} (n + 1)).fst ⟶ Z)) (i : ι) :
    TopCat.sigmaι (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst) i ≫
      diskDesc n f = f i := by
  apply TopCat.ext
  intro z
  rfl

/-- The literal sigma map of the original boundary-to-disk inclusions. -/
def boundaryToDisks (ι : Type u) (n : ℕ) : boundaries ι n ⟶ disks ι n :=
  TopCat.ofHom
    ⟨Sigma.map (id : ι → ι)
        (fun (_ : ι) (z : (classicalCellDiskPair.{u} (n + 1)).snd) =>
          (classicalCellDiskPair.{u} (n + 1)).map z),
      Continuous.sigma_map
        (fun _ => (classicalCellDiskPair.{u} (n + 1)).map.hom.continuous)⟩

theorem boundaryToDisks_apply (n : ℕ) (i : ι)
    (z : (classicalCellDiskPair.{u} (n + 1)).snd) :
    boundaryToDisks ι n ⟨i, z⟩ =
      ⟨i, (classicalCellDiskPair.{u} (n + 1)).map z⟩ :=
  rfl

/-- Every boundary-to-disk map is kept in its original indexed summand. -/
@[reassoc]
theorem boundaryι_boundaryToDisks (n : ℕ) (i : ι) :
    TopCat.sigmaι (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd) i ≫
        boundaryToDisks ι n =
      (classicalCellDiskPair.{u} (n + 1)).map ≫
        TopCat.sigmaι (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst) i := by
  apply TopCat.ext
  intro z
  rfl

/-- The full boundary sigma map is a closed embedding. -/
theorem boundaryToDisks_isClosedEmbedding (ι : Type u) (n : ℕ) :
    IsClosedEmbedding (boundaryToDisks ι n) := by
  change IsClosedEmbedding (Sigma.map (id : ι → ι)
    (fun (_ : ι) (z : (classicalCellDiskPair.{u} (n + 1)).snd) =>
      (classicalCellDiskPair.{u} (n + 1)).map z) :
    (Σ _ : ι, (classicalCellDiskPair.{u} (n + 1)).snd) →
      (Σ _ : ι, (classicalCellDiskPair.{u} (n + 1)).fst))
  exact Topology.IsClosedEmbedding.sigmaMap
    (f := fun (_ : ι) (z : (classicalCellDiskPair.{u} (n + 1)).snd) =>
      (classicalCellDiskPair.{u} (n + 1)).map z)
    (fun _ => isClosedEmbedding_classicalCellDiskPair_map (n := n + 1))

variable (X : TopCat.{u}) (n : ℕ)
variable (a : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X))

/-- All actual attaching maps, descended from the literal boundary coproduct. -/
def attachingMap : boundaries ι n ⟶ X :=
  boundaryDesc n a

theorem attachingMap_apply (i : ι) (z : (classicalCellDiskPair.{u} (n + 1)).snd) :
    attachingMap X n a ⟨i, z⟩ = a i z :=
  rfl

/-- The computed attachment space; the original space is the second pushout input. -/
def space : TopCat.{u} :=
  pushout (boundaryToDisks ι n) (attachingMap X n a)

/-- The actual inclusion of the whole original space. -/
def inclusion : X ⟶ space X n a :=
  pushout.inr (boundaryToDisks ι n) (attachingMap X n a)

/-- The actual map from the complete disk coproduct into the attachment. -/
def diskInclusion : disks ι n ⟶ space X n a :=
  pushout.inl (boundaryToDisks ι n) (attachingMap X n a)

/-- The actual characteristic map of an indexed attached disk. -/
def cell (i : ι) : (classicalCellDiskPair.{u} (n + 1)).fst ⟶ space X n a :=
  TopCat.sigmaι (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst) i ≫
    diskInclusion X n a

/-- The computed maps form the canonical pushout square. -/
theorem isPushout :
    IsPushout (boundaryToDisks ι n) (attachingMap X n a)
      (diskInclusion X n a) (inclusion X n a) :=
  IsPushout.of_hasPushout _ _

/-- Every original attaching boundary is glued to its actual characteristic disk. -/
@[reassoc]
theorem boundary_gluing (i : ι) :
    a i ≫ inclusion X n a = (classicalCellDiskPair.{u} (n + 1)).map ≫ cell X n a i := by
  apply TopCat.ext
  intro z
  exact (ConcreteCategory.congr_hom (isPushout X n a).w ⟨i, z⟩).symm

/-- The complete attachment presentation is constructed from the computed pushout. -/
def attachCells : HomotopicalAlgebra.AttachCells.{u}
    (fun _ : Unit => (classicalCellDiskPair.{u} (n + 1)).map) (inclusion X n a) where
  ι := ι
  π _ := Unit.unit
  cofan₁ := TopCat.sigmaCofan.{u, u}
    (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).snd)
  cofan₂ := TopCat.sigmaCofan.{u, u}
    (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst)
  isColimit₁ := TopCat.sigmaCofanIsColimit.{u, u} _
  isColimit₂ := TopCat.sigmaCofanIsColimit.{u, u} _
  m := boundaryToDisks ι n
  hm i := boundaryι_boundaryToDisks n i
  g₁ := attachingMap X n a
  g₂ := diskInclusion X n a
  isPushout := (isPushout X n a).flip

/-- The presentation's cell map is the original indexed characteristic map. -/
theorem attachCells_cell (i : ι) : (attachCells X n a).cell i = cell X n a i :=
  rfl

/-- The whole original space is included as a closed subspace of the actual attachment. -/
theorem inclusion_isClosedEmbedding : IsClosedEmbedding (inclusion X n a) :=
  TopCat.isClosedEmbedding_of_isPushout (isPushout X n a)
    (boundaryToDisks_isClosedEmbedding ι n)

theorem inclusion_injective : Function.Injective (inclusion X n a) :=
  (inclusion_isClosedEmbedding X n a).injective

/-- Compatible maps on the original space and every actual disk descend to the attachment. -/
def desc {Z : TopCat.{u}} (f : X ⟶ Z)
    (g : ι → ((classicalCellDiskPair.{u} (n + 1)).fst ⟶ Z))
    (h : ∀ i, (classicalCellDiskPair.{u} (n + 1)).map ≫ g i = a i ≫ f) :
    space X n a ⟶ Z :=
  pushout.desc (diskDesc n g) f (by
    apply TopCat.ext
    rintro ⟨i, z⟩
    exact ConcreteCategory.congr_hom (h i) z)

@[reassoc]
theorem inclusion_desc {Z : TopCat.{u}} (f : X ⟶ Z)
    (g : ι → ((classicalCellDiskPair.{u} (n + 1)).fst ⟶ Z))
    (h : ∀ i, (classicalCellDiskPair.{u} (n + 1)).map ≫ g i = a i ≫ f) :
    inclusion X n a ≫ desc X n a f g h = f :=
  pushout.inr_desc _ _ _

@[reassoc]
theorem cell_desc {Z : TopCat.{u}} (f : X ⟶ Z)
    (g : ι → ((classicalCellDiskPair.{u} (n + 1)).fst ⟶ Z))
    (h : ∀ i, (classicalCellDiskPair.{u} (n + 1)).map ≫ g i = a i ≫ f) (i : ι) :
    cell X n a i ≫ desc X n a f g h = g i := by
  apply TopCat.ext
  intro z
  have hLeft : diskInclusion X n a ≫ desc X n a f g h = diskDesc n g :=
    pushout.inl_desc _ _ _
  have hValue := ConcreteCategory.congr_hom hLeft
    (⟨i, z⟩ : disks ι n)
  change desc X n a f g h (diskInclusion X n a (⟨i, z⟩ : disks ι n)) =
    diskDesc n g (⟨i, z⟩ : disks ι n) at hValue
  change desc X n a f g h (diskInclusion X n a (⟨i, z⟩ : disks ι n)) = g i z
  exact hValue.trans (diskDesc_apply n g i z)

/-- Maps from the attachment are determined by the original space and every attached disk. -/
theorem hom_ext {Z : TopCat.{u}} {f g : space X n a ⟶ Z}
    (hX : inclusion X n a ≫ f = inclusion X n a ≫ g)
    (hCells : ∀ i, cell X n a i ≫ f = cell X n a i ≫ g) : f = g := by
  apply HomotopicalAlgebra.AttachCells.hom_ext (attachCells X n a) hX
  intro i
  exact hCells i

/-- Every point of the computed attachment comes from the original space or an actual cell. -/
theorem exists_inclusion_or_cell (z : space X n a) :
    (∃ x : X, inclusion X n a x = z) ∨
      ∃ (i : ι) (d : (classicalCellDiskPair.{u} (n + 1)).fst), cell X n a i d = z := by
  rcases Types.eq_or_eq_of_isPushout ((isPushout X n a).map (forget TopCat)) z with
    ⟨d, hd⟩ | ⟨x, hx⟩
  · obtain ⟨i, d⟩ := d
    change diskInclusion X n a ⟨i, d⟩ = z at hd
    exact Or.inr ⟨i, d, hd⟩
  · change inclusion X n a x = z at hx
    exact Or.inl ⟨x, hx⟩

/-- The original-space image and all characteristic disk images cover the entire attachment. -/
theorem range_inclusion_union_iUnion_range_cell :
    Set.range (inclusion X n a) ∪ ⋃ i : ι, Set.range (cell X n a i) = Set.univ := by
  ext z
  constructor
  · intro _
    exact Set.mem_univ _
  · intro _
    rcases exists_inclusion_or_cell X n a z with ⟨x, hx⟩ | ⟨i, d, hd⟩
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨d, hd⟩⟩)

/-- Positive-dimensional cell attachments preserve connectedness, including an empty family. -/
theorem connectedSpace [ConnectedSpace X] : ConnectedSpace (space X n a) := by
  let R : Set (space X n a) := Set.range (inclusion X n a)
  let C : ι → Set (space X n a) := fun i => Set.range (cell X n a i)
  have hR : IsConnected R := isConnected_range (inclusion X n a).hom.continuous
  have hC : ∀ i, IsConnected (C i) := fun i =>
    isConnected_range (cell X n a i).hom.continuous
  have hMeet : ∀ i, (R ∩ C i).Nonempty := by
    intro i
    obtain ⟨z⟩ :=
      (inferInstance : Nonempty (classicalCellDiskPair.{u} (n + 1)).snd)
    refine ⟨inclusion X n a (a i z), ⟨⟨a i z, rfl⟩, ?_⟩⟩
    exact ⟨(classicalCellDiskPair.{u} (n + 1)).map z,
      (ConcreteCategory.congr_hom (boundary_gluing X n a i) z).symm⟩
  let E : Option ι → Set (space X n a) := fun o =>
    match o with
    | none => R
    | some i => R ∪ C i
  have hE : ∀ o, IsConnected (E o) := by
    intro o
    cases o with
    | none => exact hR
    | some i => exact IsConnected.union (hMeet i) hR (hC i)
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  have hCommon : (⋂ o, E o).Nonempty := by
    refine ⟨inclusion X n a x₀, ?_⟩
    rw [Set.mem_iInter]
    intro o
    cases o with
    | none => exact ⟨x₀, rfl⟩
    | some i => exact Or.inl ⟨x₀, rfl⟩
  have hUnion : (⋃ o, E o) = Set.univ := by
    ext z
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      rcases exists_inclusion_or_cell X n a z with ⟨x, hx⟩ | ⟨i, d, hd⟩
      · exact Set.mem_iUnion.mpr ⟨none, ⟨x, hx⟩⟩
      · exact Set.mem_iUnion.mpr ⟨some i, Or.inr ⟨d, hd⟩⟩
  apply connectedSpace_iff_univ.mpr
  refine ⟨⟨inclusion X n a x₀, Set.mem_univ _⟩, ?_⟩
  rw [← hUnion]
  exact isPreconnected_iUnion hCommon (fun o => (hE o).isPreconnected)

/-- Paths in the original source and in each actual positive-dimensional
disk connect the whole computed attachment. -/
theorem pathConnectedSpace [PathConnectedSpace X] : PathConnectedSpace (space X n a) := by
  apply TopCat.pathConnectedSpace_pushout_of_joined_to_boundary
    (boundaryToDisks ι n) (attachingMap X n a)
  rintro ⟨i, d⟩
  obtain ⟨z⟩ :=
    (inferInstance : Nonempty (classicalCellDiskPair.{u} (n + 1)).snd)
  refine ⟨⟨i, z⟩, ?_⟩
  have h : Joined d ((classicalCellDiskPair.{u} (n + 1)).map z) :=
    PathConnectedSpace.joined _ _
  exact h.map (TopCat.sigmaι
    (fun _ : ι => (classicalCellDiskPair.{u} (n + 1)).fst) i).hom.continuous

end AlgebraicTopology.CellFamilyAttachment

end

end
