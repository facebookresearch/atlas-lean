/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.ClassicalCellAttachments
public import MathlibExt.Topology.Category.TopPair.Triple

/-!
# The skeletal filtration of an actual CW pair

For a subcomplex `A` of the given classical CW space `X`, the strict relative
stage `n` is the literal subcomplex `A ∪ X^{n-1}`. Its initial stage is `A`.
The new cells are the original `n`-cells outside `A`; their characteristic
maps and attaching spheres retain their values in the original space.

All inclusions below are actual subspace embeddings. No CW structure on a
quotient, spectral object, or cohomology comparison is an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace Topology.CWComplex

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
variable (A : Subcomplex (Set.univ : Set X))

/-- The original cells that are not cells of the given subcomplex. -/
abbrev relativeCells (n : ℕ) := {j : cell (Set.univ : Set X) n // j ∉ A.I n}

/-- The actual union of the subcomplex and a strict original skeleton,
including the empty and infinite skeleton indices. -/
def relativeSkeleton (n : ℕ∞) : Subcomplex (Set.univ : Set X) where
  carrier := (A : Set X) ∪ (skeletonLT (Set.univ : Set X) n : Set X)
  I m := A.I m ∪ {j | (m : ℕ∞) < n}
  closed' := A.closed.union (skeletonLT (Set.univ : Set X) n).closed
  union' := by
    rw [Set.empty_union]
    ext x
    have hA : x ∈ (A : Set X) ↔
        ∃ (m : ℕ) (j : cell (Set.univ : Set X) m), j ∈ A.I m ∧ x ∈ openCell m j := by
      rw [← CWComplex.Subcomplex.union (E := A)]
      simp only [Set.mem_iUnion, Subtype.exists, exists_prop]
    have hS : x ∈ (skeletonLT (Set.univ : Set X) n : Set X) ↔
        ∃ (m : ℕ) (_ : (m : ℕ∞) < n) (j : cell (Set.univ : Set X) m),
          x ∈ openCell m j := mem_skeletonLT_iff
    simp only [Set.mem_iUnion, Subtype.exists, exists_prop, Set.mem_union, Set.mem_setOf_eq]
    rw [hA, hS]
    constructor
    · rintro ⟨m, j, hj, hx⟩
      rcases hj with hj | hj
      · exact Or.inl ⟨m, j, hj, hx⟩
      · exact Or.inr ⟨m, hj, j, hx⟩
    · rintro (⟨m, j, hj, hx⟩ | ⟨m, hm, j, hx⟩)
      · exact ⟨m, j, Or.inl hj, hx⟩
      · exact ⟨m, j, Or.inr hm, hx⟩

/-- The carrier is the union in the original CW space. -/
@[simp]
theorem coe_relativeSkeleton (n : ℕ∞) :
    (relativeSkeleton X A n : Set X) =
      (A : Set X) ∪ (skeletonLT (Set.univ : Set X) n : Set X) := rfl

/-- Stage zero retains the complete subcomplex. -/
theorem coe_relativeSkeleton_zero : (relativeSkeleton X A 0 : Set X) = A := by
  rw [coe_relativeSkeleton, skeletonLT_zero_eq_empty, Set.union_empty]

/-- The infinite stage is the original entire space. -/
theorem coe_relativeSkeleton_top :
    (relativeSkeleton X A ⊤ : Set X) = Set.univ := by
  rw [coe_relativeSkeleton, skeletonLT_top, Set.union_univ]

/-- The cell indices of a relative stage are the original cells of `A`
and all original cells below its strict dimension. -/
@[simp]
theorem relativeSkeleton_I (n : ℕ∞) (m : ℕ) :
    (relativeSkeleton X A n).I m = A.I m ∪ {j | (m : ℕ∞) < n} := rfl

/-- Every relative stage contains the given subcomplex. -/
theorem subcomplex_subset_relativeSkeleton (n : ℕ∞) :
    (A : Set X) ⊆ relativeSkeleton X A n := Set.subset_union_left

/-- Every relative stage contains the corresponding original skeleton. -/
theorem skeleton_subset_relativeSkeleton (n : ℕ∞) :
    (skeletonLT (Set.univ : Set X) n : Set X) ⊆ relativeSkeleton X A n :=
  Set.subset_union_right

/-- Inclusion between any two ordered relative stages. -/
theorem relativeSkeleton_mono {n m : ℕ∞} (h : n ≤ m) :
    (relativeSkeleton X A n : Set X) ⊆ relativeSkeleton X A m :=
  Set.union_subset_union_right _ (skeletonLT_mono h)

/-- The relative skeletal carriers form a monotone family of actual subspaces. -/
theorem relativeSkeleton_monotone :
    Monotone (fun n : ℕ∞ => (relativeSkeleton X A n : Set X)) :=
  fun _ _ h => relativeSkeleton_mono X A h

/-- An original cell outside `A` and not yet attached is disjoint from
the complete relative stage. -/
theorem disjoint_relativeSkeleton_openCell {n : ℕ∞} {m : ℕ}
    (j : relativeCells X A m) (hnm : n ≤ m) :
    Disjoint (relativeSkeleton X A n : Set X) (openCell m j.val) := by
  rw [coe_relativeSkeleton, Set.disjoint_union_left]
  exact ⟨(A.disjoint_openCell_subcomplex_of_notMem j.property).symm,
    disjoint_skeletonLT_openCell hnm⟩

/-- A closed cell in `A` is already present at every relative stage. -/
theorem closedCell_subset_relativeSkeleton_of_mem (n : ℕ∞) (m : ℕ)
    (j : cell (Set.univ : Set X) m) (hj : j ∈ A.I m) :
    closedCell m j ⊆ relativeSkeleton X A n :=
  (A.closedCell_subset_of_mem hj).trans (subcomplex_subset_relativeSkeleton X A n)

/-- Attaching one relative dimension adds precisely the characteristic
closed cells outside the original subcomplex. -/
theorem relativeSkeleton_union_iUnion_closedCell_eq_succ (n : ℕ) :
    (relativeSkeleton X A n : Set X) ∪
        ⋃ j : relativeCells X A n, closedCell n j.val =
      relativeSkeleton X A ((n + 1 : ℕ) : ℕ∞) := by
  have hall : (relativeSkeleton X A n : Set X) ∪
      ⋃ j : cell (Set.univ : Set X) n, closedCell n j =
      relativeSkeleton X A ((n + 1 : ℕ) : ℕ∞) := by
    simp only [coe_relativeSkeleton, Nat.cast_add, Nat.cast_one]
    rw [Set.union_assoc, skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ]
  rw [← hall]
  apply Set.Subset.antisymm
  · exact Set.union_subset_union_right _
      (Set.iUnion_subset fun j => Set.subset_iUnion _ j.val)
  · apply Set.union_subset Set.subset_union_left
    apply Set.iUnion_subset
    intro j
    by_cases hj : j ∈ A.I n
    · exact (closedCell_subset_relativeSkeleton_of_mem X A n n j hj).trans
        Set.subset_union_left
    · exact Set.subset_union_of_subset_right
        (Set.subset_iUnion (fun i : relativeCells X A n => closedCell n i.val)
          (⟨j, hj⟩ : relativeCells X A n)) _

/-- The finite relative stages cover the original CW space. -/
theorem iUnion_relativeSkeleton :
    (⋃ n : ℕ, (relativeSkeleton X A n : Set X)) = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  calc
    Set.univ = ⋃ n : ℕ, (skeletonLT (Set.univ : Set X) n : Set X) :=
      (iUnion_skeletonLT_eq_complex (C := (Set.univ : Set X))).symm
    _ ⊆ ⋃ n : ℕ, (relativeSkeleton X A n : Set X) :=
      Set.iUnion_mono fun n => skeleton_subset_relativeSkeleton X A n

/-- The strict relative stage as a literal topological subspace of `X`. -/
abbrev relativeSkeletonTop (n : ℕ) : TopCat.{u} :=
  TopCat.of (relativeSkeleton X A n : Set X)

/-- The original ambient inclusion of a relative stage. -/
def relativeSkeletonInclusion (n : ℕ) : relativeSkeletonTop X A n ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Relative stages are closed subspaces of the original Hausdorff CW space. -/
theorem isClosedEmbedding_relativeSkeletonInclusion (n : ℕ) :
    IsClosedEmbedding (relativeSkeletonInclusion X A n) :=
  IsClosedEmbedding.subtypeVal (relativeSkeleton X A n).closed

/-- The inclusion of two ordered relative stages. -/
def relativeSkeletonMapOfLE (n m : ℕ) (h : n ≤ m) :
    relativeSkeletonTop X A n ⟶ relativeSkeletonTop X A m :=
  TopCat.ofHom
    ⟨Set.inclusion (relativeSkeleton_mono X A (by exact_mod_cast h)),
      continuous_subtype_val.subtype_mk _⟩

/-- The successor inclusion is an actual relative stage inclusion. -/
abbrev relativeSkeletonTransition (n : ℕ) :
    relativeSkeletonTop X A n ⟶ relativeSkeletonTop X A (n + 1) :=
  relativeSkeletonMapOfLE X A n (n + 1) (Nat.le_succ n)

@[simp]
theorem relativeSkeletonMapOfLE_comp_inclusion (n m : ℕ) (h : n ≤ m) :
    relativeSkeletonMapOfLE X A n m h ≫ relativeSkeletonInclusion X A m =
      relativeSkeletonInclusion X A n := rfl

@[simp]
theorem relativeSkeletonMapOfLE_comp (n m k : ℕ) (h : n ≤ m) (h' : m ≤ k) :
    relativeSkeletonMapOfLE X A n m h ≫ relativeSkeletonMapOfLE X A m k h' =
      relativeSkeletonMapOfLE X A n k (h.trans h') := rfl

/-- Every relative stage inclusion remains a closed embedding. -/
theorem isClosedEmbedding_relativeSkeletonMapOfLE (n m : ℕ) (h : n ≤ m) :
    IsClosedEmbedding (relativeSkeletonMapOfLE X A n m h) :=
  IsClosedEmbedding.of_comp
    (isClosedEmbedding_relativeSkeletonInclusion X A m).isEmbedding
    (show IsClosedEmbedding
      ((relativeSkeletonInclusion X A m) ∘ (relativeSkeletonMapOfLE X A n m h)) from
        isClosedEmbedding_relativeSkeletonInclusion X A n)

/-- The actual pair of two ordered relative stages. -/
def relativeSkeletonPairOfLE (n m : ℕ) (h : n ≤ m) : TopPair.{u} :=
  TopPair.of (relativeSkeletonMapOfLE X A n m h)
    (isClosedEmbedding_relativeSkeletonMapOfLE X A n m h).isEmbedding

/-- The actual successive relative skeletal pair. -/
abbrev relativeSkeletalPair (n : ℕ) : TopPair.{u} :=
  relativeSkeletonPairOfLE X A n (n + 1) (Nat.le_succ n)

/-- The original inclusion of `A` into a relative stage. -/
def subcomplexToRelativeSkeleton (n : ℕ) :
    TopCat.of (A : Set X) ⟶ relativeSkeletonTop X A n :=
  TopCat.ofHom
    ⟨Set.inclusion (subcomplex_subset_relativeSkeleton X A n),
      continuous_subtype_val.subtype_mk _⟩

/-- The complete original CW pair, with the given inclusion of `A`. -/
def originalCWPair : TopPair.{u} :=
  TopPair.of (subcomplexInclusion A) (isClosedEmbedding_subcomplexInclusion A).isEmbedding

/-- The relative skeletal endpoint pair `(A ∪ X^{n-1}, A)`. -/
def relativeStagePair (n : ℕ) : TopPair.{u} :=
  TopPair.of (subcomplexToRelativeSkeleton X A n)
    (IsEmbedding.of_comp (subcomplexToRelativeSkeleton X A n).hom.continuous
      (relativeSkeletonInclusion X A n).hom.continuous
      (show IsEmbedding
        ((relativeSkeletonInclusion X A n) ∘ (subcomplexToRelativeSkeleton X A n)) from
          (isClosedEmbedding_subcomplexInclusion A).isEmbedding))

/-- The actual restriction pair map from a relative stage to the original pair. -/
def relativeStagePairToOriginal (n : ℕ) :
    relativeStagePair X A n ⟶ originalCWPair X A :=
  TopPair.ofHom (relativeSkeletonInclusion X A n) (𝟙 _) (by
    apply TopCat.ext
    intro x
    rfl)

/-- The canonical pair map along two ordered relative stages fixes `A` pointwise. -/
def relativeStagePairMapOfLE (n m : ℕ) (h : n ≤ m) :
    relativeStagePair X A n ⟶ relativeStagePair X A m :=
  TopPair.ofHom (relativeSkeletonMapOfLE X A n m h) (𝟙 _) (by
    apply TopCat.ext
    intro x
    rfl)

/-- The successive stages with the original base form a literal topological triple. -/
def relativeSkeletalTriple (n : ℕ) : AlgebraicTopology.TopTriple.{u} :=
  ⟨CategoryTheory.ComposableArrows.mk₂ (subcomplexToRelativeSkeleton X A n)
      (relativeSkeletonTransition X A n),
    ⟨(relativeStagePair X A n).isEmbedding_map,
      (isClosedEmbedding_relativeSkeletonMapOfLE X A n (n + 1) (Nat.le_succ n)).isEmbedding⟩⟩

/-- Relative characteristic disks are the original characteristic disks
corestricted to the actual successor relative stage. -/
def characteristicRelativeDiskToSkeleton (n : ℕ) (j : relativeCells X A n) :
    (classicalCellDiskPair.{u} n).fst ⟶ relativeSkeletonTop X A (n + 1) :=
  characteristicDiskToSkeleton n j.val ≫
    TopCat.ofHom
      ⟨Set.inclusion (skeleton_subset_relativeSkeleton X A ((n + 1 : ℕ) : ℕ∞)),
        continuous_subtype_val.subtype_mk _⟩

/-- The attaching sphere retains its original characteristic map and lands
in the complete preceding relative stage. -/
def characteristicRelativeSphereToSkeleton (n : ℕ) (j : relativeCells X A n) :
    (classicalCellDiskPair.{u} n).snd ⟶ relativeSkeletonTop X A n :=
  characteristicSphereToSkeleton n j.val ≫
    TopCat.ofHom
      ⟨Set.inclusion (skeleton_subset_relativeSkeleton X A n),
        continuous_subtype_val.subtype_mk _⟩

/-- The relative attachment square consists of the original characteristic values. -/
theorem characteristic_relative_attachment_square (n : ℕ) (j : relativeCells X A n) :
    characteristicRelativeSphereToSkeleton X A n j ≫ relativeSkeletonTransition X A n =
      (classicalCellDiskPair.{u} n).map ≫ characteristicRelativeDiskToSkeleton X A n j := rfl

/-- The actual original characteristic disk map is retained after ambient inclusion. -/
@[simp]
theorem characteristicRelativeDiskToSkeleton_comp_inclusion
    (n : ℕ) (j : relativeCells X A n) :
    characteristicRelativeDiskToSkeleton X A n j ≫ relativeSkeletonInclusion X A (n + 1) =
      characteristicDiskMap n j.val := rfl

/-- The original characteristic disk and sphere constitute the relative cell pair map. -/
def characteristicRelativeCellPairMap (n : ℕ) (j : relativeCells X A n) :
    classicalCellDiskPair.{u} n ⟶ relativeSkeletalPair X A n :=
  TopPair.ofHom (characteristicRelativeDiskToSkeleton X A n j)
    (characteristicRelativeSphereToSkeleton X A n j)
    (characteristic_relative_attachment_square X A n j)

end Topology.CWComplex

end
