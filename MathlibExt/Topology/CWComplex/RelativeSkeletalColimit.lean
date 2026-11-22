/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.RelativeCellAttachments

/-!
# The actual CW pair as its relative skeletal colimit

The relative skeletal sequence begins with the given subcomplex and has
the original space as its colimit. Its transitions and cocone maps are
literal inclusions. The colimit proof descends each compatible family
through the proved original-space relative dimension quotient.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace Topology.CWComplex

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
variable (A : Subcomplex (Set.univ : Set X))

/-- The actual increasing relative skeletal sequence. -/
def relativeSkeletalDiagram : ℕ ⥤ TopCat.{u} where
  obj n := relativeSkeletonTop X A n
  map f := relativeSkeletonMapOfLE X A _ _ (leOfHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem relativeSkeletalDiagram_obj (n : ℕ) :
    (relativeSkeletalDiagram X A).obj n = relativeSkeletonTop X A n := rfl

@[simp]
theorem relativeSkeletalDiagram_map (n m : ℕ) (h : n ≤ m) :
    (relativeSkeletalDiagram X A).map (homOfLE h) = relativeSkeletonMapOfLE X A n m h := rfl

theorem relativeSkeletalDiagram_map_succ (n : ℕ) :
    (relativeSkeletalDiagram X A).map (homOfLE (Nat.le_succ n)) =
      relativeSkeletonTransition X A n := rfl

/-- The actual inclusion cocone has the original ambient CW space as its point. -/
def relativeSkeletalCocone : Cocone (relativeSkeletalDiagram X A) where
  pt := X
  ι :=
    { app := relativeSkeletonInclusion X A
      naturality _ _ _ := rfl }

@[simp]
theorem relativeSkeletalCocone_pt : (relativeSkeletalCocone X A).pt = X := rfl

@[simp]
theorem relativeSkeletalCocone_ι_app (n : ℕ) :
    (relativeSkeletalCocone X A).ι.app n = relativeSkeletonInclusion X A n := rfl

/-- A cocone on the relative stages is a continuous family on their actual dimension union. -/
def relativeSkeletalCoconeFamily (c : Cocone (relativeSkeletalDiagram X A)) :
    C(RelativeSkeletalUnion X A, c.pt) :=
  ⟨fun z => c.ι.app z.1 z.2, continuous_sigma fun n => (c.ι.app n).hom.continuous⟩

/-- The cocone equations identify every two stage representatives of the same original point. -/
theorem relativeSkeletalCoconeFamily_factors (c : Cocone (relativeSkeletalDiagram X A)) :
    Function.FactorsThrough (relativeSkeletalCoconeFamily X A c)
      (relativeSkeletalUnionQuotient X A) := by
  rintro ⟨n, x⟩ ⟨m, y⟩ hxy
  let k := max n m
  have hx := ConcreteCategory.congr_hom (c.w (homOfLE (Nat.le_max_left n m))) x
  have hy := ConcreteCategory.congr_hom (c.w (homOfLE (Nat.le_max_right n m))) y
  have hz : relativeSkeletonMapOfLE X A n k (Nat.le_max_left n m) x =
      relativeSkeletonMapOfLE X A m k (Nat.le_max_right n m) y := Subtype.ext hxy
  exact hx.symm.trans ((congrArg (c.ι.app k) hz).trans hy)

/-- Descend a compatible relative family to the original ambient CW space. -/
def relativeSkeletalCoconeDesc (c : Cocone (relativeSkeletalDiagram X A)) : X ⟶ c.pt :=
  TopCat.ofHom ((isQuotientMap_relativeSkeletalUnionQuotient X A).lift
    (relativeSkeletalCoconeFamily X A c) (relativeSkeletalCoconeFamily_factors X A c))

/-- The descended map retains each original relative stage map. -/
@[reassoc (attr := simp)]
theorem relativeSkeletalInclusion_comp_coconeDesc
    (c : Cocone (relativeSkeletalDiagram X A)) (n : ℕ) :
    relativeSkeletonInclusion X A n ≫ relativeSkeletalCoconeDesc X A c = c.ι.app n := by
  apply TopCat.ext
  intro x
  exact DFunLike.congr_fun ((isQuotientMap_relativeSkeletalUnionQuotient X A).lift_comp
    (relativeSkeletalCoconeFamily X A c) (relativeSkeletalCoconeFamily_factors X A c)) ⟨n, x⟩

/-- The actual relative skeletal inclusion cocone is a colimit. -/
def relativeSkeletalCoconeIsColimit : IsColimit (relativeSkeletalCocone X A) where
  desc := relativeSkeletalCoconeDesc X A
  fac := relativeSkeletalInclusion_comp_coconeDesc X A
  uniq c f hf := by
    apply TopCat.ext
    intro x
    obtain ⟨⟨n, y⟩, hxy⟩ := (isQuotientMap_relativeSkeletalUnionQuotient X A).surjective x
    change relativeSkeletonInclusion X A n y = x at hxy
    rw [← hxy]
    exact (ConcreteCategory.congr_hom (hf n) y).trans
      (ConcreteCategory.congr_hom (relativeSkeletalInclusion_comp_coconeDesc X A c n) y).symm

/-- Every actual relative skeletal successor is a closed embedding. -/
theorem relativeSkeletalDiagram_successor_closedEmbedding (n : ℕ) :
    IsClosedEmbedding ((relativeSkeletalDiagram X A).map (homOfLE (Nat.le_succ n))) :=
  isClosedEmbedding_relativeSkeletonMapOfLE X A n (n + 1) (Nat.le_succ n)


end Topology.CWComplex

end
