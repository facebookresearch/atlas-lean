/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingCube

/-!
# The actual coherent composition face

The original union composition identifies the product of the two
coherent Hom objects with the actual subcomplex of path chains containing
the supplied middle vertex in every scalar vertex. Splitting uses actual
interval intersections and retains all original endpoints, including
coincident endpoints. No composition/fibre outcome is supplied.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.CompositionFace
variable {J : Type u} [LinearOrder J] (i j k : J)

private instance (a b : SimplicialThickening.Path i k) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The actual coherent Hom subcomplex whose whole original path chain contains the middle
vertex. -/
def positive : (nerve (SimplicialThickening.Path i k)).Subcomplex where
  obj q := {p | ∀ t, j ∈ (p.obj t).I}
  map f p hp := by
    intro t
    exact hp (f.unop.toOrderHom t)

variable {i j k}

/-- The actual left interval restriction of an original path through the supplied middle vertex. -/
def leftPath (p : SimplicialThickening.Path i k) (hp : j ∈ p.I) :
  SimplicialThickening.Path i j where
  I := p.I ∩ Set.Iic j
  left := ⟨p.left, p.left_le j hp⟩
  right := ⟨hp, le_rfl⟩
  left_le t ht := p.left_le t ht.1
  le_right _ ht := ht.2

/-- The actual right interval restriction of the same original path and middle-vertex datum. -/
def rightPath (p : SimplicialThickening.Path i k) (hp : j ∈ p.I) :
  SimplicialThickening.Path j k where
  I := p.I ∩ Set.Ici j
  left := ⟨hp, le_rfl⟩
  right := ⟨p.right, p.le_right j hp⟩
  left_le _ ht := ht.2
  le_right t ht := p.le_right t ht.1

/-- The original left restriction of a union of composable paths is exactly its supplied
left path. -/
theorem left_union (p : SimplicialThickening.Path i j) (q : SimplicialThickening.Path j k) :
    leftPath ((SimplicialThickening.compFunctor (.mk i) (.mk j) (.mk k)).obj (p, q))
      (Or.inl p.right) = p := by
  apply SimplicialThickening.Path.ext
  ext t
  constructor
  · rintro ⟨ht | ht, hj⟩
    · exact ht
    · have h : t = j := le_antisymm hj (q.left_le t ht)
      simpa only [h] using p.right
  · intro ht
    exact ⟨Or.inl ht, p.le_right t ht⟩

/-- The same original union restricts on the right to exactly its supplied right path. -/
theorem right_union (p : SimplicialThickening.Path i j) (q : SimplicialThickening.Path j k) :
    rightPath ((SimplicialThickening.compFunctor (.mk i) (.mk j) (.mk k)).obj (p, q))
      (Or.inl p.right) = q := by
  apply SimplicialThickening.Path.ext
  ext t
  constructor
  · rintro ⟨ht | ht, hj⟩
    · have h : t = j := le_antisymm (p.le_right t ht) hj
      simpa only [h] using q.left
    · exact ht
  · intro ht
    exact ⟨Or.inr ht, q.left_le t ht⟩

/-- Gluing the two actual interval restrictions recovers the whole original path. -/
theorem union_split (p : SimplicialThickening.Path i k) (hp : j ∈ p.I) :
    (SimplicialThickening.compFunctor (.mk i) (.mk j) (.mk k)).obj (leftPath p hp,
      rightPath p hp) = p := by
  apply SimplicialThickening.Path.ext
  ext t
  constructor
  · rintro (⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht
  · intro ht
    obtain hj | hj := le_total t j
    · exact Or.inl ⟨ht, hj⟩
    · exact Or.inr ⟨ht, hj⟩

variable (i j k)

/-- The actual left original Hom chain obtained by interval restriction in every scalar
vertex and arrow. -/
def leftChain {q : SimplexCategoryᵒᵖ} (p : (positive i j k : SSet.{u}).obj q) :
    (nerve (SimplicialThickening.Path i j)).obj q where
  obj t := leftPath (p.val.obj t) (p.property t)
  map f := ⟨homOfLE (fun t ht => ⟨(p.val.map f).hom.down.down ht.1, ht.2⟩)⟩

/-- The actual right original Hom chain from the same complete middle-vertex path data. -/
def rightChain {q : SimplexCategoryᵒᵖ} (p : (positive i j k : SSet.{u}).obj q) :
    (nerve (SimplicialThickening.Path j k)).obj q where
  obj t := rightPath (p.val.obj t) (p.property t)
  map f := ⟨homOfLE (fun t ht => ⟨(p.val.map f).hom.down.down ht.1, ht.2⟩)⟩

/-- The actual original enriched union composition, with no replacement of its whole Hom maps. -/
def composition : nerve (SimplicialThickening.Path i j) ⊗ nerve (SimplicialThickening.Path j k) ⟶
    nerve (SimplicialThickening.Path i k) :=
  eComp SSet.{u} (C := SimplicialThickening J) (.mk i) (.mk j) (.mk k)

/-- The actual union composition has values in the whole original middle-vertex face. -/
def glue : nerve (SimplicialThickening.Path i j) ⊗ nerve (SimplicialThickening.Path j k)
  ⟶ positive i j k where
  app q := ↾fun p => ⟨(composition i j k).app q p, fun t => Or.inl (p.1.obj t).right⟩
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact congr($((composition i j k).naturality f) p)

/-- Split the same actual coherent composition face into its original left and right whole
Hom chains. -/
def split : (positive i j k : SSet.{u}) ⟶
    nerve (SimplicialThickening.Path i j) ⊗ nerve (SimplicialThickening.Path j k) where
  app q := ↾fun p => (leftChain i j k p, rightChain i j k p)
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
      intro x y g
      exact Subsingleton.elim _ _
    · refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
      intro x y g
      exact Subsingleton.elim _ _

/-- The genuine whole Hom product/composition-face isomorphism, retaining the original
scalar paths and endpoints. -/
def positiveIso : nerve (SimplicialThickening.Path i j) ⊗ nerve (SimplicialThickening.Path
  j k) ≅ positive i j k where
  hom := glue i j k
  inv := split i j k
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · refine CategoryTheory.Functor.ext (fun t => left_union (p.1.obj t) (p.2.obj t)) ?_
      intro x y g
      exact Subsingleton.elim _ _
    · refine CategoryTheory.Functor.ext (fun t => right_union (p.1.obj t) (p.2.obj t)) ?_
      intro x y g
      exact Subsingleton.elim _ _
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => union_split (p.val.obj t) (p.property t)) ?_
    intro x y g
    exact Subsingleton.elim _ _

/-- The forward comparison followed by the actual face inclusion is the original whole
enriched composition. -/
theorem positiveIso_composition : (positiveIso i j k).hom ≫ (positive i j k).ι =
  composition i j k := rfl

end CategoryTheory.CoherentRealization.CompositionFace
