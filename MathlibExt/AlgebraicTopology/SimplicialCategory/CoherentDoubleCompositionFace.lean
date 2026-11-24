/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCompositionFace

/-!
# Actual intersections of coherent composition faces

The intersection of two original middle-vertex faces is identified with
the literal product of the three original coherent Hom objects. The
inverse splits that same whole path twice. Both scalar inverse equations
and the original left/right union-composition agreement are proved.
Coincident middle vertices are included.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.DoubleCompositionFace
open CompositionFace
variable {J : Type u} [LinearOrder J] (i j k l : J)

private instance (a b : SimplicialThickening.Path i l) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The same original path has both specified middle vertices at every scalar vertex. -/
def face : (nerve (SimplicialThickening.Path i l)).Subcomplex :=
  positive i j l ⊓ positive i k l

/-- The literal original three-Hom product with the right parenthesization. -/
abbrev triple : SSet.{u} :=
  nerve (SimplicialThickening.Path i j) ⊗
    (nerve (SimplicialThickening.Path j k) ⊗ nerve (SimplicialThickening.Path k l))

/-- The actual right-parenthesized coherent union composition on the three original Hom objects. -/
def composition : triple i j k l ⟶ nerve (SimplicialThickening.Path i l) :=
  nerve (SimplicialThickening.Path i j) ◁ CompositionFace.composition j k l ≫
    CompositionFace.composition i j l

/-- The original triple union lies in both original middle-vertex faces. -/
def glue : triple i j k l ⟶ face i j k l where
  app q := ↾fun p => ⟨(composition i j k l).app q p,
    ⟨fun t => Or.inl (p.1.obj t).right,
      fun t => Or.inr (Or.inl (p.2.1.obj t).right)⟩⟩
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact congr($((composition i j k l).naturality f) p)

variable {i j k l}

/-- The actual right interval path retains the second supplied middle vertex. -/
theorem middle_mem (hjk : j ≤ k) {q : SimplexCategoryᵒᵖ}
    (p : (face i j k l : SSet.{u}).obj q) (t : Fin (q.unop.len + 1)) :
    k ∈ (rightPath (p.val.obj t) (p.property.1 t)).I :=
  ⟨p.property.2 t, hjk⟩

variable (i j k l)

/-- The actual second and third original path chains after the first original interval split. -/
def rightFace (hjk : j ≤ k) {q : SimplexCategoryᵒᵖ}
    (p : (face i j k l : SSet.{u}).obj q) : (positive j k l : SSet.{u}).obj q :=
  ⟨rightChain i j l ⟨p.val, p.property.1⟩, middle_mem hjk p⟩

/-- Split the same whole original double face into its three original interval Hom chains. -/
def split (hjk : j ≤ k) : (face i j k l : SSet.{u}) ⟶ triple i j k l where
  app q := ↾fun p =>
    (leftChain i j l ⟨p.val, p.property.1⟩,
      (leftChain j k l (rightFace i j k l hjk p), rightChain j k l (rightFace i j k l hjk p)))
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
      intro x y g
      exact Subsingleton.elim _ _
    · apply Prod.ext
      · refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
        intro x y g
        exact Subsingleton.elim _ _
      · refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
        intro x y g
        exact Subsingleton.elim _ _

/-- The genuine whole triple-Hom isomorphism onto the intersection of the two original
composition faces. -/
def faceIso (hjk : j ≤ k) : triple i j k l ≅ face i j k l where
  hom := glue i j k l
  inv := split i j k l hjk
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · refine CategoryTheory.Functor.ext (fun t => left_union (p.1.obj t)
        ((SimplicialThickening.compFunctor (.mk j) (.mk k) (.mk l)).obj (p.2.1.obj t,
          p.2.2.obj t))) ?_
      intro x y g
      exact Subsingleton.elim _ _
    · apply Prod.ext
      · refine CategoryTheory.Functor.ext (fun t => ?_) ?_
        · change leftPath (rightPath
            ((SimplicialThickening.compFunctor (.mk i) (.mk j) (.mk l)).obj
              (p.1.obj t, (SimplicialThickening.compFunctor (.mk j) (.mk k) (.mk l)).obj
                (p.2.1.obj t, p.2.2.obj t))) (Or.inl (p.1.obj t).right))
              ⟨Or.inr (Or.inl (p.2.1.obj t).right), hjk⟩ = p.2.1.obj t
          apply SimplicialThickening.Path.ext
          exact (congrArg (fun z : SimplicialThickening.Path j l => z.I ∩ Set.Iic k)
            (right_union (p.1.obj t)
              ((SimplicialThickening.compFunctor (.mk j) (.mk k) (.mk l)).obj
                (p.2.1.obj t, p.2.2.obj t)))).trans
              (congrArg SimplicialThickening.Path.I (left_union (p.2.1.obj t) (p.2.2.obj t)))
        · intro x y g
          exact Subsingleton.elim _ _
      · refine CategoryTheory.Functor.ext (fun t => ?_) ?_
        · change rightPath (rightPath
            ((SimplicialThickening.compFunctor (.mk i) (.mk j) (.mk l)).obj
              (p.1.obj t, (SimplicialThickening.compFunctor (.mk j) (.mk k) (.mk l)).obj
                (p.2.1.obj t, p.2.2.obj t))) (Or.inl (p.1.obj t).right))
              ⟨Or.inr (Or.inl (p.2.1.obj t).right), hjk⟩ = p.2.2.obj t
          apply SimplicialThickening.Path.ext
          exact (congrArg (fun z : SimplicialThickening.Path j l => z.I ∩ Set.Ici k)
            (right_union (p.1.obj t)
              ((SimplicialThickening.compFunctor (.mk j) (.mk k) (.mk l)).obj
                (p.2.1.obj t, p.2.2.obj t)))).trans
              (congrArg SimplicialThickening.Path.I (right_union (p.2.1.obj t) (p.2.2.obj t)))
        · intro x y g
          exact Subsingleton.elim _ _
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => ?_) ?_
    · change (SimplicialThickening.compFunctor (.mk i) (.mk j) (.mk l)).obj
        (leftPath (p.val.obj t) (p.property.1 t),
          (SimplicialThickening.compFunctor (.mk j) (.mk k) (.mk l)).obj
            (leftPath (rightPath (p.val.obj t) (p.property.1 t)) (middle_mem hjk p t),
              rightPath (rightPath (p.val.obj t) (p.property.1 t)) (middle_mem hjk p t))) =
                p.val.obj t
      rw [union_split, union_split]
    · intro x y g
      exact Subsingleton.elim _ _

/-- The original double-face forward map reads back the entire original right-parenthesized
composition. -/
theorem faceIso_composition (hjk : j ≤ k) :
    (faceIso i j k l hjk).hom ≫ (face i j k l).ι = composition i j k l := rfl

/-- Both original parenthesizations give exactly the same whole coherent Hom map on the
actual double face. -/
theorem left_composition :
    (α_ (nerve (SimplicialThickening.Path i j)) (nerve (SimplicialThickening.Path j k))
      (nerve (SimplicialThickening.Path k l))).inv ≫
        CompositionFace.composition i j k ▷ nerve (SimplicialThickening.Path k l) ≫
          CompositionFace.composition i k l = composition i j k l :=
  e_assoc SSet.{u} (C := SimplicialThickening J) (.mk i) (.mk j) (.mk k) (.mk l)

end CategoryTheory.CoherentRealization.DoubleCompositionFace
