/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeThroughFunctors
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso

/-!
# Whole original marked through-cone free prism

The entire through-subset nerve is the actual product of its original
lower coherent Hom nerve and upper cone nerve. Both maps retain all
original simplex operators. The lower Hom is maximally marked and the
upper cone keeps its original maximum marking, giving exactly the
through-cone marking. The inverse followed by original inclusion is
precisely the full native cone action.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq
private instance {n : ℕ} (i j : Vertex.{u} n) (p q : SimplicialThickening.Path i j) : Subsingleton (p ⟶ q) :=
  ⟨fun _ _ => InducedCategory.Hom.ext (Subsingleton.elim _ _)⟩

/-- The original through-subset inclusion forgets only the proof that its pivot was retained. -/
def throughForgetFunctor {n : ℕ} (i j : Vertex.{u} n) : ConeThrough i j ⥤ ConeSubset i where
  obj := Subtype.val
  map f := homOfLE (leOfHom f)

/-- The entire original through-cone has precisely the pulled-back original maximum-preserving marking. -/
def coneThroughWeight {n : ℕ} (i j : Vertex.{u} n) : Marked.{u} :=
  comap (coneWeight i) (nerveMap (throughForgetFunctor i j))

/-- The entire original through-cone nerve splits into its whole original coherent path and upper-cone simplex. -/
def throughPrismHom {n : ℕ} (i j : Vertex.{u} n) :
    (coneThroughWeight i j).toSSet ⟶ (prod (max (nerve (SimplicialThickening.Path i j))) (coneWeight j)).toSSet where
  app q := ↾fun x => (x ⋙ throughLowerPathFunctor i j, x ⋙ throughUpperConeFunctor i j)
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext rfl rfl

/-- The inverse whole original prism reconstructs the native through-cone by the original path union. -/
def throughPrismInv {n : ℕ} (i j : Vertex.{u} n) :
    (prod (max (nerve (SimplicialThickening.Path i j))) (coneWeight j)).toSSet ⟶ (coneThroughWeight i j).toSSet where
  app q := ↾fun x => x.1.prod' x.2 ⋙ throughUnionFunctor i j
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro x
    refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- The full original through-cone nerve is its actual whole scalar prism, with both original inverse maps proved. -/
def throughPrismNerveIso {n : ℕ} (i j : Vertex.{u} n) :
    (coneThroughWeight i j).toSSet ≅ (prod (max (nerve (SimplicialThickening.Path i j))) (coneWeight j)).toSSet where
  hom := throughPrismHom i j
  inv := throughPrismInv i j
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    change (x ⋙ throughSplitFunctor i j) ⋙ throughUnionFunctor i j = x
    refine CategoryTheory.Functor.ext (fun t => pathThrough_split (x.obj t)) (fun _ _ _ => Subsingleton.elim _ _)
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · refine CategoryTheory.Functor.ext
        (fun t => throughLowerPath_pathThrough (x.1.obj t) (x.2.obj t)) (fun _ _ _ => Subsingleton.elim _ _)
    · refine CategoryTheory.Functor.ext
        (fun t => throughUpperCone_pathThrough (x.1.obj t) (x.2.obj t)) (fun _ _ _ => Subsingleton.elim _ _)

/-- The whole original through-cone marking is exactly maximal original path marking times the original
  upper maximum marking. -/
theorem throughPrism_marking_iff {n : ℕ} (i j : Vertex.{u} n) (e : (coneThroughWeight i j).toSSet _⦋1⦌) :
    e ∈ (coneThroughWeight i j).marking ↔
      (throughPrismHom i j).app (op ⦋1⦌) e ∈ (prod (max (nerve (SimplicialThickening.Path i j))) (coneWeight
        j)).marking := by
  change ((e.obj 0).val.maximum = (e.obj 1).val.maximum) ↔
    True ∧ (throughUpperCone (e.obj 0)).maximum = (throughUpperCone (e.obj 1)).maximum
  rw [throughUpperCone_maximum, throughUpperCone_maximum]
  exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩

/-- The entire original through-cone is the genuine marked free coherent Hom prism over its unchanged upper cone. -/
def throughPrismIso {n : ℕ} (i j : Vertex.{u} n) :
    coneThroughWeight i j ≅ prod (max (nerve (SimplicialThickening.Path i j))) (coneWeight j) :=
  isoMk (throughPrismNerveIso i j) (throughPrism_marking_iff i j)

/-- The original through-cone includes by its complete original subset map and original marks. -/
def throughWeightInclusion {n : ℕ} (i j : Vertex.{u} n) : coneThroughWeight i j ⟶ coneWeight i :=
  comapHom (coneWeight i) (nerveMap (throughForgetFunctor i j))

/-- The whole inverse through-prism followed by original inclusion is precisely the original native cone
  action on all paths and coefficients. -/
theorem throughPrism_inv_inclusion {n : ℕ} (i j : Vertex.{u} n) :
    (throughPrismIso i j).inv ≫ throughWeightInclusion i j = coneAction i j := by
  apply Hom.ext
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro x
  refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _)

end SSet.Marked.CoherentWeight
