/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeThroughPairFunctors
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeThroughPrism
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductAdjunction

/-!
# Whole marked original ordered intersection prisms

The original ordered two-pivot subset nerve is exactly the original
lower coherent Hom prism over its remaining whole through-cone. The
second original split gives the complete two-path/upper-cone prism.
Both original inverse maps, all scalar operators and constant-maximum
marks are retained, including the equal-pivot self-path case.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq
private instance {n : ℕ} (i j : Vertex.{u} n) (p q : SimplicialThickening.Path i j) : Subsingleton (p ⟶ q) :=
  ⟨fun _ _ => InducedCategory.Hom.ext (Subsingleton.elim _ _)⟩

/-- The original two-pivot subset includes by its unchanged full cone subset. -/
def throughPairForgetFunctor {n : ℕ} (i j k : Vertex.{u} n) : ConeThroughPair i j k ⥤ ConeSubset i where
  obj := Subtype.val
  map f := homOfLE (leOfHom f)

/-- The entire original two-pivot cone retains its original pulled-back constant-maximum marking. -/
def coneThroughPairWeight {n : ℕ} (i j k : Vertex.{u} n) : Marked.{u} :=
  comap (coneWeight i) (nerveMap (throughPairForgetFunctor i j k))

/-- The whole original ordered two-pivot simplex reads its original lower path and full remaining through-cone. -/
def throughPairPrismHom {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    (coneThroughPairWeight i j k).toSSet ⟶
      (prod (max (nerve (SimplicialThickening.Path i j))) (coneThroughWeight j k)).toSSet where
  app q := ↾fun x =>
    (x ⋙ pairFirstThroughFunctor i j k ⋙ throughLowerPathFunctor i j,
      x ⋙ pairUpperThroughFunctor hjk)
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext rfl rfl

/-- The whole inverse ordered prism uses exactly the original native path union and remaining through-cone. -/
def throughPairPrismInv {n : ℕ} {i j k : Vertex.{u} n} :
    (prod (max (nerve (SimplicialThickening.Path i j))) (coneThroughWeight j k)).toSSet ⟶
      (coneThroughPairWeight i j k).toSSet where
  app q := ↾fun x => x.1.prod' x.2 ⋙ throughPairUnionFunctor i j k
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro x
    refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- The full original ordered intersection nerve is its genuine whole coherent Hom/through-cone prism. -/
def throughPairPrismNerveIso {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    (coneThroughPairWeight i j k).toSSet ≅
      (prod (max (nerve (SimplicialThickening.Path i j))) (coneThroughWeight j k)).toSSet where
  hom := throughPairPrismHom hjk
  inv := throughPairPrismInv
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    change (x ⋙ throughPairSplitFunctor (i := i) hjk) ⋙ throughPairUnionFunctor i j k = x
    refine CategoryTheory.Functor.ext (fun t => pathThroughPair_split hjk (x.obj t)) (fun _ _ _ =>
      Subsingleton.elim _ _)
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · refine CategoryTheory.Functor.ext (fun t => pairFirstThrough_lower_path (x.1.obj t) (x.2.obj t))
        (fun _ _ _ => Subsingleton.elim _ _)
    · refine CategoryTheory.Functor.ext (fun t => pairUpperThrough_path hjk (x.1.obj t) (x.2.obj t))
        (fun _ _ _ => Subsingleton.elim _ _)

/-- The actual original ordered intersection marking is exactly maximal lower-path marking and the original
  remaining-through marking. -/
theorem throughPairPrism_marking_iff {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k)
    (e : (coneThroughPairWeight i j k).toSSet _⦋1⦌) :
    e ∈ (coneThroughPairWeight i j k).marking ↔
      (throughPairPrismHom hjk).app (op ⦋1⦌) e ∈
        (prod (max (nerve (SimplicialThickening.Path i j))) (coneThroughWeight j k)).marking := by
  change ((e.obj 0).val.maximum = (e.obj 1).val.maximum) ↔
    True ∧ (pairUpperThrough hjk (e.obj 0)).val.maximum = (pairUpperThrough hjk (e.obj 1)).val.maximum
  rw [pairUpperThrough_maximum, pairUpperThrough_maximum]
  exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩

/-- The entire original ordered two-pivot cone is its genuine marked lower-path/remaining-through prism. -/
def throughPairPrismIso {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    coneThroughPairWeight i j k ≅ prod (max (nerve (SimplicialThickening.Path i j))) (coneThroughWeight j k) :=
  isoMk (throughPairPrismNerveIso hjk) (throughPairPrism_marking_iff hjk)

/-- The whole original ordered two-pivot cone is exactly its marked two-path/upper-cone prism by both native
  original splits. -/
def throughPairTriplePrismIso {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    coneThroughPairWeight i j k ≅
      prod (max (nerve (SimplicialThickening.Path i j)))
        (prod (max (nerve (SimplicialThickening.Path j k))) (coneWeight k)) :=
  throughPairPrismIso hjk ≪≫
    (markedProductBifunctor.mapIso (throughPrismIso j k)).app (max (nerve (SimplicialThickening.Path i j)))

end SSet.Marked.CoherentWeight
