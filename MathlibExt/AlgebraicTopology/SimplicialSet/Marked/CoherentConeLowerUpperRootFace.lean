/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCofaceMaxima
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeUpperRootBoundaryUnit

/-!
# Full original lower/upper root intersections and positive preimages

The exact original lower/upper coordinate intersection retains its
entire inherited maximum marking and both original projections. The
genuine original lower-coface inverse takes every whole intersection
word to a positive original smaller-root word: its original positive
upper coordinate bounds the unchanged original image maximum. This
constructs a full marked map into the original positive root cone.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The full actual original marked lower/upper root-coordinate intersection retains both original coordinates and
every inherited original maximum mark. -/
def coneLowerUpperRootFaceWeight {n : ℕ} (j k : Fin (n + 2)) : Marked.{u} :=
  comap (coneWeight (⊥ : Vertex.{u} (n + 1)))
    (coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) (ULift.up j) false ⊓
      coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) (ULift.up k) true).ι

/-- The original whole marked lower/upper intersection retains its unchanged full-root-cone inclusion. -/
def coneLowerUpperRootFaceInclusion {n : ℕ} (j k : Fin (n + 2)) :
    coneLowerUpperRootFaceWeight.{u} j k ⟶ coneWeight (⊥ : Vertex.{u} (n + 1)) :=
  comapHom (coneWeight (⊥ : Vertex.{u} (n + 1)))
    (coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) (ULift.up j) false ⊓
      coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) (ULift.up k) true).ι

/-- The unchanged original lower-coordinate projection of the full marked lower/upper root intersection. -/
def coneLowerUpperRootFaceLeft {n : ℕ} (j k : Fin (n + 2)) :
    coneLowerUpperRootFaceWeight.{u} j k ⟶ coneLowerRootFaceWeight j :=
  (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1)))).map (homOfLE inf_le_left)

/-- The unchanged original upper-coordinate projection of the full marked lower/upper root intersection. -/
def coneLowerUpperRootFaceRight {n : ℕ} (j k : Fin (n + 2)) :
    coneLowerUpperRootFaceWeight.{u} j k ⟶ coneUpperFaceMarked (⊥ : Vertex.{u} (n + 1)) (ULift.up k) :=
  (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1)))).map (homOfLE inf_le_right)

/-- The first original coordinate projection keeps the whole original intersection inclusion. -/
theorem coneLowerUpperRootFaceLeft_inclusion {n : ℕ} (j k : Fin (n + 2)) :
    coneLowerUpperRootFaceLeft.{u} j k ≫ coneLowerRootFaceInclusion j = coneLowerUpperRootFaceInclusion j k := by
  apply Hom.ext
  rfl

/-- The second original coordinate projection keeps the whole original intersection inclusion. -/
theorem coneLowerUpperRootFaceRight_inclusion {n : ℕ} (j k : Fin (n + 2)) :
    coneLowerUpperRootFaceRight.{u} j k ≫ coneUpperFaceInclusion (⊥ : Vertex.{u} (n + 1)) (ULift.up k) =
      coneLowerUpperRootFaceInclusion j k := by
  apply Hom.ext
  rfl

/-- The complete original lower/upper marked intersection reads its whole smaller-root cone word through the same
genuine original lower-coface inverse. -/
def coneLowerUpperRootPreimage {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) (k : Fin (n + 2)) :
    coneLowerUpperRootFaceWeight.{u} j k ⟶ coneWeight (⊥ : Vertex.{u} n) :=
  coneLowerUpperRootFaceLeft j k ≫ (coneLowerRootFaceIso j hj).inv

/-- The entire original lower/upper preimage retains exactly the original unchanged full intersection inclusion
under its genuine whole root-coface image. -/
theorem coneLowerUpperRootPreimage_inclusion {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) (k : Fin (n + 2)) :
    coneLowerUpperRootPreimage.{u} j hj k ≫ coneRootCofaceImage j hj = coneLowerUpperRootFaceInclusion j k := by
  let e := coneLowerRootFaceIso.{u} j hj
  let p := coneLowerRootFaceInclusion.{u} j
  have ht : e.inv ≫ coneRootCofaceImage j hj = p :=
    (congrArg (fun f => e.inv ≫ f) (coneLowerRootFaceIso_rootImage j hj).symm).trans (e.inv_hom_id_assoc p)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => coneLowerUpperRootFaceLeft j k ≫ f) ht).trans (coneLowerUpperRootFaceLeft_inclusion j k))

/-- Every scalar vertex of every whole original lower/upper intersection word has a genuinely positive original
smaller-root maximum under its unchanged original lower-coface inverse. -/
theorem coneLowerUpperRootPreimage_positive {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (k : Fin (n + 2)) (hk : 0 < k) (q : SimplexCategoryᵒᵖ)
    (x : (coneLowerUpperRootFaceWeight.{u} j k).toSSet.obj q) (t : Fin (q.unop.len + 1)) :
    (⊥ : Vertex.{u} n) < (((coneLowerUpperRootPreimage j hj k).hom.app q x).obj t).maximum := by
  let p := coneLowerUpperRootPreimage.{u} j hj k
  have hx : (coneRootCofaceImage j hj).hom.app q (p.hom.app q x) = x.val :=
    congrArg (fun f : coneLowerUpperRootFaceWeight.{u} j k ⟶ coneWeight (⊥ : Vertex.{u} (n + 1)) =>
      f.hom.app q x) (coneLowerUpperRootPreimage_inclusion j hj k)
  have hm : coneCofaceEmbedding j ((p.hom.app q x).obj t).maximum = (x.val.obj t).maximum :=
    (coneRootCofaceImage_maximum j hj q (p.hom.app q x) t).symm.trans
      (congrArg (fun a => (a.obj t).maximum) hx)
  have hkMem : ULift.up k ∈ (x.val.obj t).vertices := (x.property.2 t).mpr rfl
  have hpos : (⊥ : Vertex.{u} (n + 1)) < (x.val.obj t).maximum :=
    (show (⊥ : Vertex.{u} (n + 1)) < ULift.up k from hk).trans_le ((x.val.obj t).le_maximum _ hkMem)
  by_contra hnot
  have hz : ((p.hom.app q x).obj t).maximum = (⊥ : Vertex.{u} n) :=
    le_antisymm (le_of_not_gt hnot) bot_le
  have hmax : (x.val.obj t).maximum = (⊥ : Vertex.{u} (n + 1)) :=
    hm.symm.trans ((congrArg (coneCofaceEmbedding j) hz).trans (coneCofaceEmbedding_root j hj))
  exact (lt_irrefl _) (hmax ▸ hpos)

/-- The entire original lower/upper intersection simplex lifts to its same complete original positive smaller-root
simplex. -/
def coneLowerUpperRootPositiveSimplex {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (k : Fin (n + 2)) (hk : 0 < k) (q : SimplexCategoryᵒᵖ)
    (x : (coneLowerUpperRootFaceWeight.{u} j k).toSSet.obj q) :
    (nerve (ConeAfter (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n))).obj q where
  obj t := ⟨((coneLowerUpperRootPreimage j hj k).hom.app q x).obj t,
    coneLowerUpperRootPreimage_positive j hj k hk q x t⟩
  map h := homOfLE (leOfHom (((coneLowerUpperRootPreimage j hj k).hom.app q x).map h))

/-- The whole original marked lower/upper intersection maps into the same original positive smaller-root cone by its
genuine coface inverse, preserving every scalar operator and inherited maximum mark. -/
def coneLowerUpperRootPositivePreimage {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (k : Fin (n + 2)) (hk : 0 < k) :
    coneLowerUpperRootFaceWeight.{u} j k ⟶ coneAfterWeight (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n) where
  hom :=
    { app q := ↾fun x => coneLowerUpperRootPositiveSimplex j hj k hk q x
      naturality q r f := by
        apply ConcreteCategory.hom_ext
        intro x
        refine CategoryTheory.Functor.ext (fun t => Subtype.ext ?_) (fun _ _ _ => Subsingleton.elim _ _)
        exact congrArg (fun a => a.obj t) (congr($((coneLowerUpperRootPreimage j hj k).hom.naturality f) x)) }
  preserve {e} he := (coneLowerUpperRootPreimage j hj k).preserve he

/-- The complete original marked positive preimage retains exactly its unchanged original coface inverse under the
original full positive inclusion. -/
theorem coneLowerUpperRootPositivePreimage_inclusion {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (k : Fin (n + 2)) (hk : 0 < k) :
    coneLowerUpperRootPositivePreimage.{u} j hj k hk ≫ coneAfterInclusion (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n) =
      coneLowerUpperRootPreimage j hj k := by
  apply Hom.ext
  ext q x
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

end SSet.Marked.CoherentWeight
