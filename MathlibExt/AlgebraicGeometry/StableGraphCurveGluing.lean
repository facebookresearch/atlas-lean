/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StableCurveStackModels
public import MathlibExt.AlgebraicGeometry.PixtonWeightings
public import Mathlib.CategoryTheory.Pi.Basic

/-!
# Actual stable-graph curve gluing and product stack points

Every branch and leg is a genuine marked point of an actual vertex curve.
The glued scheme is the quotient of those actual schemes by the prescribed
branch-section pairs, with the full universal property over the parameter
scheme. Equalities of geometric points alone are not used as the gluing
operation. Vertex arrows are actual marking-preserving curve isomorphisms.

The graph product stack is identified with the product of these entire
scheme-valued fibre groupoids. Stable-graph automorphisms and modular
weights reuse the completed native combinatorics in PixtonWeightings.
Source: JPPZ arXiv:1602.04705v2, Sections 0.3.2--0.3.3, printed pp8--9.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StableGraphCurveGluing

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open StableCurveStackModels UniversalCurveStability MarkedCurveStabilization
open StackCycleGeometry StackCycleRelations

variable {g n : ℕ} (G : StableGraph g n)

abbrev HalfEdge := Fin n ⊕ (Fin G.edges × Fin 2)

def vertexOf : HalfEdge G → Fin G.vertices :=
  Sum.elim G.marking (fun h => G.endpoint h.1 h.2)

abbrev HalfEdgesAt (v : Fin G.vertices) := {h : HalfEdge G // vertexOf G h = v}

instance halfEdgesAtFintype (v : Fin G.vertices) : Fintype (HalfEdgesAt G v) :=
  Fintype.ofFinite _

def vertexValence (v : Fin G.vertices) : ℕ := Fintype.card (HalfEdgesAt G v)

def halfEdgeIndex (h : HalfEdge G) : Fin (vertexValence G (vertexOf G h)) :=
  Fintype.equivFin (HalfEdgesAt G (vertexOf G h)) ⟨h, rfl⟩

variable {k : Type} [Field k] (T : Over (Spec (.of k)))

abbrev VertexFamilies :=
  ∀ v : Fin G.vertices, CurveFamily T (G.genus v) (vertexValence G v)

def branchSection (F : VertexFamilies G T) (h : HalfEdge G) :
    T.left ⟶ (curve (F (vertexOf G h))).X :=
  (curve (F (vertexOf G h))).marking (halfEdgeIndex G h)

/-- The actual node quotient, with the source branch pairs and leg labels fixed. -/
structure CurveGluing (F : VertexFamilies G T) where
  glued : MarkedFamily T.left n g
  stable : MarkedCurveStabilization.IsStable glued
  component : ∀ v : Fin G.vertices, (curve (F v)).X ⟶ glued.X
  over : ∀ v, component v ≫ glued.π = (curve (F v)).π
  legs : ∀ i : Fin n,
    branchSection G T F (Sum.inl i) ≫ component (G.marking i) = glued.marking i
  nodes : ∀ e : Fin G.edges,
    branchSection G T F (Sum.inr (e, 0)) ≫ component (G.endpoint e 0) =
      branchSection G T F (Sum.inr (e, 1)) ≫ component (G.endpoint e 1)
  universal : ∀ (Z : Scheme.{0}) (z : Z ⟶ T.left)
      (f : ∀ v : Fin G.vertices, (curve (F v)).X ⟶ Z),
    (∀ v, f v ≫ z = (curve (F v)).π) →
    (∀ e : Fin G.edges,
      branchSection G T F (Sum.inr (e, 0)) ≫ f (G.endpoint e 0) =
        branchSection G T F (Sum.inr (e, 1)) ≫ f (G.endpoint e 1)) →
      ∃! h : glued.X ⟶ Z, h ≫ z = glued.π ∧ ∀ v, component v ≫ h = f v

def CurveGluing.output {F : VertexFamilies G T} (Q : CurveGluing G T F) : CurveFamily T g n :=
  ⟨⟨Q.glued, Q.glued.π ≫ T.hom, by simp⟩, Q.stable⟩

/-- The literal product of the vertex moduli family functors. -/
def vertexFamilyFunctor
    (V : ∀ v : Fin G.vertices, StableCurveStackModel (k := k) (G.genus v) (vertexValence G v))
    (X : Stack (Spec (.of k))) (p : ∀ v : Fin G.vertices, StackHom X (V v).stack) :
    X.Fibre T ⥤ VertexFamilies G T where
  obj x v := ((V v).family T).obj ((component (p v) T).obj x)
  map h v := ((V v).family T).map ((component (p v) T).map h)
  map_id x := by
    funext v
    change ((V v).family T).map ((component (p v) T).map (𝟙 x)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp f h := by
    funext v
    change ((V v).family T).map ((component (p v) T).map (f ≫ h)) =
      ((V v).family T).map ((component (p v) T).map f) ≫
        ((V v).family T).map ((component (p v) T).map h)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-- The product is normalized on all objects and arrows of every scheme fibre. -/
structure GraphProductData
    (V : ∀ v : Fin G.vertices, StableCurveStackModel (k := k) (G.genus v) (vertexValence G v)) where
  stack : Stack (Spec (.of k))
  vertex : ∀ v : Fin G.vertices, StackHom stack (V v).stack
  product : ∀ T : Over (Spec (.of k)), (vertexFamilyFunctor G T V stack vertex).IsEquivalence
  finiteType : FiniteTypeArtin k stack
  dm : stack.IsDeligneMumfordStack
  dimension : HasDimension stack (3 * (g : ℤ) - 3 + n - G.edges)

def GraphProductData.families
    {V : ∀ v : Fin G.vertices, StableCurveStackModel (k := k) (G.genus v) (vertexValence G v)}
    (P : GraphProductData G V) : P.stack.Fibre T ⥤ VertexFamilies G T :=
  vertexFamilyFunctor G T V P.stack P.vertex

end MathlibExt.AlgebraicGeometry.StableGraphCurveGluing
