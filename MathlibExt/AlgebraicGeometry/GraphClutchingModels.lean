/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StableGraphCurveGluing
public import MathlibExt.AlgebraicGeometry.StackProjectiveModels

/-!
# Source-normalized geometric graph clutching

The clutching morphism is fixed on every scheme-valued family by the
actual node quotient of the pulled vertex curves. Its arrow map and every
base-change map commute with the same component maps and native stack
comparison cells. Consequently no unrelated morphism named xi_Gamma is
substituted for the geometric operation.
Source: JPPZ arXiv:1602.04705v2, Section 0.3.3, printed p9.
Ordinary curve, groupoid, pullback and quotient primitives retain the
source attribution of StableCurveStackModels and StableGraphCurveGluing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GraphClutchingModels

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open StableCurveStackModels StableGraphCurveGluing UniversalCurveStability
open StackCycleGeometry StackCycleRelations StackProjectiveModels

variable {k : Type} [Field k]

def mappedFamilyAt {g n : ℕ} (M : StableCurveStackModel (k := k) g n)
    {X : Stack (Spec (.of k))} (p : StackHom X M.stack)
    (T : Over (Spec (.of k))) (x : X.Fibre T) :=
  familyAt M T ((component p T).obj x)

def mappedFamilyArrow {g n : ℕ} (M : StableCurveStackModel (k := k) g n)
    {X : Stack (Spec (.of k))} (p : StackHom X M.stack)
    (T : Over (Spec (.of k))) {x y : X.Fibre T} (h : x ⟶ y) :
    (mappedFamilyAt M p T x).X ≅ (mappedFamilyAt M p T y).X :=
  ((M.family T).map ((component p T).map h)).hom.iso

/-- The actual native strong-transformation cell followed by the actual
Cartesian curve projection, in the correct source-to-target direction. -/
def mappedFamilyReindex {g n : ℕ} (M : StableCurveStackModel (k := k) g n)
    {X : Stack (Spec (.of k))} (p : StackHom X M.stack)
    {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : X.Fibre U) :
    (mappedFamilyAt M p T ((pull X f).obj x)).X ⟶ (mappedFamilyAt M p U x).X :=
  ((M.family T).map ((Cat.Hom.toNatIso (p.naturality f.op.toLoc)).hom.app x)).hom.iso.hom ≫
    (M.reindex f ((component p U).obj x)).projection

theorem mappedFamilyReindex_marking {g n : ℕ} (M : StableCurveStackModel (k := k) g n)
    {X : Stack (Spec (.of k))} (p : StackHom X M.stack)
    {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : X.Fibre U) (i : Fin n) :
    (mappedFamilyAt M p T ((pull X f).obj x)).marking i ≫ mappedFamilyReindex M p f x =
      f.left ≫ (mappedFamilyAt M p U x).marking i := by
  rw [mappedFamilyReindex, ← Category.assoc]
  exact (congrArg (fun s => s ≫ (M.reindex f ((component p U).obj x)).projection)
    (((M.family T).map
      ((Cat.Hom.toNatIso (p.naturality f.op.toLoc)).hom.app x)).hom.markings i)).trans
        ((M.reindex f ((component p U).obj x)).markings i)

def totalFamilyMap {g n : ℕ} (M : StableCurveStackModel (k := k) g n)
    {X : Stack (Spec (.of k))} (p : StackHom X M.stack)
    {a b : Pseudofunctor.CoGrothendieck X.toPseudofunctor} (h : a ⟶ b) :
    (mappedFamilyAt M p a.base a.fiber).X ⟶ (mappedFamilyAt M p b.base b.fiber).X :=
  (mappedFamilyArrow M p a.base h.fiber).hom ≫ mappedFamilyReindex M p h.base b.fiber

theorem totalFamilyMap_marking {g n : ℕ} (M : StableCurveStackModel (k := k) g n)
    {X : Stack (Spec (.of k))} (p : StackHom X M.stack)
    {a b : Pseudofunctor.CoGrothendieck X.toPseudofunctor} (h : a ⟶ b) (i : Fin n) :
    (mappedFamilyAt M p a.base a.fiber).marking i ≫ totalFamilyMap M p h =
      h.base.left ≫ (mappedFamilyAt M p b.base b.fiber).marking i := by
  rw [totalFamilyMap, ← Category.assoc]
  exact (congrArg (fun s => s ≫ mappedFamilyReindex M p h.base b.fiber)
    (((M.family a.base).map ((component p a.base).map h.fiber)).hom.markings i)).trans
      (mappedFamilyReindex_marking M p h.base b.fiber i)

variable {g n : ℕ} (G : StableGraph g n)
  (V : ∀ v : Fin G.vertices, StableCurveStackModel (k := k) (G.genus v) (vertexValence G v))
  (P : GraphProductData G V) (M : StableCurveStackModel (k := k) g n)

/-- Clutching is the actual family quotient on objects, arrows and every base change. -/
structure GraphClutchingData where
  clutch : StackHom P.stack M.stack
  projective : ProjectiveMorphism clutch
  gluing : ∀ (T : Over (Spec (.of k))) (x : P.stack.Fibre T),
    CurveGluing G T ((P.families G T).obj x)
  comparison : ∀ (T : Over (Spec (.of k))) (x : P.stack.Fibre T),
    CurveGluing.output G T (gluing T x) ≅ (M.family T).obj ((component clutch T).obj x)
  arrows : ∀ (T : Over (Spec (.of k))) {x y : P.stack.Fibre T} (h : x ⟶ y)
      (v : Fin G.vertices),
    (gluing T x).component v ≫ (comparison T x).hom.hom.iso.hom ≫
      (mappedFamilyArrow M clutch T h).hom =
    ((P.families G T).map h v).hom.iso.hom ≫
      (gluing T y).component v ≫ (comparison T y).hom.hom.iso.hom
  reindex : ∀ {T U : Over (Spec (.of k))} (f : T ⟶ U) (x : P.stack.Fibre U)
      (v : Fin G.vertices),
    (gluing T ((pull P.stack f).obj x)).component v ≫
      (comparison T ((pull P.stack f).obj x)).hom.hom.iso.hom ≫
        mappedFamilyReindex M clutch f x =
    mappedFamilyReindex (V v) (P.vertex v) f x ≫
      (gluing U x).component v ≫ (comparison U x).hom.hom.iso.hom

end MathlibExt.AlgebraicGeometry.GraphClutchingModels
