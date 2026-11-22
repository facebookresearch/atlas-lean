/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopSpaceWeakEquivalence

/-!
# Based positive homotopy groups and every component of simplicial loops

A map of Kan complexes that is bijective on positive homotopy groups at one
specified source vertex induces a weak equivalence of the loop spaces at that
vertex. No condition on the other components of the original spaces is needed.

The proof uses the genuine based-path fibration, with its total-space point
chosen at each individual loop vertex. The contractible total spaces and the
existing exactness, multiplication, and degree-zero correction theorem make
the connecting maps bijective. Their naturality supplies the homotopy-group
bijections at every loop component, including degree zero.

The rerooted fibration argument is adapted from the private helpers in
`LoopSpaceWeakEquivalence`. Here its exact source data and whole morphism are
public, and the incoming assumption is the specified based positive map.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalClosed Simplicial Opposite
open scoped Simplicial

universe u

namespace SSet

/-- The actual based-path fibration rerooted at an arbitrary loop vertex.
Its base vertex remains `x`; its chosen fiber point is the supplied `z`. -/
def loopFibrationSequenceAtVertex (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (z : loopSpace X x _⦋0⦌) : FibrationSequence.{u} where
  E := basedPath X x
  B := X
  p := basedPathProj X x
  fibration_p := inferInstance
  fibrant_B := inferInstance
  e := z.val
  b := x
  hb := (Subcomplex.mem_fiber_obj_zero_iff (basedPathProj X x) x).mp z.property

/-- Rerooting changes no total space. -/
@[simp]
theorem loopFibrationSequenceAtVertex_total (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (z : loopSpace X x _⦋0⦌) :
    (loopFibrationSequenceAtVertex X x z).E = basedPath X x := rfl

/-- Rerooting changes no projection. -/
@[simp]
theorem loopFibrationSequenceAtVertex_proj (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (z : loopSpace X x _⦋0⦌) :
    (loopFibrationSequenceAtVertex X x z).p = basedPathProj X x := rfl

/-- The strict fiber is the same actual loop space at every chosen vertex. -/
@[simp]
theorem loopFibrationSequenceAtVertex_fiber (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (z : loopSpace X x _⦋0⦌) :
    (loopFibrationSequenceAtVertex X x z).fiber = loopSpace X x := rfl

/-- The chosen strict-fiber vertex is exactly the supplied loop vertex. -/
@[simp]
theorem loopFibrationSequenceAtVertex_fiberPoint (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (z : loopSpace X x _⦋0⦌) :
    (loopFibrationSequenceAtVertex X x z).fiberPoint = z := by
  apply Subtype.ext
  rfl

/-- A strictly pointed map induces the entire morphism of rerooted
based-path fibrations, with the actual image of the supplied loop vertex. -/
def loopFibrationSequenceAtVertexHom
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y)
    (z : loopSpace X x _⦋0⦌) :
    FibrationSequenceHom (loopFibrationSequenceAtVertex X x z)
      (loopFibrationSequenceAtVertex Y y ((loopSpaceMap f h).app _ z)) where
  totalMap := basedPathMap f h
  baseMap := f
  comm := basedPathMap_proj f h
  total_pt := rfl
  base_pt := h

/-- The entire morphism retains the original map on the base. -/
@[simp]
theorem loopFibrationSequenceAtVertexHom_baseMap
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y)
    (z : loopSpace X x _⦋0⦌) :
    (loopFibrationSequenceAtVertexHom f h z).baseMap = f := rfl

/-- The entire morphism retains the genuine strictly pointed based-path map. -/
@[simp]
theorem loopFibrationSequenceAtVertexHom_totalMap
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y)
    (z : loopSpace X x _⦋0⦌) :
    (loopFibrationSequenceAtVertexHom f h z).totalMap = basedPathMap f h := rfl

/-- On the actual strict fiber the morphism is the original strict loop map. -/
@[simp]
theorem loopFibrationSequenceAtVertexHom_fiberMap
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y)
    (z : loopSpace X x _⦋0⦌) :
    (loopFibrationSequenceAtVertexHom f h z).fiberMap = loopSpaceMap f h := rfl

/-- Every homotopy group of the based-path space vanishes at every total
vertex. The change of basepoint is the actual fundamental-groupoid action
along the contraction edge, rather than a chosen bijection of arbitrary sets. -/
theorem subsingleton_pi_basedPath_at_vertex (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (e : basedPath X x _⦋0⦌) (n : ℕ) :
    Subsingleton (KanComplex.π n (basedPath X x) e) := by
  let edge : Edge (basedPathPoint X x) e := by
    simpa using Edge.ofSimplicialObjectHomotopy
      (basedPathContraction X x).toSimplicialObjectHomotopy e
  let p : FundamentalGroupoid.mk (basedPathPoint X x) ⟶
      FundamentalGroupoid.mk e := FundamentalGroupoid.homMk edge
  rw [← (KanComplex.π.actionEquiv (n := n) p).subsingleton_congr]
  exact subsingleton_pi_basedPath X x n

/-- At every actual loop vertex, genuine fibration exactness makes the
connecting map bijective, with degree zero included. -/
theorem loopFibrationSequenceAtVertex_connectingMap_bijective
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌)
    (z : loopSpace X x _⦋0⦌) (n : ℕ) :
    Function.Bijective ((loopFibrationSequenceAtVertex X x z).connectingMap n) := by
  apply FibrationSequence.connectingMap_bijective_of_subsingleton_total
  intro k
  exact subsingleton_pi_basedPath_at_vertex X x z.val k

/-- The actual connecting square is natural for the whole rerooted morphism. -/
theorem loopFibrationSequenceAtVertex_connectingMap_naturality
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y)
    (z : loopSpace X x _⦋0⦌) (n : ℕ)
    (a : KanComplex.π (n + 1) X x) :
    KanComplex.π.map (loopFibrationSequenceAtVertexHom f h z).fiberMap
        (loopFibrationSequenceAtVertexHom f h z).fiberMap_app_basePoint n
        ((loopFibrationSequenceAtVertex X x z).connectingMap n a) =
      (loopFibrationSequenceAtVertex Y y ((loopSpaceMap f h).app _ z)).connectingMap n
        (KanComplex.π.map f h (n + 1) a) :=
  FibrationSequence.connectingMap_naturality (loopFibrationSequenceAtVertexHom f h z) a

/-- A bijection in based degree `n + 1` induces a bijection in loop degree
`n` at every source loop vertex. This statement also covers `n = 0`. -/
theorem loopSpaceMap_bijective_pi_of_based_positive
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y)
    (z : loopSpace X x _⦋0⦌) (n : ℕ)
    (hπ : Function.Bijective (KanComplex.π.map f h (n + 1))) :
    Function.Bijective (KanComplex.π.map (loopSpaceMap f h) rfl n (x := z)) := by
  let S := loopFibrationSequenceAtVertex X x z
  let T := loopFibrationSequenceAtVertex Y y ((loopSpaceMap f h).app _ z)
  let F := loopFibrationSequenceAtVertexHom f h z
  have hS : Function.Bijective (S.connectingMap n) :=
    loopFibrationSequenceAtVertex_connectingMap_bijective X x z n
  have hT : Function.Bijective (T.connectingMap n) :=
    loopFibrationSequenceAtVertex_connectingMap_bijective Y y
      ((loopSpaceMap f h).app _ z) n
  have hcomm :
      KanComplex.π.map F.fiberMap F.fiberMap_app_basePoint n ∘ S.connectingMap n =
        T.connectingMap n ∘ KanComplex.π.map f h (n + 1) := by
    funext a
    exact loopFibrationSequenceAtVertex_connectingMap_naturality f h z n a
  have hcomp := hT.comp hπ
  rw [← hcomm] at hcomp
  have hBottom :=
    (Function.Bijective.of_comp_iff _ hS).mp hcomp
  have ha : S.fiberPoint = z :=
    loopFibrationSequenceAtVertex_fiberPoint X x z
  have hb : T.fiberPoint = (loopSpaceMap f h).app _ z :=
    loopFibrationSequenceAtVertex_fiberPoint Y y ((loopSpaceMap f h).app _ z)
  have hMap : (loopSpaceMap f h).app _ S.fiberPoint = T.fiberPoint :=
    F.fiberMap_app_basePoint
  have hBottom' : Function.Bijective
      (KanComplex.π.map (loopSpaceMap f h) hMap n) := hBottom
  have transfer : ∀ {a₁ a₂ : loopSpace X x _⦋0⦌}
      {b₁ b₂ : loopSpace Y y _⦋0⦌}
      (ha : a₁ = a₂) (hb : b₁ = b₂)
      (h₁ : (loopSpaceMap f h).app _ a₁ = b₁)
      (h₂ : (loopSpaceMap f h).app _ a₂ = b₂),
      Function.Bijective (KanComplex.π.map (loopSpaceMap f h) h₁ n) →
        Function.Bijective (KanComplex.π.map (loopSpaceMap f h) h₂ n) := by
    intro a₁ a₂ b₁ b₂ ha hb h₁ h₂ hh
    subst a₂
    subst b₂
    exact hh
  exact transfer ha hb hMap rfl hBottom'

/-- Based positive bijections give bijectivity on all loop components. -/
theorem loopSpaceMap_bijective_piZero_of_based_positive
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y)
    (hπ : Function.Bijective (KanComplex.π.map f h 1)) :
    Function.Bijective (mapπ₀ (loopSpaceMap f h)) := by
  let z := (loopFibrationSequence X x).fiberPoint
  apply (KanComplex.bijective_mapπ₀_iff_bijective_mapπ_zero
    (loopSpaceMap f h) z ((loopSpaceMap f h).app _ z) rfl).mp
  exact loopSpaceMap_bijective_pi_of_based_positive f h z 0 hπ

/-- A strictly pointed map need only be bijective on positive homotopy
groups at its original chosen vertex to be weak on the entire loop space. -/
theorem loopSpaceMap_mem_W_of_based_positive
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y)
    (hπ : ∀ n : ℕ, Function.Bijective (KanComplex.π.map f h (n + 1))) :
    KanComplex.W (loopSpaceMap f h) := by
  rw [KanComplex.W_iff]
  constructor
  · exact loopSpaceMap_bijective_piZero_of_based_positive f h (hπ 0)
  · intro n z
    exact loopSpaceMap_bijective_pi_of_based_positive f h z (n + 1) (hπ (n + 1))

end SSet
