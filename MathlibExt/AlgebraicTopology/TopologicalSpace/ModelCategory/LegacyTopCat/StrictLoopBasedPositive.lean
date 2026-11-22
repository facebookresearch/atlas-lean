/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopSpaceBasedPositive
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.Comparison.TopCatSingularHomotopyGroup
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.StrictLoopMapWeakHomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.ZerothHomotopyWeakHomotopy

/-!
# Based positive homotopy groups detect weakness of the entire strict loop map

The actual cube-to-singular multiplicative comparison identifies bijectivity
of the positive homotopy-group map at a specified vertex in both directions.
The entire singular-loop Arrow isomorphism then transports the all-component
based-path fibration result to the literal continuous strict loop map.

The hypothesis concerns only positive homotopy groups at the original chosen
point. It asserts no weak equivalence of the original spaces and requires no
information about their unrelated path components. The conclusion concerns
the entire loop space, including its actual path-component map.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Simplicial
open scoped Simplicial Topology

universe u

namespace TopCat

/-- Bijectivity of the actual positive singular homotopy-group map is
equivalent to bijectivity of the actual cube-based map at the same point.
Both directions use the complete multiplicative natural comparison. -/
theorem bijective_singular_positive_piMap_iff
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) (n : ℕ) :
    let _ : SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X
    let _ : SSet.KanComplex (TopCat.toSSet.obj Y) := TopCat.toSSet_obj_kanComplex Y
    Function.Bijective (SSet.KanComplex.π.map (TopCat.toSSet.map f)
      (rfl : (TopCat.toSSet.map f).app _ (TopCat.toSSetObj₀Equiv.symm x) =
        TopCat.toSSetObj₀Equiv.symm (f x)) (n + 1)) ↔
      Function.Bijective (HomotopyGroup.mapHomOfEq f.hom rfl n (x := x)) := by
  dsimp only
  let _ : SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex (TopCat.toSSet.obj Y) := TopCat.toSSet_obj_kanComplex Y
  let eX := homotopyGroupSingularMulEquiv n X x
  let eY := homotopyGroupSingularMulEquiv n Y (f x)
  let a := SSet.KanComplex.π.map (TopCat.toSSet.map f)
    (rfl : (TopCat.toSSet.map f).app _ (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm (f x)) (n + 1)
  let b := HomotopyGroup.mapHomOfEq f.hom rfl n (x := x)
  have hcomm : eY ∘ b = a ∘ eX := by
    funext q
    exact homotopyGroupSingularMulEquiv_naturality n f rfl q
  have hfun : a = eY ∘ b ∘ eX.symm := by
    funext q
    obtain ⟨r, rfl⟩ := eX.surjective q
    simp only [Function.comp_apply, MulEquiv.symm_apply_apply]
    exact (congrFun hcomm r).symm
  change Function.Bijective a ↔ Function.Bijective b
  rw [hfun]
  constructor
  · intro hab
    have hright : Function.Bijective (b ∘ eX.symm) :=
      (Function.Bijective.of_comp_iff' eY.bijective _).mp hab
    exact (Function.Bijective.of_comp_iff _ eX.symm.bijective).mp hright
  · intro hb
    exact eY.bijective.comp (hb.comp eX.symm.bijective)

end TopCat

namespace ContinuousMap

/-- The whole Arrow of the singular strict topological loop map is
isomorphic to the Arrow of the actual simplicial loop-space map. -/
def strictLoopSingularArrowIso
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    Arrow.mk (TopCat.toSSet.map (TopCat.ofHom (strictLoopMap f x))) ≅
      Arrow.mk (SSet.loopSpaceMap
        (x := TopCat.toSSetObj₀Equiv.symm x)
        (y := TopCat.toSSetObj₀Equiv.symm (f x))
        (TopCat.toSSet.map (TopCat.ofHom f)) rfl) :=
  Arrow.isoMk (SSet.singularLoopIso X x) (SSet.singularLoopIso Y (f x))
    (SSet.singularLoopIso_hom_naturality f x).symm

/-- The forward source component is the genuine singular-loop isomorphism. -/
@[simp]
theorem strictLoopSingularArrowIso_hom_left
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    (strictLoopSingularArrowIso f x).hom.left = (SSet.singularLoopIso X x).hom := rfl

/-- The forward target component is the genuine target singular-loop isomorphism. -/
@[simp]
theorem strictLoopSingularArrowIso_hom_right
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    (strictLoopSingularArrowIso f x).hom.right =
      (SSet.singularLoopIso Y (f x)).hom := rfl

/-- The inverse source component retains the actual inverse singular-loop map. -/
@[simp]
theorem strictLoopSingularArrowIso_inv_left
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    (strictLoopSingularArrowIso f x).inv.left = (SSet.singularLoopIso X x).inv := rfl

/-- The inverse target component retains the actual inverse singular-loop map. -/
@[simp]
theorem strictLoopSingularArrowIso_inv_right
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    (strictLoopSingularArrowIso f x).inv.right =
      (SSet.singularLoopIso Y (f x)).inv := rfl

/-- Positive cube-based bijections at the original point imply actual weak
equivalence of the strict loop map on all components. -/
theorem strictLoopMap_mem_weakHomotopyEquivalences_of_based_positive
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X)
    (hπ : ∀ n : ℕ,
      Function.Bijective (HomotopyGroup.mapHomOfEq f rfl n (x := x))) :
    TopCat.weakHomotopyEquivalences (TopCat.ofHom (strictLoopMap f x)) := by
  let _ : SSet.KanComplex (TopCat.toSSet.obj (TopCat.of X)) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex (TopCat.toSSet.obj (TopCat.of Y)) :=
    TopCat.toSSet_obj_kanComplex _
  have hSing : ∀ n : ℕ, Function.Bijective (SSet.KanComplex.π.map
      (TopCat.toSSet.map (TopCat.ofHom f))
      (rfl : (TopCat.toSSet.map (TopCat.ofHom f)).app _
        (TopCat.toSSetObj₀Equiv.symm x) = TopCat.toSSetObj₀Equiv.symm (f x)) (n + 1)) := by
    intro n
    exact (TopCat.bijective_singular_positive_piMap_iff (TopCat.ofHom f) x n).mpr (hπ n)
  have hLoop : SSet.KanComplex.W (SSet.loopSpaceMap
      (x := TopCat.toSSetObj₀Equiv.symm x)
      (y := TopCat.toSSetObj₀Equiv.symm (f x))
      (TopCat.toSSet.map (TopCat.ofHom f)) rfl) :=
    SSet.loopSpaceMap_mem_W_of_based_positive _ rfl hSing
  rw [TopCat.mem_weakHomotopyEquivalences_iff]
  exact (MorphismProperty.arrow_mk_iso_iff SSet.KanComplex.W
    (strictLoopSingularArrowIso f x)).mpr hLoop

/-- The conclusion includes bijectivity of the actual map on all path
components of the strict topological loop space. -/
theorem strictLoopMap_bijective_piZero_of_based_positive
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X)
    (hπ : ∀ n : ℕ,
      Function.Bijective (HomotopyGroup.mapHomOfEq f rfl n (x := x))) :
    Function.Bijective (TopCat.zerothHomotopyMap (TopCat.ofHom (strictLoopMap f x))) := by
  have h := strictLoopMap_mem_weakHomotopyEquivalences_of_based_positive f x hπ
  exact h.bijective_zerothHomotopyMap

end ContinuousMap
