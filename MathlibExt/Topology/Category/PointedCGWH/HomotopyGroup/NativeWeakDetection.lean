/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.NativeLoopWeakDetection
import MathlibExt.Topology.Category.PointedCGWH.Repointing
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne

/-!
# Native weak equivalences from components and all source points

The actual cube-to-singular functions control the component map and every
positive homotopy map at each physical source point. The existing singular
component and fundamental-groupoid criteria give the native CGWH weak class.
The full comparison functions and actual point maps are retained.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial
open scoped CGWH.modelCategory Simplicial

namespace PointedCGWH.NativeAllPointWeakDetectionGeometry
open PointedCGWH.SingularHomotopyGeometry
open PointedCGWH.CubeSingularGeometry
open PointedCGWH.NativeLoopWeakDetectionGeometry

/-- Changing an actual target vertex by its equality retains the whole bijectivity condition. -/
theorem piMapAtTarget_bijective_iff {A D : SSet.{v}}
    (f : A ⟶ D)
    (a : A _⦋0⦌) (d : D _⦋0⦌) (h : f.app _ a = d) (k : ℕ) :
    Function.Bijective (SSet.KanComplex.π.map f h k (x := a)) ↔
      Function.Bijective (SSet.KanComplex.π.map f rfl k (x := a)) := by
  cases h
  rfl

/-- Every actual singular vertex is the original singular image of a given physical point. -/
theorem singularPoint_pointedAt (A : CGWH.{u, v})
    (z : (underlyingSingularFunctor.obj A) _⦋0⦌) :
    singularPoint (PointedCGWH.pointedAt A (TopCat.toSSetObj₀Equiv z)) = z := by
  change TopCat.toSSetObj₀Equiv.symm (TopCat.toSSetObj₀Equiv z) = z
  exact TopCat.toSSetObj₀Equiv.symm_apply_apply z

/-- The actual selected degree-zero cube map controls the entire singular component map. -/
theorem singularComponentMap_bijective {A D : PointedCGWH.{u, v}} (f : A ⟶ D)
    (h₀ : Function.Bijective (piNMap 0 f)) :
    Function.Bijective (SSet.mapπ₀ (singularFunctor.map f)) := by
  have h := (selectedSingularPiMap_bijective_iff 0 f).mpr h₀
  change Function.Bijective
    (SSet.KanComplex.π.map (singularFunctor.map f)
      (singularPoint_naturality f) 0 (x := singularPoint A)) at h
  exact (SSet.KanComplex.bijective_mapπ₀_iff_bijective_mapπ_zero
    (singularFunctor.map f) (singularPoint A) (singularPoint D)
      (singularPoint_naturality f)).mp h

/-- The whole actual singular map of a repointed morphism is its original right map. -/
theorem singularMapAt_value {A D : CGWH.{u, v}} (f : A ⟶ D)
    (a : A) (d : D) (h : f a = d) :
    singularFunctor.map (PointedCGWH.pointedAtMap f a d h) = underlyingSingularFunctor.map f := rfl

/-- The entire pointed singular map retains the same original underlying functor action. -/
theorem singularMap_right_value {A D : PointedCGWH.{u, v}} (f : A ⟶ D) :
    singularFunctor.map f = underlyingSingularFunctor.map f.right := rfl

/-- Equal original whole singular maps preserve the actual complete pi-map condition. -/
theorem piMap_bijective_of_maps_eq {A D : SSet.{v}} (f g : A ⟶ D) (h : f = g)
    (k : ℕ) (a : A _⦋0⦌)
    (hf : Function.Bijective (SSet.KanComplex.π.map f rfl k (x := a))) :
    Function.Bijective (SSet.KanComplex.π.map g rfl k (x := a)) := by
  cases h
  exact hf

/-- The same actual singular source point preserves the full original pi-map condition. -/
theorem piMap_bijective_of_point_eq {A D : SSet.{v}} (f : A ⟶ D) (k : ℕ)
    (a b : A _⦋0⦌) (h : a = b)
    (ha : Function.Bijective (SSet.KanComplex.π.map f rfl k (x := a))) :
    Function.Bijective (SSet.KanComplex.π.map f rfl k (x := b)) := by
  cases h
  exact ha

set_option diagnostics true in
/-- Every physical source point gives the actual singular positive map at its original vertex. -/
theorem singularPositiveMap_bijective {A D : PointedCGWH.{u, v}} (f : A ⟶ D)
    (hπ : ∀ (a : A.right) (n : ℕ),
      Function.Bijective (piNMap (n + 1) (PointedCGWH.pointedAtMap f.right a (f.right a) rfl)))
    (n : ℕ) (z : (singularFunctor.obj A) _⦋0⦌) :
    Function.Bijective
      (SSet.KanComplex.π.map (singularFunctor.map f) rfl (n + 1) (x := z)) := by
  let a : A.right := TopCat.toSSetObj₀Equiv z
  let A' : PointedCGWH.{u, v} := PointedCGWH.pointedAt A.right a
  let D' : PointedCGWH.{u, v} := PointedCGWH.pointedAt D.right (f.right a)
  let g : A' ⟶ D' := PointedCGWH.pointedAtMap f.right a (f.right a) rfl
  have h : Function.Bijective
      (SSet.KanComplex.π.map (singularFunctor.map g)
        (singularPoint_naturality g) (n + 1) (x := singularPoint A')) :=
    (selectedSingularPiMap_bijective_iff (n + 1) g).mpr (hπ a n)
  have h' := (piMapAtTarget_bijective_iff (singularFunctor.map g)
    (singularPoint A') (singularPoint D') (singularPoint_naturality g) (n + 1)).mp h
  have hm : singularFunctor.map g = singularFunctor.map f :=
    (singularMapAt_value f.right a (f.right a) rfl).trans (singularMap_right_value f).symm
  have hActual := piMap_bijective_of_maps_eq _ _ hm (n + 1) (singularPoint A') h'
  exact piMap_bijective_of_point_eq _ (n + 1) (singularPoint A') z
    (singularPoint_pointedAt A.right z) hActual

/-- The real fundamental-groupoid equivalence follows from the actual component and pi-one maps. -/
theorem singularFundamentalGroupoid_isEquivalence {A D : PointedCGWH.{u, v}} (f : A ⟶ D)
    (h₀ : Function.Bijective (piNMap 0 f))
    (hπ : ∀ (a : A.right) (n : ℕ),
      Function.Bijective (piNMap (n + 1) (PointedCGWH.pointedAtMap f.right a (f.right a) rfl))) :
    (SSet.mapFundamentalGroupoid (singularFunctor.map f)).IsEquivalence :=
  (SSet.KanComplex.isEquivalence_mapFundamentalGroupoid_iff
    (singularFunctor.map f)).mpr
      ⟨singularComponentMap_bijective f h₀, fun z => singularPositiveMap_bijective f hπ 0 z⟩

/-- The actual all-point homotopy maps give the full original singular weak condition. -/
theorem singularMap_mem_W {A D : PointedCGWH.{u, v}} (f : A ⟶ D)
    (h₀ : Function.Bijective (piNMap 0 f))
    (hπ : ∀ (a : A.right) (n : ℕ),
      Function.Bijective (piNMap (n + 1) (PointedCGWH.pointedAtMap f.right a (f.right a) rfl))) :
    SSet.KanComplex.W (singularFunctor.map f) :=
  (SSet.KanComplex.W_iff (singularFunctor.map f)).mpr
    ⟨singularComponentMap_bijective f h₀, fun n z => singularPositiveMap_bijective f hπ n z⟩

/-- This is the original CGWH weak class, at every physical source point. -/
theorem weak_of_component_and_all_point_pi {A D : PointedCGWH.{u, v}} (f : A ⟶ D)
    (h₀ : Function.Bijective (piNMap 0 f))
    (hπ : ∀ (a : A.right) (n : ℕ),
      Function.Bijective (piNMap (n + 1) (PointedCGWH.pointedAtMap f.right a (f.right a) rfl))) :
    CGWH.weakHomotopyEquivalences f.right := by
  rw [CGWH.weakHomotopyEquivalences_eq_inverseImage,
    CategoryTheory.MorphismProperty.inverseImage_iff]
  change SSet.KanComplex.W (singularFunctor.map f)
  exact singularMap_mem_W f h₀ hπ

end PointedCGWH.NativeAllPointWeakDetectionGeometry

end
