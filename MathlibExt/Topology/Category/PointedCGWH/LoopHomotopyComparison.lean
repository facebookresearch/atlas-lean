/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.StrictLoopBasedPositive
import MathlibExt.Topology.Category.PointedCGWH.LoopComparison
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CompactlyGeneratedCoreflectionWeakHomotopy
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHHomotopyGroupInvariance

/-!
# Literal native loop comparison and based positive homotopy groups

Retain the full original selected-point transport and strict-loop Arrow
isomorphism. The native compact-open comparison and compact-generation
counit give the actual singular isomorphism and weakness of the original
loop landing. Based positive bijections then make the full native one-sphere
internal-Hom map weak, including every loop component. The subsequent
original stable-K successor application has separate source scope.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped MonoidalClosed CGWH.modelCategory Simplicial Topology

namespace PointedCGWH.LoopGeometry

/-- The whole loop-space homeomorphism induced by equality of the chosen
point. It changes no underlying loop function. -/
def loopPointEqHomeomorph {X : Type v} [TopologicalSpace X]
    {x y : X} (h : x = y) : LoopSpace X x ≃ₜ LoopSpace X y := by
  subst y
  exact Homeomorph.refl _

/-- Point transport retains every evaluation of the underlying loop. -/
@[simp]
theorem loopPointEqHomeomorph_apply_eval {X : Type v} [TopologicalSpace X]
    {x y : X} (h : x = y) (gamma : LoopSpace X x) (t : unitInterval) :
    loopPointEqHomeomorph h gamma t = gamma t := by
  subst y
  rfl

/-- Inverse point transport retains every evaluation as well. -/
@[simp]
theorem loopPointEqHomeomorph_symm_apply_eval {X : Type v} [TopologicalSpace X]
    {x y : X} (h : x = y) (gamma : LoopSpace X y) (t : unitInterval) :
    (loopPointEqHomeomorph h).symm gamma t = gamma t := by
  subst y
  rfl

/-- The same point transport as a whole isomorphism of bundled loop spaces. -/
def loopPointEqIso (X : TopCat.{v}) {x y : X} (h : x = y) :
    TopCat.of (LoopSpace X x) ≅ TopCat.of (LoopSpace X y) :=
  TopCat.isoOfHomeo (loopPointEqHomeomorph h)

/-- The whole Arrow of the raw image-point strict loop map is identified
with the original pointed compact-open strict loop map. -/
def rawStrictLoopArrowIso {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    Arrow.mk (TopCat.ofHom (ContinuousMap.strictLoopMap
      (CGWH.cgwhToTop.map f.right).hom (PointedCGWH.underlyingBasepoint X))) ≅
      Arrow.mk (TopCat.ofHom (PointedCGWH.strictLoopMap f)) := by
  let e := loopPointEqIso (CGWH.cgwhToTop.obj Y.right)
    (PointedCGWH.underlyingBasepoint_naturality f)
  refine Arrow.isoMk (Iso.refl _) e ?_
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro gamma
  apply Path.ext
  funext t
  change PointedCGWH.strictLoopMap f gamma t =
    loopPointEqHomeomorph (PointedCGWH.underlyingBasepoint_naturality f)
      (ContinuousMap.strictLoopMap
        (CGWH.cgwhToTop.map f.right).hom (PointedCGWH.underlyingBasepoint X) gamma) t
  rw [loopPointEqHomeomorph_apply_eval]
  rfl

/-- The forward source component is the identity on the whole raw loop space. -/
@[simp]
theorem rawStrictLoopArrowIso_hom_left {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (rawStrictLoopArrowIso f).hom.left = 𝟙 _ := rfl

/-- The forward target component is the actual selected-point transport. -/
@[simp]
theorem rawStrictLoopArrowIso_hom_right {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (rawStrictLoopArrowIso f).hom.right =
      (loopPointEqIso (CGWH.cgwhToTop.obj Y.right)
        (PointedCGWH.underlyingBasepoint_naturality f)).hom := rfl

/-- The inverse source component is the identity on the whole raw loop space. -/
@[simp]
theorem rawStrictLoopArrowIso_inv_left {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (rawStrictLoopArrowIso f).inv.left = 𝟙 _ := rfl

/-- The inverse target component is the inverse of the same point transport. -/
@[simp]
theorem rawStrictLoopArrowIso_inv_right {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (rawStrictLoopArrowIso f).inv.right =
      (loopPointEqIso (CGWH.cgwhToTop.obj Y.right)
        (PointedCGWH.underlyingBasepoint_naturality f)).inv := rfl

/-- The exact target homotopy-group equivalence from the original pointed
basepoint to the literal image of the original source point. -/
def piNTargetPointEquiv (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    PointedCGWH.piN (n + 1) Y ≃
      HomotopyGroup.Pi (n + 1) (CGWH.cgwhToTop.obj Y.right)
        ((CGWH.cgwhToTop.map f.right).hom (PointedCGWH.underlyingBasepoint X)) :=
  Equiv.cast (congrArg
    (fun y => HomotopyGroup.Pi (n + 1) (CGWH.cgwhToTop.obj Y.right) y)
    (PointedCGWH.underlyingBasepoint_naturality f).symm)

/-- The entire original positive-degree map equals raw postcomposition
after the exact target-point transport, on its whole source domain. -/
theorem piNMap_eq_raw_transport (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    piNTargetPointEquiv n f ∘ PointedCGWH.piNMap (n + 1) f =
      HomotopyGroup.mapHomOfEq (CGWH.cgwhToTop.map f.right).hom rfl n
        (x := PointedCGWH.underlyingBasepoint X) := by
  funext a
  change Eq.mp _ (PointedCGWH.piNMap (n + 1) f a) = _
  rw [PointedCGWH.piNMap_apply, HomotopyGroup.mapHomOfEq_apply]

/-- Bijectivity of the original native positive map is exactly bijectivity
of raw postcomposition at the original chosen point. -/
theorem piNMap_bijective_iff_raw (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    Function.Bijective (PointedCGWH.piNMap (n + 1) f) ↔
      Function.Bijective (HomotopyGroup.mapHomOfEq
        (CGWH.cgwhToTop.map f.right).hom rfl n
        (x := PointedCGWH.underlyingBasepoint X)) := by
  rw [← piNMap_eq_raw_transport n f]
  exact (Function.Bijective.of_comp_iff' (piNTargetPointEquiv n f).bijective _).symm

/-- Original native based positive bijections make the actual compact-open
pointed loop map weak on every component. -/
theorem strictLoopMap_weak_of_basedPositive
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hπ : ∀ n : ℕ, Function.Bijective (PointedCGWH.piNMap (n + 1) f)) :
    TopCat.weakHomotopyEquivalences (TopCat.ofHom (PointedCGWH.strictLoopMap f)) := by
  have hraw := ContinuousMap.strictLoopMap_mem_weakHomotopyEquivalences_of_based_positive
    (CGWH.cgwhToTop.map f.right).hom (PointedCGWH.underlyingBasepoint X)
    (fun n => (piNMap_bijective_iff_raw n f).mp (hπ n))
  exact (TopCat.weakHomotopyEquivalences.arrow_mk_iso_iff
    (rawStrictLoopArrowIso f)).mp hraw

/-- The actual native loop landing becomes an isomorphism after singular
complexes. Its source comparison is the native compact-open NatIso and its
target comparison is the real compact-generation counit. -/
theorem loopLanding_singular_isIso (X : PointedCGWH.{u, v}) :
    IsIso (TopCat.toSSet.map (PointedCGWH.loopLanding X)) := by
  let a := CGWH.cgwhToTop.map
    (PointedCGWH.loopIsoCompactOpenCoreflection.hom.app X).right
  let Raw := (Arrow.mk (PointedCGWH.loopLanding X)).right
  let c := CompactlyGenerated.adj.{u, v}.counit.app Raw
  let e := TopCat.toSSet.mapIso (CGWH.cgwhToTop.mapIso
    (PointedCGWH.pointedToCGWH.mapIso
      (PointedCGWH.loopIsoCompactOpenCoreflection.app X)))
  have he : e.hom = TopCat.toSSet.map a := rfl
  let hA : IsIso (TopCat.toSSet.map a) := by
    rw [← he]
    infer_instance
  let hC : IsIso (TopCat.toSSet.map c) :=
    TopCat.toSSet_map_compactlyGeneratedAdjCounit_isIso _
  let ea := @asIso _ _ _ _ (TopCat.toSSet.map a) hA
  let ec := @asIso _ _ _ _ (TopCat.toSSet.map c) hC
  let eComp := ea ≪≫ ec
  erw [PointedCGWH.loopLanding, TopCat.toSSet.map_comp]
  change IsIso (TopCat.toSSet.map a ≫ TopCat.toSSet.map c)
  exact (inferInstance : IsIso eComp.hom)

/-- The real native loop landing is weak on all components. -/
theorem loopLanding_weak (X : PointedCGWH.{u, v}) :
    TopCat.weakHomotopyEquivalences (PointedCGWH.loopLanding X) := by
  rw [TopCat.mem_weakHomotopyEquivalences_iff]
  let Source := (Arrow.mk (PointedCGWH.loopLanding X)).left
  let Raw := (Arrow.mk (PointedCGWH.loopLanding X)).right
  let _ : SSet.KanComplex (TopCat.toSSet.obj Source) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex (TopCat.toSSet.obj Raw) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : IsIso (TopCat.toSSet.map (PointedCGWH.loopLanding X)) :=
    loopLanding_singular_isIso X
  let e : TopCat.toSSet.obj Source ≅ TopCat.toSSet.obj Raw :=
    asIso (TopCat.toSSet.map (PointedCGWH.loopLanding X))
  exact SSet.KanComplex.W.ofIso e

/-- Original based positive bijections make the same actual native loop map
weak on all components, by cancellation of the genuine landing comparison. -/
theorem loopMap_weak_of_basedPositive
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hπ : ∀ n : ℕ, Function.Bijective (PointedCGWH.piNMap (n + 1) f)) :
    CGWH.weakHomotopyEquivalences (PointedCGWH.loop.map f).right := by
  rw [CGWH.weakHomotopyEquivalences_eq_inverseImage, MorphismProperty.inverseImage_iff,
    TopCat.mem_weakHomotopyEquivalences_iff]
  have hX := (TopCat.mem_weakHomotopyEquivalences_iff _).mp (loopLanding_weak X)
  have hY := (TopCat.mem_weakHomotopyEquivalences_iff _).mp (loopLanding_weak Y)
  have hraw := (TopCat.mem_weakHomotopyEquivalences_iff _).mp
    (strictLoopMap_weak_of_basedPositive f hπ)
  have hSquare :
      TopCat.toSSet.map (CGWH.cgwhToTop.map (PointedCGWH.loop.map f).right) ≫
          TopCat.toSSet.map (PointedCGWH.loopLanding Y) =
        TopCat.toSSet.map (PointedCGWH.loopLanding X) ≫
          TopCat.toSSet.map (TopCat.ofHom (PointedCGWH.strictLoopMap f)) :=
    (TopCat.toSSet.map_comp
      (CGWH.cgwhToTop.map (PointedCGWH.loop.map f).right)
      (PointedCGWH.loopLanding Y)).symm.trans
        ((TopCat.toSSet.congr_map (PointedCGWH.loopLanding_naturality f)).trans
          (TopCat.toSSet.map_comp (PointedCGWH.loopLanding X)
            (TopCat.ofHom (PointedCGWH.strictLoopMap f))))
  apply SSet.KanComplex.W.of_postcomp hY
  exact (congrArg (fun g => SSet.KanComplex.W g) hSquare).mpr
    (SSet.KanComplex.W.comp hX hraw)

/-- The conclusion is weakness of the original one-sphere internal-Hom
map, with its original pointed source and target. -/
theorem ihomSphereOne_weak_of_basedPositive
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hπ : ∀ n : ℕ, Function.Bijective (PointedCGWH.piNMap (n + 1) f)) :
    weakEquivalences PointedCGWH.{u, v}
      ((ihom PointedCGWH.sphereOne).map f) := by
  apply (HomotopicalAlgebra.weakEquivalence_iff _).mp
  apply (PointedCGWH.weakEquivalence_iff _).mpr
  apply (HomotopicalAlgebra.weakEquivalence_iff _).mpr
  exact loopMap_weak_of_basedPositive f hπ

/-- The original one-sphere internal-Hom conclusion includes its actual
zeroth-homotopy map on every path component. -/
theorem ihomSphereOne_pi0_bijective_of_basedPositive
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hπ : ∀ n : ℕ, Function.Bijective (PointedCGWH.piNMap (n + 1) f)) :
    Function.Bijective (TopCat.zerothHomotopyMap
      (CGWH.cgwhToTop.map ((ihom PointedCGWH.sphereOne).map f).right)) := by
  have h := loopMap_weak_of_basedPositive f hπ
  rw [CGWH.weakHomotopyEquivalences_eq_inverseImage, MorphismProperty.inverseImage_iff] at h
  exact h.bijective_zerothHomotopyMap

end PointedCGWH.LoopGeometry
