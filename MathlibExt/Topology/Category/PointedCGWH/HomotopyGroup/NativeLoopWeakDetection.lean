/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AllLoopPointGeometry
import MathlibExt.Topology.Category.PointedCGWH.Singular.CubeHomotopyComparison
import MathlibExt.Topology.Category.PointedCGWH.Singular.LoopComparison
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.NativeLoopShift

/-!
# GENUINE original native-loop weak detection from selected positive maps

The actual original cube-singular NatIso and native singular-loop NatIso
retain every full function, source/target point and input-map square.
The original based-path ALL-loop-point theorem therefore proves a genuine
weak detector for the actual native loop.map. The SAME CGWH weak class is
used through its real singular definition. Selected positive homotopy is
sufficient here because every point of the loop-map source is discharged
by original based-path geometry. No arbitrary unlooped-space detector,
alternative carrier, incoming weak law or stable model is assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial
open scoped CGWH.modelCategory Simplicial

namespace PointedCGWH.NativeLoopWeakDetectionGeometry
open PointedCGWH.SingularHomotopyGeometry
open PointedCGWH.CubeSingularGeometry
open PointedCGWH.NativeLoopShiftGeometry

/-- BOTH original selected singular pi comparison functions retain the actual cube maps. -/
def selectedSingularPiIso (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hπ : Function.Bijective (piNMap n f)) : (piFunctor n).obj X ≅ (piFunctor n).obj Y :=
  ((cubeSingularNatIso n).app X).symm ≪≫ (Equiv.ofBijective (piNMap n f) hπ).toIso ≪≫
    (cubeSingularNatIso n).app Y

/-- The ENTIRE original comparison hom is the actual same selected singular pi map. -/
theorem selectedSingularPiIso_hom (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hπ : Function.Bijective (piNMap n f)) :
    (selectedSingularPiIso n f hπ).hom = (piFunctor n).map f :=
  (Iso.inv_comp_eq ((cubeSingularNatIso n).app X)).mpr
    ((cubeSingularNatIso n).hom.naturality f)

/-- The ENTIRE original inverse keeps BOTH cube-singular maps and actual chosen pi inverse. -/
theorem selectedSingularPiIso_inv (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hπ : Function.Bijective (piNMap n f)) :
    (selectedSingularPiIso n f hπ).inv = (cubeSingularNatIso n).inv.app Y ≫
      (Equiv.ofBijective (piNMap n f) hπ).toIso.inv ≫ (cubeSingularNatIso n).hom.app X := rfl

/-- The SAME full original cube-singular NatIso detects bijections in either direction. -/
theorem selectedSingularPiMap_bijective_iff (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    Function.Bijective ((piFunctor n).map f) ↔ Function.Bijective (piNMap n f) :=
  (CategoryTheory.isIso_iff_bijective ((piFunctor n).map f)).symm.trans
    ((NatIso.isIso_map_iff (cubeSingularNatIso n) f).symm.trans
      (CategoryTheory.isIso_iff_bijective ((piNFunctor n).map f)))

/-- The actual native and strict singular-loop maps have the SAME original full weak condition. -/
theorem nativeLoopSingularMap_W_iff {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    SSet.KanComplex.W (nativeLoopSingularFunctor.map f) ↔
      SSet.KanComplex.W (strictLoopSingularFunctor.map f) := by
  have hx := SSet.KanComplex.W.ofIso (nativeLoopSingularIso X)
  have hy := SSet.KanComplex.W.ofIso (nativeLoopSingularIso Y)
  have h := nativeLoopSingularIso_naturality f
  constructor
  · intro hw
    exact SSet.KanComplex.W.of_precomp hx (h ▸ SSet.KanComplex.W.comp hw hy)
  · intro hw
    exact SSet.KanComplex.W.of_postcomp hy (h.symm ▸ SSet.KanComplex.W.comp hx hw)

/-- The original native loop weak class is its ACTUAL full strict singular-loop class. -/
theorem nativeLoopMap_weak_iff_strict {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    CGWH.weakHomotopyEquivalences (PointedCGWH.loop.map f).right ↔
      SSet.KanComplex.W (strictLoopSingularFunctor.map f) := by
  rw [CGWH.weakHomotopyEquivalences_eq_inverseImage,
    CategoryTheory.MorphismProperty.inverseImage_iff]
  change SSet.KanComplex.W (nativeLoopSingularFunctor.map f) ↔ _
  exact nativeLoopSingularMap_W_iff f

/-- GENUINE selected-base positive tests detect the SAME entire original native loop weak map. -/
theorem nativeLoopMap_weak_iff_based {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    CGWH.weakHomotopyEquivalences (PointedCGWH.loop.map f).right ↔
      ∀ n : ℕ, Function.Bijective (piNMap (n + 1) f) := by
  apply (nativeLoopMap_weak_iff_strict f).trans
  constructor
  · intro hw n
    have hs := (SSet.OriginalAllLoopPointGeometry.loopMap_W_iff_base
      (singularFunctor.map f) (singularPoint_naturality f)).mp hw n
    exact (selectedSingularPiMap_bijective_iff (n + 1) f).mp hs
  · intro hp
    exact SSet.loopSpaceMap_mem_W_of_based_positive
      (singularFunctor.map f) (singularPoint_naturality f)
        (fun n => (selectedSingularPiMap_bijective_iff (n + 1) f).mpr (hp n))

/-- EVERY actual native singular-loop vertex has the original full bijective homotopy map. -/
theorem nativeLoopSingularMap_pi_bijective_of_based {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hπ : ∀ n : ℕ, Function.Bijective (piNMap (n + 1) f))
    (z : (nativeLoopSingularFunctor.obj X) _⦋0⦌) (n : ℕ) :
    Function.Bijective (SSet.KanComplex.π.map (nativeLoopSingularFunctor.map f) rfl n (x := z)) :=
  ((nativeLoopSingularMap_W_iff f).mpr
    (SSet.loopSpaceMap_mem_W_of_based_positive
      (singularFunctor.map f) (singularPoint_naturality f)
        (fun k => (selectedSingularPiMap_bijective_iff (k + 1) f).mpr (hπ k)))).bijective_piMap n z

/-- The ACTUAL original native loop functor preserves the SAME full original weak class. -/
theorem nativeLoopMap_preserves_weak {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hw : CGWH.weakHomotopyEquivalences f.right) :
    CGWH.weakHomotopyEquivalences (PointedCGWH.loop.map f).right := by
  have hs : SSet.KanComplex.W (singularFunctor.map f) := by
    rw [CGWH.weakHomotopyEquivalences_eq_inverseImage,
      CategoryTheory.MorphismProperty.inverseImage_iff] at hw
    exact hw
  exact (nativeLoopMap_weak_iff_strict f).mpr (hs.loopSpaceMap (singularPoint_naturality f))

/-- The SAME original weak class gives its actual selected positive pi bijections. -/
theorem weakMap_selectedPositivePi_bijective {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hw : CGWH.weakHomotopyEquivalences f.right) (n : ℕ) :
    Function.Bijective (piNMap (n + 1) f) :=
  (nativeLoopMap_weak_iff_based f).mp (nativeLoopMap_preserves_weak f hw) n

end PointedCGWH.NativeLoopWeakDetectionGeometry
