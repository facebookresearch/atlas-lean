/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.DoubleMappingCylinderOpenCharts
public import MathlibExt.Topology.Category.TopCat.TrivialCofibrationExtension

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The original cofibration pair in the actual open collar

The same original cylinder path from height one to one half lies in V.
The existing HEP retunes the original B→V map so its restriction to X is
exactly the PUBLIC overlap midpoint. The retuned map is weak by the original
V/B deformation and that actual homotopy. No retuned map, weak equivalence,
source-family or coefficient calibration is an input.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra AlgebraicTopology
open scoped TopCat.modelCategory

universe u

namespace TopCat

private def retunedMidpointTime : TopCat.I.{u} :=
  (TopCat.I.homeomorph.{u}).symm (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval)

private theorem midpointCurve_mem_openB
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (s : unitInterval) (x : X) :
    doubleMappingCylinderMiddle i f
      (x, mappingCylinderInterpolate retunedMidpointTime s (1 : TopCat.I.{u})) ∈
        doubleMappingCylinderOpenB i f := by
  rw [mem_doubleMappingCylinderOpenB, doubleMappingCylinderHeight_middle,
    mappingCylinderInterpolate_height, TopCat.I.homeomorph_one,
    retunedMidpointTime, (TopCat.I.homeomorph.{u}).apply_symm_apply]
  change 1 / 3 < (1 - (s : ℝ)) * (1 : ℝ) + (s : ℝ) * (1 / 2 : ℝ)
  nlinarith [s.2.2]

private theorem boundaryEndpoint_value
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (t : TopCat.I.{u})
    (c : X ⟶ TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)))
    (hc : c ≫ subspaceIncl (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) =
      mappingCylinderEndpoint X t ≫ doubleMappingCylinderMiddle i f) (x : X) :
    (c.hom x).1 = doubleMappingCylinderMiddle i f (x, t) := by
  have hL : (c ≫ subspaceIncl
      (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f))).hom x = (c.hom x).1 :=
    congrArg (fun k : C(X, doubleMappingCylinder i f) => k x)
      (TopCat.hom_comp c (subspaceIncl
        (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f))))
  have hR : (mappingCylinderEndpoint X t ≫ doubleMappingCylinderMiddle i f).hom x =
      doubleMappingCylinderMiddle i f (x, t) :=
    (congrArg (fun k : C(X, doubleMappingCylinder i f) => k x)
      (TopCat.hom_comp (mappingCylinderEndpoint X t) (doubleMappingCylinderMiddle i f))).trans
        (congrArg (fun p : mappingCylinderDomain X => doubleMappingCylinderMiddle i f p)
          (mappingCylinderEndpoint_apply X t x))
  exact hL.symm.trans
    ((congrArg (fun k : X ⟶ doubleMappingCylinder i f => k.hom x) hc).trans hR)

/-- The whole original X boundary homotopy inside the same V, from the
original B endpoint to the original PUBLIC overlap midpoint. -/
public def doubleMappingCylinderMidpointBoundaryHomotopy
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.Homotopy (i ≫ doubleMappingCylinderBToOpenB i f)
      (doubleMappingCylinderMidpoint i f ≫ doubleMappingCylinderOverlapToOpenB i f) where
  toFun z := ⟨doubleMappingCylinderMiddle i f
    (z.2, mappingCylinderInterpolate retunedMidpointTime z.1 (1 : TopCat.I.{u})),
    midpointCurve_mem_openB i f z.1 z.2⟩
  continuous_toFun := ((doubleMappingCylinderMiddle i f).hom.continuous.comp
    (continuous_snd.prodMk ((continuous_mappingCylinderInterpolate retunedMidpointTime).comp
      (continuous_fst.prodMk continuous_const)))).subtype_mk _
  map_zero_left x := by
    have hc : (i ≫ doubleMappingCylinderBToOpenB i f) ≫
        subspaceIncl (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) =
        mappingCylinderEndpoint X 1 ≫ doubleMappingCylinderMiddle i f :=
      (Category.assoc i (doubleMappingCylinderBToOpenB i f) _).trans
        ((congrArg (fun k : B ⟶ doubleMappingCylinder i f => i ≫ k)
          (doubleMappingCylinderBToOpenB_inclusion i f)).trans (doubleMappingCylinder_one i f).symm)
    have hCurve : doubleMappingCylinderMiddle i f
        (x, mappingCylinderInterpolate retunedMidpointTime 0 (1 : TopCat.I.{u})) =
        doubleMappingCylinderMiddle i f (x, (1 : TopCat.I.{u})) :=
      congrArg (fun t : TopCat.I.{u} => doubleMappingCylinderMiddle i f (x, t))
        (mappingCylinderInterpolate_zero retunedMidpointTime (1 : TopCat.I.{u}))
    apply Subtype.ext
    exact hCurve.trans
      (boundaryEndpoint_value i f 1 (i ≫ doubleMappingCylinderBToOpenB i f) hc x).symm
  map_one_left x := by
    have hc : (doubleMappingCylinderMidpoint i f ≫ doubleMappingCylinderOverlapToOpenB i f) ≫
        subspaceIncl (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) =
        mappingCylinderEndpoint X retunedMidpointTime ≫ doubleMappingCylinderMiddle i f :=
      (Category.assoc (doubleMappingCylinderMidpoint i f)
        (doubleMappingCylinderOverlapToOpenB i f) _).trans
        ((congrArg (fun k : TopCat.of
            (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) ⟶
            doubleMappingCylinder i f => doubleMappingCylinderMidpoint i f ≫ k)
          (doubleMappingCylinderOverlapToOpenB_inclusion i f)).trans
            (doubleMappingCylinderMidpoint_inclusion i f))
    have hCurve : doubleMappingCylinderMiddle i f
        (x, mappingCylinderInterpolate retunedMidpointTime 1 (1 : TopCat.I.{u})) =
        doubleMappingCylinderMiddle i f (x, retunedMidpointTime) :=
      congrArg (fun t : TopCat.I.{u} => doubleMappingCylinderMiddle i f (x, t))
        (mappingCylinderInterpolate_one retunedMidpointTime (1 : TopCat.I.{u}))
    apply Subtype.ext
    exact hCurve.trans
      (boundaryEndpoint_value i f retunedMidpointTime
        (doubleMappingCylinderMidpoint i f ≫ doubleMappingCylinderOverlapToOpenB i f) hc x).symm

/-- Computed HEP data, retaining the entire original X family at every
time. The source equation uses the same PUBLIC midpoint and overlap map. -/
public structure DoubleMappingCylinderRetunedBData
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) where
  /-- The map from B to its open cylinder chart obtained by homotopy extension. -/
  map : B ⟶ TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f))
  /-- The homotopy from the original B chart inclusion to the retuned map. -/
  homotopy : TopCat.Homotopy (doubleMappingCylinderBToOpenB i f) map
  source : i ≫ map = doubleMappingCylinderMidpoint i f ≫ doubleMappingCylinderOverlapToOpenB i f
  source_family : ∀ s : unitInterval, ∀ x : X,
    homotopy (s, i x) = doubleMappingCylinderMidpointBoundaryHomotopy i f (s, x)

private theorem nonempty_doubleMappingCylinderRetunedBData
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i] (f : X ⟶ H) :
    Nonempty (DoubleMappingCylinderRetunedBData i f) := by
  obtain ⟨g, K, hg, hK⟩ := exists_homotopyExtension_of_cofibration i
    (doubleMappingCylinderBToOpenB i f)
    (doubleMappingCylinderMidpoint i f ≫ doubleMappingCylinderOverlapToOpenB i f)
    (doubleMappingCylinderMidpointBoundaryHomotopy i f)
  exact ⟨{
    map := g
    homotopy := K
    source := hg
    source_family := hK }⟩

/-- The actual retuned B map is computed solely from the genuine i HEP. -/
public def doubleMappingCylinderRetunedBData
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i] (f : X ⟶ H) :
    DoubleMappingCylinderRetunedBData i f :=
  Classical.choice (nonempty_doubleMappingCylinderRetunedBData i f)

/-- The original B leg retuned to the collar midpoint along its whole source inclusion. -/
public def doubleMappingCylinderRetunedB
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i] (f : X ⟶ H) :
    B ⟶ TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) :=
  (doubleMappingCylinderRetunedBData i f).map

@[reassoc]
public theorem doubleMappingCylinderRetunedB_source
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i] (f : X ⟶ H) :
    i ≫ doubleMappingCylinderRetunedB i f =
      doubleMappingCylinderMidpoint i f ≫ doubleMappingCylinderOverlapToOpenB i f :=
  (doubleMappingCylinderRetunedBData i f).source

/-- The SAME retuned map is weak by the actual original collar
deformation and its HEP homotopy. No weak witness is input. -/
public theorem doubleMappingCylinderRetunedB_mem_weakHomotopyEquivalences
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i] (f : X ⟶ H) :
    TopCat.weakHomotopyEquivalences (doubleMappingCylinderRetunedB i f) := by
  let a := doubleMappingCylinderBToOpenB i f
  let r := doubleMappingCylinderOpenBRetraction i f
  have hr : TopCat.weakHomotopyEquivalences r :=
    doubleMappingCylinderOpenBRetraction_mem_weakHomotopyEquivalences i f
  have hComp : TopCat.weakHomotopyEquivalences (a ≫ r) := by
    rw [doubleMappingCylinderBToOpenB_retraction]
    exact TopCat.weakHomotopyEquivalences.of_isIso _
  have ha : TopCat.weakHomotopyEquivalences a :=
    TopCat.weakHomotopyEquivalences.of_postcomp _ _ hr hComp
  exact (weakHomotopyEquivalences_iff_of_homotopy
    (doubleMappingCylinderRetunedBData i f).homotopy).mp ha

end TopCat

end
