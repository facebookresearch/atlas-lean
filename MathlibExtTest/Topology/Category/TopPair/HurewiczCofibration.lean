/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.HurewiczCofibration
public import MathlibExt.Topology.Category.TopPair.IntervalBoundaryNDR

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Topology
open scoped unitInterval

universe u v

namespace MathlibExtTest.Topology.Category.TopPair.HurewiczCofibration

variable {P : _root_.TopPair.{u}}

example (t : _root_.TopCat.I.{u}) (a : P.snd) :
    _root_.TopPair.hurewiczCylinderSidePoint P t a ∈
      _root_.TopPair.hurewiczCylinderSide P :=
  _root_.TopPair.hurewiczCylinderSidePoint_mem P t a

example (x : P.fst) :
    _root_.TopPair.hurewiczCylinderBottomPoint P x ∈
      _root_.TopPair.hurewiczCylinderBottom P :=
  _root_.TopPair.hurewiczCylinderBottomPoint_mem P x

example :
    Nonempty (_root_.TopPair.HurewiczCofibrationData P) ↔
      IsClosedEmbedding P.map ∧
        _root_.TopCat.IsHurewiczCofibration P.map :=
  _root_.TopPair.hurewiczCofibrationData_iff P

example (hclosed : IsClosedEmbedding P.map)
    (hhep : _root_.TopCat.IsHurewiczCofibration P.map) :
    _root_.TopPair.HurewiczCofibrationData P :=
  _root_.TopPair.HurewiczCofibrationData.ofIsClosedEmbeddingOfHEP hclosed hhep

section CrossUniverse

variable {Y : Type v} [TopologicalSpace Y]
variable (d : _root_.TopPair.HurewiczCofibrationData P)
variable (f : C(P.fst, Y)) (H : C(unitInterval × P.snd, Y))
variable (h0 : ∀ a, H (0, a) = f (P.map a))

example : _root_.Topology.HomotopyExtensionData P.map.hom f H h0 :=
  d.homotopyExtension f H h0

example : _root_.Topology.HasHomotopyExtensionProperty.{u, v} P.map.hom :=
  d.hasHomotopyExtensionProperty

end CrossUniverse

section Behavioral

private def ibMid : _root_.TopCat.I.{u} :=
  _root_.TopCat.I.homeomorph.symm ⟨1 / 2, by norm_num⟩

private def ibZero : (_root_.TopPair.intervalBoundaryPair.{u}).snd :=
  ⟨0, by simp [_root_.TopPair.topCatIntervalBoundary]⟩

private noncomputable def ibHData :
    _root_.TopPair.HurewiczCofibrationData
      (_root_.TopPair.intervalBoundaryPair.{u}) :=
  _root_.TopPair.intervalBoundaryNDRData.toStandard.hurewiczCofibrationData

/-- The cylinder retraction fixes a concrete side point. -/
example :
    ibHData.cylinderRetraction
        ((_root_.TopPair.hurewiczCylinderPair _).map
          (_root_.TopPair.hurewiczCylinderSidePoint _ ibMid ibZero)) =
      _root_.TopPair.hurewiczCylinderSidePoint _ ibMid ibZero :=
  ibHData.cylinderRetraction_boundary _

/-- The cylinder retraction fixes a concrete bottom point. -/
example :
    ibHData.cylinderRetraction
        ((_root_.TopPair.hurewiczCylinderPair _).map
          (_root_.TopPair.hurewiczCylinderBottomPoint _ ibMid)) =
      _root_.TopPair.hurewiczCylinderBottomPoint _ ibMid :=
  ibHData.cylinderRetraction_boundary _

/-- A nonconstant side homotopy: projection to the time coordinate. -/
private noncomputable def ibSide :
    C(unitInterval × (_root_.TopPair.intervalBoundaryPair.{u}).snd, ℝ) :=
  ⟨fun p => (p.1 : ℝ), continuous_subtype_val.comp continuous_fst⟩

private noncomputable def ibBase :
    C((_root_.TopPair.intervalBoundaryPair.{u}).fst, ℝ) :=
  ContinuousMap.const _ 0

private theorem ibH0
    (a : (_root_.TopPair.intervalBoundaryPair.{u}).snd) :
    ibSide (0, a) =
      ibBase ((_root_.TopPair.intervalBoundaryPair.{u}).map a) :=
  rfl

private noncomputable def ibHExt :=
  ibHData.homotopyExtension ibBase ibSide ibH0

/-- The bottom face carries the base map at a concrete interior point. -/
example : ibHExt.extension (0, ibMid) = 0 :=
  ibHExt.extension_zero ibMid

/-- The side face carries the nonconstant homotopy: value 1 at time 1. -/
example : ibHExt.extension (1,
    (_root_.TopPair.intervalBoundaryPair.{u}).map ibZero) = 1 :=
  ibHExt.extension_subspace 1 ibZero

/-- The side face at an interior time distinguishes the homotopy from any
constant extension. -/
example : ibHExt.extension (⟨1 / 2, by norm_num⟩,
    (_root_.TopPair.intervalBoundaryPair.{u}).map ibZero) = 1 / 2 :=
  ibHExt.extension_subspace _ ibZero

end Behavioral

end MathlibExtTest.Topology.Category.TopPair.HurewiczCofibration

end
