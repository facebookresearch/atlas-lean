/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.NDREndpointCylinder

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory MonoidalCategory Topology

universe u

namespace MathlibExtTest.Topology.Category.TopPair.NDREndpointCylinder

variable (P : _root_.TopPair.{u}) (d : _root_.TopPair.NDRData P)

example : (_root_.TopPair.endpointCylinderBoundaryPair P).fst =
    _root_.TopCat.I.{u} ⊗ P.fst :=
  rfl

example : Set.range (_root_.TopPair.endpointCylinderBoundaryPair P).map =
    (Set.range (_root_.TopPair.intervalBoundaryPair.{u}).map).unionProd
      (Set.range P.map) :=
  _root_.TopPair.range_endpointCylinderBoundaryPair_map P

example (z : (_root_.TopPair.endpointCylinderBoundaryPair P).fst) :
    z ∈ Set.range (_root_.TopPair.endpointCylinderBoundaryPair P).map ↔
      ((z.1 : _root_.TopCat.I.{u}) = (0 : _root_.TopCat.I.{u}) ∨
        (z.1 : _root_.TopCat.I.{u}) = (1 : _root_.TopCat.I.{u})) ∨
        (z.2 : P.fst) ∈ Set.range P.map :=
  _root_.TopPair.mem_range_endpointCylinderBoundaryPair_map_iff P z

example (x : P.fst) :
    ((0 : _root_.TopCat.I.{u}), x) ∈
      Set.range (_root_.TopPair.endpointCylinderBoundaryPair P).map :=
  (_root_.TopPair.mem_range_endpointCylinderBoundaryPair_map_iff P _).2
    (Or.inl (Or.inl rfl))

example (x : P.fst) :
    ((1 : _root_.TopCat.I.{u}), x) ∈
      Set.range (_root_.TopPair.endpointCylinderBoundaryPair P).map :=
  (_root_.TopPair.mem_range_endpointCylinderBoundaryPair_map_iff P _).2
    (Or.inl (Or.inr rfl))

example (t : _root_.TopCat.I.{u}) (a : P.snd) :
    (t, P.map a) ∈
      Set.range (_root_.TopPair.endpointCylinderBoundaryPair P).map :=
  (_root_.TopPair.mem_range_endpointCylinderBoundaryPair_map_iff P _).2
    (Or.inr ⟨a, rfl⟩)

example : _root_.TopPair.NDRData
    (_root_.TopPair.endpointCylinderBoundaryPair P) :=
  d.endpointCylinderBoundaryData

example (z : (_root_.TopPair.endpointCylinderBoundaryPair P).fst) :
    d.endpointCylinderBoundaryData.control z =
      (_root_.TopPair.intervalBoundaryNDRData.{u}).control z.1 *
        d.control z.2 :=
  d.endpointCylinderBoundaryData_control_apply z

example : _root_.TopCat.IsHurewiczCofibration
    (_root_.TopPair.endpointCylinderBoundaryPair P).map :=
  d.endpointRelativeHurewicz

end MathlibExtTest.Topology.Category.TopPair.NDREndpointCylinder

end
