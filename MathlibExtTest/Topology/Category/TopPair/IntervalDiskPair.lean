/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.IntervalDiskPair

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory MonoidalCategory Topology

universe u

namespace MathlibExtTest.Topology.Category.TopPair.IntervalDiskPair

open _root_.Topology.CWComplex

example (n : ℕ) : (intervalDiskPair.{u} n).fst =
    _root_.TopCat.I.{u} ⊗ (classicalCellDiskPair.{u} n).fst :=
  intervalDiskPair_fst n

example (n : ℕ) :
    Set.range (intervalDiskPair.{u} n).map =
      (Set.range (_root_.TopPair.intervalBoundaryPair.{u}).map).unionProd
        (Set.range (classicalCellDiskPair.{u} n).map) :=
  range_intervalDiskPair_map n

example (n : ℕ) (x : (classicalCellDiskPair.{u} n).fst) :
    ((0 : _root_.TopCat.I.{u}), x) ∈ Set.range (intervalDiskPair.{u} n).map :=
  (mem_range_intervalDiskPair_map_iff n _).2 (Or.inl (Or.inl rfl))

example (n : ℕ) (x : (classicalCellDiskPair.{u} n).fst) :
    ((1 : _root_.TopCat.I.{u}), x) ∈ Set.range (intervalDiskPair.{u} n).map :=
  (mem_range_intervalDiskPair_map_iff n _).2 (Or.inl (Or.inr rfl))

example (n : ℕ) : _root_.TopPair.NDRData (intervalDiskPair.{u} n) :=
  intervalDiskPairNDRData.{u} n

example (n : ℕ) : _root_.TopPair.GoodPairData (intervalDiskPair.{u} n) :=
  intervalDiskPairGoodPairData.{u} n

example (n : ℕ) : _root_.TopCat.IsHurewiczCofibration
    (intervalDiskPair.{u} n).map :=
  intervalDiskPair_isHurewiczCofibration.{u} n

end MathlibExtTest.Topology.Category.TopPair.IntervalDiskPair

end
