/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.Basic
public import MathlibExt.AlgebraicTopology.LocalCoefficient.HomotopyFiberAcyclicity
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoops

/-!
# Local-coefficient comparison for an arbitrary plus map

The specified source point supplies an actual point of the original ending
fiber. Its canonical reduced acyclicity therefore gives isomorphisms of the
actual integral terminal maps. The existing one-fiber coefficient criterion
then proves the original pullback chain map is a quasi-isomorphism for every
integral target system, including nonflat stalks.

The target is path connected. This condition excludes the extra disjoint
target components permitted by the chosen-fiber predicate alone. A genuine
independently sized connected CW-type target supplies it internally.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap

universe u v

namespace TopCat.IsPlusConstructionAt

variable {X Y : TopCat.{u}} {f : X ⟶ Y}
  {x : X} {y : Y} {hxy : f x = y}
  {P : Subgroup (FundamentalGroup X x)} [P.Normal] [Group.IsPerfect P]

/-- The actual specified ending fiber of an arbitrary plus map has all its
integral terminal maps invertible. The constant loop supplies nonemptiness. -/
public theorem terminalHomology_isIso
    (h : TopCat.IsPlusConstructionAt f x y hxy P) (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map
      (terminal.from (TopCat.homotopyFiber f y))) := by
  let z := TopCat.loopToHomotopyFiber f x y hxy (Path.refl y)
  let : Nonempty (TopCat.homotopyFiber f y) := ⟨z⟩
  exact ((TopCat.isAcyclicSpace_iff_terminalHomology_isIso
    (TopCat.homotopyFiber f y)).mp h.acyclic) n

/-- Every integral target system is preserved by the SAME original plus map.
No cellular/cofibration hypothesis or stalk-flatness witness is needed. -/
public theorem localCoefficientHomologyEquivalence [PathConnectedSpace Y]
    (h : TopCat.IsPlusConstructionAt f x y hxy P) :
    TopCat.IsLocalCoefficientHomologyEquivalence f := by
  intro L n
  let m := TopCat.localCoefficientPullbackChainMap f L
  let : QuasiIso m :=
    TopCat.localCoefficientPullbackChainMap_quasiIso_of_homotopyFiber f y
      (fun k => h.terminalHomology_isIso k) L
  change IsIso (HomologicalComplex.homologyMap m n)
  exact (quasiIsoAt_iff_isIso_homologyMap m n).mp inferInstance

/-- Every point of the path-connected target has a canonically acyclic
original ending fiber; this is derived from the actual all-system comparison. -/
public theorem homotopyFiber_acyclic_all [PathConnectedSpace Y]
    (h : TopCat.IsPlusConstructionAt f x y hxy P) (z : Y) :
    TopCat.IsAcyclicMapAt f z := by
  exact TopCat.isAcyclicMapAt_of_localCoefficientHomologyEquivalence
    f h.localCoefficientHomologyEquivalence z

/-- A connected target with a genuine independently sized unbased CW model
satisfies the full original all-local-coefficient comparison. -/
public theorem localCoefficientHomologyEquivalence_of_CWType [ConnectedSpace Y]
    (h : TopCat.IsPlusConstructionAt f x y hxy P)
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y)) :
    TopCat.IsLocalCoefficientHomologyEquivalence f := by
  obtain ⟨C, hT, hC, ⟨e⟩⟩ := hCW
  let : T2Space C := hT
  let : Topology.CWComplex (Set.univ : Set C) := hC
  let : PathConnectedSpace Y :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType e
  exact h.localCoefficientHomologyEquivalence

end TopCat.IsPlusConstructionAt

end
