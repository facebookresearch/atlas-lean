/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import
MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
public import
MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWHomotopy
public import
Mathlib.Topology.Homotopy.TopCat.ToSSet
public import
Mathlib.Topology.Homotopy.Equiv

/-!
# Topological homotopy equivalences are weak homotopy equivalences

For `X Y : Type u` and `e : ContinuousMap.HomotopyEquiv X Y`, the forward map
`TopCat.ofHom e.toFun` and the inverse map `TopCat.ofHom e.invFun` both lie in
`TopCat.weakHomotopyEquivalences`. Each leg transports its
`ContinuousMap.Homotopic` side across `TopCat.Homotopy.toSSet` and closes by
`SSet.KanComplex.W.of_homotopy` using explicit local singular-Kan witnesses.
No horn construction, no coproduct or pushout closure, no factorization system,
and no model structure.
-/

@[expose] public section

open CategoryTheory

namespace TopCat

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Forward leg of a topological homotopy equivalence is a weak homotopy
equivalence. -/
theorem homotopyEquiv_toFun_mem (e : ContinuousMap.HomotopyEquiv X Y) :
    weakHomotopyEquivalences.{u} (TopCat.ofHom e.toFun) := by
  rw [TopCat.mem_weakHomotopyEquivalences_iff]
  have hFG :
      TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 _) := by
    exact e.left_inv.some
  have hGF :
      TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 _) := by
    exact e.right_inv.some
  have hX :
      SSet.Homotopy
        (TopCat.toSSet.map (TopCat.ofHom e.toFun) ≫
          TopCat.toSSet.map (TopCat.ofHom e.invFun)) (𝟙 _) := by
    simpa using hFG.toSSet
  have hY :
      SSet.Homotopy
        (TopCat.toSSet.map (TopCat.ofHom e.invFun) ≫
          TopCat.toSSet.map (TopCat.ofHom e.toFun)) (𝟙 _) := by
    simpa using hGF.toSSet
  let _ : SSet.KanComplex (TopCat.toSSet.obj (TopCat.of X)) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex (TopCat.toSSet.obj (TopCat.of Y)) :=
    TopCat.toSSet_obj_kanComplex _
  exact SSet.KanComplex.W.of_homotopy _ _ hX hY

/-- Inverse leg of a topological homotopy equivalence is a weak homotopy
equivalence. -/
theorem homotopyEquiv_invFun_mem (e : ContinuousMap.HomotopyEquiv X Y) :
    weakHomotopyEquivalences.{u} (TopCat.ofHom e.invFun) :=
  homotopyEquiv_toFun_mem e.symm

/-- A morphism equal to the forward leg is a weak homotopy equivalence. -/
theorem mem_of_eq_toFun {f : TopCat.of X ⟶ TopCat.of Y}
    (e : ContinuousMap.HomotopyEquiv X Y) (hf : f = TopCat.ofHom e.toFun) :
    weakHomotopyEquivalences.{u} f :=
  hf ▸ homotopyEquiv_toFun_mem e

/-- A morphism equal to the inverse leg is a weak homotopy equivalence. -/
theorem mem_of_eq_invFun {f : TopCat.of Y ⟶ TopCat.of X}
    (e : ContinuousMap.HomotopyEquiv X Y) (hf : f = TopCat.ofHom e.invFun) :
    weakHomotopyEquivalences.{u} f :=
  hf ▸ homotopyEquiv_invFun_mem e

end TopCat
