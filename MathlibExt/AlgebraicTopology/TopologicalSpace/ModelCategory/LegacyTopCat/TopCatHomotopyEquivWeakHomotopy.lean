/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
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
# Weak homotopy equivalences from topological homotopy equivalences

Both the forward map and the inverse map of a topological homotopy equivalence
are weak homotopy equivalences. The same conclusions apply to topological morphisms
identified with either of those continuous maps.
-/

@[expose] public section

open CategoryTheory

namespace TopCat

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/--
The forward map of a topological homotopy equivalence is a weak homotopy
equivalence.
-/
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

/--
The chosen inverse map of a topological homotopy equivalence is a weak homotopy
equivalence.
-/
theorem homotopyEquiv_invFun_mem (e : ContinuousMap.HomotopyEquiv X Y) :
    weakHomotopyEquivalences.{u} (TopCat.ofHom e.invFun) :=
  homotopyEquiv_toFun_mem e.symm

/--
A topological morphism equal to the forward map of a homotopy equivalence is
a weak homotopy equivalence.
-/
theorem mem_of_eq_toFun {f : TopCat.of X ⟶ TopCat.of Y}
    (e : ContinuousMap.HomotopyEquiv X Y) (hf : f = TopCat.ofHom e.toFun) :
    weakHomotopyEquivalences.{u} f :=
  hf ▸ homotopyEquiv_toFun_mem e

/--
A topological morphism equal to the inverse map of a homotopy equivalence is
a weak homotopy equivalence.
-/
theorem mem_of_eq_invFun {f : TopCat.of Y ⟶ TopCat.of X}
    (e : ContinuousMap.HomotopyEquiv X Y) (hf : f = TopCat.ofHom e.invFun) :
    weakHomotopyEquivalences.{u} f :=
  hf ▸ homotopyEquiv_invFun_mem e

end TopCat
