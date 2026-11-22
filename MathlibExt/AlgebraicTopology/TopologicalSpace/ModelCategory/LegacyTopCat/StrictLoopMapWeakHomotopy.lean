/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopSpaceWeakEquivalence
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularLoopComparisonIso
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# Strict loop maps preserve weak homotopy equivalences

Strict postcomposition on loop spaces preserves weak homotopy equivalences.
The proof transports the simplicial loop-space theorem across the exact
singular-loop comparison square and uses left cancellation by the target
comparison isomorphism.

The source and target spaces live in one universe.  This file introduces no
weakly pointed, Quillen Q/S, spectrum, or stronger equivalence claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Simplicial
open scoped Simplicial Topology

universe u

namespace ContinuousMap

/-- Strict postcomposition on based loop spaces preserves weak homotopy
equivalences. -/
theorem strictLoopMap_mem_weakHomotopyEquivalences
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X)
    (hf : TopCat.weakHomotopyEquivalences (TopCat.ofHom f)) :
    TopCat.weakHomotopyEquivalences
      (TopCat.ofHom (strictLoopMap f x)) := by
  let _ : SSet.KanComplex
      (TopCat.toSSet.obj (TopCat.of X)) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex
      (TopCat.toSSet.obj (TopCat.of Y)) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex
      (TopCat.toSSet.obj (TopCat.of (LoopSpace X x))) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex
      (TopCat.toSSet.obj (TopCat.of (LoopSpace Y (f x)))) :=
    TopCat.toSSet_obj_kanComplex _
  rw [TopCat.mem_weakHomotopyEquivalences_iff] at hf ⊢
  have hLoop : SSet.KanComplex.W
      (SSet.loopSpaceMap
        (x := TopCat.toSSetObj₀Equiv.symm x)
        (y := TopCat.toSSetObj₀Equiv.symm (f x))
        (TopCat.toSSet.map (TopCat.ofHom f)) (by rfl)) :=
    hf.loopSpaceMap (h := by rfl)
  have hSource : SSet.KanComplex.W
      (SSet.singularLoopIso X x).hom :=
    SSet.KanComplex.W.ofIso (SSet.singularLoopIso X x)
  have hTarget : SSet.KanComplex.W
      (SSet.singularLoopIso Y (f x)).hom :=
    SSet.KanComplex.W.ofIso (SSet.singularLoopIso Y (f x))
  apply SSet.KanComplex.W.of_postcomp hTarget
  rw [SSet.singularLoopIso_hom_naturality]
  exact SSet.KanComplex.W.comp hSource hLoop

end ContinuousMap
