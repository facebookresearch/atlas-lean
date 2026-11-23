/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalVertex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import MathlibExt.Topology.Category.PointedTopCat

/-!
# Geometric realization of the weak-stage diagonal, with distinguished point

For a Waldhausen category `C`, `stageWeakDiagonalReal C` is
`SSet.toTop.obj (stageWeakDiagonal C)` in `TopCat`. The zero-vertex inclusion
`stageWeakDiagonalZeroInclusion C : Δ[0] ⟶ stageWeakDiagonal C` via
`SSet.const` realizes as `stageWeakDiagonalReal.basepoint C` by applying the
realized map to the unique `default : |Δ[0]|`. The bundled pointed object
`stageWeakDiagonalReal.toPointed C : PointedTopCat` is
`Under.mk (stageWeakDiagonalReal.basepointMap C)`.

First realization layer only. It provides no induced maps, identity/composition
laws, paths, homotopies, connectedness, iterated realization, additivity,
π₀/K₀ identification, G-theory, spectra, or Q/S comparison; realized maps are
deferred to a subsequent module built from the existing `stageWeakDiagonalMap`
API.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategory C]

/-- Unpointed geometric realization of `stageWeakDiagonal C`. -/
noncomputable abbrev stageWeakDiagonalReal :=
  SSet.toTop.obj (stageWeakDiagonal C)

/-- Realized basepoint, from the zero-vertex inclusion. -/
noncomputable def stageWeakDiagonalReal.basepoint :
    stageWeakDiagonalReal C :=
  SSet.toTop.map (stageWeakDiagonalZeroInclusion C) default

/-- Constant map from the point into the realization, at the basepoint. -/
noncomputable def stageWeakDiagonalReal.basepointMap :
    TopCat.of PUnit ⟶ stageWeakDiagonalReal C :=
  TopCat.ofHom (ContinuousMap.const _ (stageWeakDiagonalReal.basepoint C))

/-- Bundled pointed realization, via `Under.mk`. -/
noncomputable def stageWeakDiagonalReal.toPointed :
    PointedTopCat.{max u v} :=
  Under.mk (stageWeakDiagonalReal.basepointMap C)

/-- Space computation: the pointed bundle unfolds to the realization. -/
@[simp]
theorem stageWeakDiagonalReal.toPointed_right :
    (stageWeakDiagonalReal.toPointed C).right = stageWeakDiagonalReal C :=
  rfl

/-- Point computation: the pointed bundle points at the realized basepoint. -/
@[simp]
theorem stageWeakDiagonalReal.toPointed_hom_apply :
    (stageWeakDiagonalReal.toPointed C).hom PUnit.unit =
      stageWeakDiagonalReal.basepoint C :=
  rfl

end CategoryTheory.Waldhausen.SConstruction
