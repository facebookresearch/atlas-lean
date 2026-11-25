/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Realized nullhomotopies from simplicial homotopies

A realized constant simplicial map is the constant continuous map at the
corresponding realized vertex. Consequently, two simplicial homotopies with a
common source, one ending at a map and one at a constant map, make the
realization of the first endpoint nullhomotopic.

This file introduces no weak-equivalence hypothesis, chosen inverse,
last-vertex cancellation, contractible-space instance, Approximation theorem,
or K-theory consequence.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

/-- Realizing a constant simplicial map gives the constant continuous map
at the realized vertex. -/
theorem toTop_map_const_hom {A Y : SSet.{u}} (y : Y _⦋0⦌) :
    (SSet.toTop.map (SSet.const (X := A) y)).hom =
      ContinuousMap.const _ (SSet.realizedVertex y) := by
  ext z
  rw [SSet.realizedVertex_eq_const]
  let p : A ⟶ (Δ[0] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.from A
  rw [← SSet.comp_const p y, Functor.map_comp]
  change SSet.toTop.map (SSet.const y) (SSet.toTop.map p z) =
    SSet.toTop.map (SSet.const y) default
  rw [Subsingleton.elim (SSet.toTop.map p z) default]

/-- Two simplicial homotopies with a common source, one ending at a map and
one at a constant map, make the realization of the first endpoint
nullhomotopic. -/
theorem toTop_map_nullhomotopic_of_common_source
    {A Y : SSet.{u}} {r f : A ⟶ Y} (y : Y _⦋0⦌)
    (hrf : SSet.Homotopy r f)
    (hrconst : SSet.Homotopy r (SSet.const y)) :
    ContinuousMap.Nullhomotopic (SSet.toTop.map f).hom := by
  let Hrf := SSet.realizeHomotopy A Y r f hrf
  let Hrc := SSet.realizeHomotopy A Y r (SSet.const y) hrconst
  have Hrc' : ContinuousMap.Homotopy
      (SSet.toTop.map r).hom
      (ContinuousMap.const _ (SSet.realizedVertex y)) :=
    ContinuousMap.Homotopy.cast Hrc rfl (SSet.toTop_map_const_hom y)
  exact ⟨SSet.realizedVertex y, ⟨Hrf.symm.trans Hrc'⟩⟩

end SSet
