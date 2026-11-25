/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.FiniteCompact
public import MathlibExt.Topology.Category.CompactlyGenerated.GeneratedBy
public import MathlibExt.Topology.Compactness.WeakHausdorffSpace

import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Topology.Instances.Shrink

/-!
# Finite simplicial realizations in compactly generated spaces

A finite simplicial set has a small compact Hausdorff realization. Shrinking
the carrier only inside the proof supplies a compact Hausdorff probe in an
independent universe, so the original realization topology is compactly
generated. The public bundled object retains the literal realization carrier
and topology.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology

universe u v

namespace SSet

private theorem realization_small_of_finite
    (K : SSet.{v}) [K.Finite] :
    Small.{u} (SSet.toTop.obj K) := by
  let _ : Small.{u} K.N := small_map (Finite.equivFin K.N)
  let _ : ∀ s : K.N,
      Small.{u} (Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :=
    fun _ => inferInstance
  let _ : Small.{u}
      (Σ s : K.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :=
    inferInstance
  exact small_of_surjective (SSet.surjective_sigmaToTop K)

private theorem uCompactlyGeneratedSpace_of_small_compact_t2
    (X : Type v) [TopologicalSpace X] [Small.{u} X]
    [CompactSpace X] [T2Space X] :
    UCompactlyGeneratedSpace.{u} X := by
  let e : X ≃ₜ Shrink.{u} X := Shrink.homeomorph X
  let _ : CompactSpace (Shrink.{u} X) := e.compactSpace
  let _ : T2Space (Shrink.{u} X) := e.t2Space
  let S : CompHaus.{u} := CompHaus.of (Shrink.{u} X)
  have hShrink :
      IsGeneratedBy CompactlyGenerated.compactHausProbes.{u}
        (Shrink.{u} X) := by
    change IsGeneratedBy CompactlyGenerated.compactHausProbes.{u}
      (CompactlyGenerated.compactHausProbes S)
    infer_instance
  let _ : IsGeneratedBy CompactlyGenerated.compactHausProbes.{u}
      (Shrink.{u} X) := hShrink
  apply Topology.isGeneratedBy_compactHausProbes_iff.mp
  exact e.symm.isQuotientMap.isGeneratedBy

/-- The realization of a finite simplicial set is compactly generated for
an independent compact-probe universe. -/
theorem uCompactlyGeneratedSpace_realization_of_finite
    (K : SSet.{v}) [K.Finite] :
    UCompactlyGeneratedSpace.{u} (SSet.toTop.obj K) := by
  let _ : Small.{u} (SSet.toTop.obj K) :=
    realization_small_of_finite K
  exact uCompactlyGeneratedSpace_of_small_compact_t2 (SSet.toTop.obj K)

/-- The realization of a finite simplicial set is weak Hausdorff for an
independent compact-probe universe. -/
theorem uWeakHausdorffSpace_realization_of_finite
    (K : SSet.{v}) [K.Finite] :
    UWeakHausdorffSpace.{u} (SSet.toTop.obj K) :=
  uWeakHausdorffSpaceOfT2 (SSet.toTop.obj K)

/-- A finite simplicial realization as a compactly generated space, with
the literal realization carrier and topology. -/
noncomputable def toCompactlyGeneratedOfFinite
    (K : SSet.{v}) [K.Finite] : CompactlyGenerated.{u, v} where
  toTop := SSet.toTop.obj K
  is_compactly_generated :=
    uCompactlyGeneratedSpace_realization_of_finite K

end SSet
