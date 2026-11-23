/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationHausdorff

open Topology Set

universe u v

#check SSet.realization_t2Space
#print axioms SSet.realization_t2Space

-- The actual public theorem separates arbitrary original realization points.
example (K : SSet.{u}) (x y : SSet.toTop.obj K) (hxy : x ≠ y) :
    ∃ U V : Set (SSet.toTop.obj K),
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V := by
  let : T2Space (SSet.toTop.obj K) := SSet.realization_t2Space K
  exact t2_separation hxy

-- Compact subsets are closed without a finite-simplicial-set premise.
example (K : SSet.{u}) (A : Set (SSet.toTop.obj K)) (hA : IsCompact A) :
    IsClosed A := by
  let : T2Space (SSet.toTop.obj K) := SSet.realization_t2Space K
  exact hA.isClosed

-- The domain may have its own universe; the actual compact image is closed.
example (K : SSet.{u}) {X : Type v} [TopologicalSpace X] [CompactSpace X]
    (f : C(X, SSet.toTop.obj K)) : IsClosed (Set.range f) := by
  let : T2Space (SSet.toTop.obj K) := SSet.realization_t2Space K
  exact (isCompact_range f.continuous).isClosed
