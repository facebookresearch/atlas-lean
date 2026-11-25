/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.TDA.ZeroDimensionalPersistence

@[expose] public section

open CategoryTheory MathlibExt.Topology.TDA

/-- At scale `1` the points `0` and `2` of the line are in the same cluster (chain `0, 1, 2`). -/
example : (Quot.mk _ 0 : (clusterFunctor (dist : ℝ → ℝ → ℝ)).obj 1) = Quot.mk _ 2 :=
  Quot.sound (Relation.EqvGen.trans _ 1 _ (Relation.EqvGen.rel _ _ (by norm_num [Real.dist_eq]))
    (Relation.EqvGen.rel _ _ (by norm_num [Real.dist_eq])))

/-- Adding a constant `η ≥ 0` to a dissimilarity moves its cluster functor by an
`η`-interleaving. -/
noncomputable example (d : Fin 3 → Fin 3 → ℝ) (η : ℝ) (hη : 0 ≤ η) :
    Interleaving (clusterFunctor d) (clusterFunctor fun a b => d a b + η) η :=
  clusterFunctorInterleaving hη fun a b => by simp [abs_of_nonneg hη]
