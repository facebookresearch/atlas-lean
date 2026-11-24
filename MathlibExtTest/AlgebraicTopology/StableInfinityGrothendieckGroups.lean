/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicTopology.StableInfinityGrothendieckGroups

/-!
# Relations of the degree-zero Grothendieck group of a stable ∞-category

The two ends of an equivalence edge have the same class. A pushout square with a zero
vertical corner gives `[horizontal] = [origin] + [final]`: the middle term of the cofibre
sequence `origin → horizontal → final` is the sum of the other two. Exact functors act on
classes by their object map.
-/

open CategoryTheory Opposite
open MathlibExt.AlgebraicTopology.StableInfinityCategoryModels
open MathlibExt.AlgebraicTopology.StableInfinityMappingSpaces
open MathlibExt.AlgebraicTopology.StableInfinityFiniteDiagrams
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicTopology.StableInfinityGrothendieckGroups
open scoped Simplicial

universe u

example (C : StableInfinityCategory.{u}) (e : C.toSSet _⦋1⦌)
    (he : IsEquivalenceEdge C.toSSet e) :
    objectClass C (C.toSSet.δ 1 e) = objectClass C (C.toSSet.δ 0 e) := by
  rw [objectClass, objectClass, QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure (Or.inl ⟨e, he, rfl⟩)

example (C : StableInfinityCategory.{u}) (d : indexNerve SquareCorner ⟶ C.toSSet)
    (hd : IsPushoutSquare d) (hz : IsZeroObject C.toSSet (cornerValue d .vertical)) :
    objectClass C (cornerValue d .horizontal) =
      objectClass C (cornerValue d .origin) + objectClass C (cornerValue d .final) := by
  rw [objectClass, objectClass, objectClass, ← QuotientAddGroup.mk_add,
    QuotientAddGroup.eq_iff_sub_mem, ← sub_sub]
  exact AddSubgroup.subset_closure (Or.inr ⟨d, hd, hz, rfl⟩)

example {C D : StableInfinityCategory.{u}} (f : ExactFunctor C D) (x : C.toSSet _⦋0⦌) :
    grothendieckMap f (objectClass C x) = objectClass D (f.map.app (op ⦋0⦌) x) := by
  simp [grothendieckMap, objectClass, objectCycleMap]
